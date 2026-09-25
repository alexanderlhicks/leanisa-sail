use lean_vm::cpu::{DerefMode, Op, Program, bytecode_columns};
use primitives::field::{F64, F192};
use serde_json::{Value, json};
use std::collections::HashMap;
use std::io::{self, BufRead};
use std::panic::{AssertUnwindSafe, catch_unwind};

type Result<T> = std::result::Result<T, String>;

fn array<'a>(v: &'a Value, size: usize, label: &str) -> Result<&'a [Value]> {
    let values = v
        .as_array()
        .ok_or_else(|| format!("{label} must be an array"))?;
    if values.len() != size {
        return Err(format!("{label} must contain {size} entries"));
    }
    Ok(values)
}

fn hex(v: &Value) -> Result<u64> {
    let text = v.as_str().ok_or("limb must be a hexadecimal string")?;
    if text.is_empty() || text.len() > 16 || !text.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err("limb must be unsigned 64-bit hexadecimal".into());
    }
    u64::from_str_radix(text, 16).map_err(|e| e.to_string())
}

fn word(v: &Value) -> Result<F192> {
    let v = array(v, 3, "word")?;
    Ok(F192::new(hex(&v[0])?, hex(&v[1])?, hex(&v[2])?))
}

fn output_word(v: F192) -> Value {
    json!([
        format!("{:016x}", v.c0),
        format!("{:016x}", v.c1),
        format!("{:016x}", v.c2)
    ])
}

fn op(v: &Value) -> Result<Op> {
    let name = v[0].as_str().ok_or("missing opcode")?;
    let size = match name {
        "xor" | "mul" | "jump" => 4,
        "set" => 3,
        "deref" => 5,
        "blake" => 8,
        _ => return Err(format!("unknown opcode: {name}")),
    };
    let v = array(v, size, "instruction")?;
    let n = |i: usize| -> Result<u32> {
        let value = v[i].as_u64().ok_or("offset must be an unsigned integer")?;
        u32::try_from(value).map_err(|_| "offset must fit in u32".into())
    };
    Ok(match name {
        "xor" => Op::Xor {
            a: n(1)?,
            b: n(2)?,
            c: n(3)?,
        },
        "mul" => Op::Mul {
            a: n(1)?,
            b: n(2)?,
            c: n(3)?,
        },
        "set" => Op::Set {
            o: n(1)?,
            k: word(&v[2])?,
        },
        "deref" => Op::Deref {
            o1: n(1)?,
            o2: n(2)?,
            o3: n(3)?,
            mode: match v[4].as_str() {
                Some("Cell") => DerefMode::Cell,
                Some("Pc") => DerefMode::Pc,
                Some("Fp") => DerefMode::Fp,
                _ => return Err("invalid DEREF mode".into()),
            },
        },
        "jump" => Op::Jump {
            oc: n(1)?,
            od: n(2)?,
            of: n(3)?,
        },
        "blake" => Op::Blake2s {
            ins: [n(1)?, n(2)?, n(3)?, n(4)?],
            cv: n(5)?,
            out: n(6)?,
            md: n(7)?,
        },
        _ => unreachable!(),
    })
}

fn request(v: Value) -> Result<Value> {
    match v["kind"].as_str() {
        Some("field") => {
            let a = word(&v["a"])?;
            let b = word(&v["b"])?;
            Ok(
                json!({"base": format!("{:016x}", (F64(a.c0) * F64(b.c0)).0), "extension": output_word(a * b)}),
            )
        }
        Some("blake") => {
            let message = array(&v["message"], 8, "message")?
                .iter()
                .map(hex)
                .collect::<Result<Vec<_>>>()?;
            let cv = array(&v["cv"], 4, "cv")?
                .iter()
                .map(hex)
                .collect::<Result<Vec<_>>>()?;
            let md = word(&v["md"])?;
            if md.c2 != 0 {
                return Err("BLAKE metadata must fit in 128 bits".into());
            }
            let a = std::array::from_fn(|i| F64(message[i]));
            let b = std::array::from_fn(|i| F64(message[i + 4]));
            let cv = std::array::from_fn(|i| F64(cv[i]));
            let block = lean_vm::hash_flock::compression(a, b, cv, md);
            Ok(json!(
                lean_vm::hash_flock::digest(&block).map(|x| format!("{:016x}", x.0))
            ))
        }
        Some("execute") => {
            let program = v["program"].as_array().ok_or("program must be an array")?;
            if !program.len().is_power_of_two() || program.len() as u64 > (1u64 << 32) {
                return Err("program length must be a power of two in 1..2^32".into());
            }
            let ops = program.iter().map(op).collect::<Result<Vec<_>>>()?;
            let input = array(&v["input"], 2, "input")?;
            let input = [word(&input[0])?, word(&input[1])?];
            if input.iter().any(|w| w.c2 != 0) {
                return Err("public input words must fit in 128 bits".into());
            }
            let columns = bytecode_columns(&ops);
            let encoding: Vec<Vec<_>> = (0..ops.len())
                .map(|i| columns.iter().map(|c| format!("{:016x}", c[i].0)).collect())
                .collect();
            let program = Program::assemble(ops, HashMap::new(), 64);
            // The pinned upstream API has no fuel parameter. The Python harness
            // runs each request in its own process with a wall-clock timeout.
            let exec = program.execute(input);
            let cells: Vec<_> = exec
                .mem
                .iter()
                .enumerate()
                .filter(|(_, w)| **w != F192::ZERO)
                .map(|(i, w)| json!([i, output_word(*w)]))
                .collect();
            Ok(
                json!({"memory_size": exec.mem.len(), "cells": cells, "cycles": exec.cycles,
                    "encoding": encoding, "unconstrained_reads": exec.unconstrained_reads}),
            )
        }
        _ => Err("unknown request kind".into()),
    }
}

fn main() {
    // Panics from the upstream executor are reported separately from input
    // rejection. Neither is treated as a verdict of the Sail model.
    std::panic::set_hook(Box::new(|_| {}));
    for line in io::stdin().lock().lines() {
        let reply = catch_unwind(AssertUnwindSafe(|| -> Result<Value> {
            let line = line.map_err(|e| e.to_string())?;
            let input = serde_json::from_str(&line).map_err(|e| e.to_string())?;
            request(input)
        }));
        let output = match reply {
            Ok(Ok(answer)) => json!({"status": "ok", "answer": answer}),
            Ok(Err(error)) => json!({"status": "rejected", "error": error}),
            Err(payload) => {
                let error = payload
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| payload.downcast_ref::<&str>().copied())
                    .unwrap_or("non-string upstream panic");
                json!({"status": "panic", "error": error})
            }
        };
        println!("{output}");
    }
}
