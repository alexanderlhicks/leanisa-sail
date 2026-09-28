#!/usr/bin/env python3
"""Compare actual Sail, Rust leanVM, and Lean leanerVM on a shared corpus."""

import argparse
from copy import deepcopy
import hashlib
import importlib
import json
import math
import os
from pathlib import Path
import random
import re
import resource
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 64) - 1
MAX_PROGRAM = 64
MAX_MEMORY = 131072
MAX_FUEL = 1024
VERDICTS = ("Running", "Halted", "BadAccess", "BadValue", "BadInstance", "OutOfFuel")
HEX = re.compile(r"[0-9a-f]{16}\Z")
FAILURE_CONTEXT = {}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def word(value):
    return [f"{(value >> (64 * i)) & MASK:016x}" for i in range(3)]


def integer(limbs):
    return sum(int(value, 16) << (64 * i) for i, value in enumerate(limbs))


def uint(value, maximum, label):
    require(type(value) is int and 0 <= value <= maximum, f"invalid {label}")


def words(value, count, label):
    require(isinstance(value, list) and len(value) == count
            and all(isinstance(x, str) and HEX.fullmatch(x) for x in value),
            f"{label} needs {count} canonical hexadecimal u64 limbs")


def validate_request(req):
    """Enforce the bounded common input domain before any target is invoked."""
    require(isinstance(req, dict), "request must be an object")
    kind = req.get("kind")
    if kind in ("field", "add"):
        require(set(req) == {"kind", "a", "b"}, "unexpected field keys")
        words(req.get("a"), 3, "a")
        words(req.get("b"), 3, "b")
    elif kind == "blake":
        require(set(req) == {"kind", "message", "cv", "md"}, "unexpected BLAKE keys")
        words(req.get("message"), 8, "message")
        words(req.get("cv"), 4, "cv")
        words(req.get("md"), 3, "metadata")
        require(int(req["md"][2], 16) == 0, "metadata exceeds 128 bits")
    elif kind in ("codec", "execute", "image"):
        allowed = {"codec": {"kind", "program"},
                   "execute": {"kind", "program", "input"},
                   "image": {"kind", "program", "input", "memory_size", "cells", "fuel"}}
        require(set(req) == allowed[kind], f"unexpected {kind} keys")
        program = req.get("program")
        require(isinstance(program, list) and 1 <= len(program) <= MAX_PROGRAM,
                "program length outside 1..64")
        require(len(program) & (len(program) - 1) == 0, "program length must be a power of two")
        arities = {"xor": 4, "mul": 4, "set": 3, "deref": 5, "jump": 4, "blake": 8}
        for op in program:
            require(isinstance(op, list) and op and isinstance(op[0], str)
                    and op[0] in arities and len(op) == arities[op[0]], "invalid instruction")
            offsets = op[1:2] if op[0] == "set" else op[1:4] if op[0] == "deref" else op[1:]
            for offset in offsets:
                uint(offset, 65535, "offset")
            if op[0] == "set":
                words(op[2], 3, "SET value")
            if op[0] == "deref":
                require(op[4] in ("Cell", "Pc", "Fp"), "invalid DEREF mode")
        if kind != "codec":
            inputs = req.get("input")
            require(isinstance(inputs, list) and len(inputs) == 2, "need two public input words")
            for value in inputs:
                words(value, 3, "public input")
                require(int(value[2], 16) == 0, "public input exceeds 128 bits")
        if kind == "image":
            uint(req.get("memory_size"), MAX_MEMORY, "memory size")
            require(req["memory_size"] >= 65536 and req["memory_size"] & (req["memory_size"] - 1) == 0,
                    "shared image memory length must be 65536 or 131072")
            uint(req.get("fuel"), MAX_FUEL, "fuel")
            cells = req.get("cells")
            require(isinstance(cells, list) and len(cells) <= req["memory_size"], "invalid sparse image")
            seen = set()
            for cell in cells:
                require(isinstance(cell, list) and len(cell) == 2, "invalid cell")
                uint(cell[0], req["memory_size"] - 1, "cell index")
                require(cell[0] not in seen, "duplicate cell index")
                seen.add(cell[0])
                words(cell[1], 3, "cell")
    else:
        raise RuntimeError(f"unknown request kind: {kind!r}")


def process(command, *, data="", cwd=None, env=None, timeout=60, output_limit=16 << 20):
    """Bound the complete process group, elapsed time, and retained output."""
    child = None
    try:
        with tempfile.TemporaryFile() as stdin, tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            stdin.write(data.encode())
            stdin.seek(0)
            try:
                child = subprocess.Popen([str(x) for x in command], stdin=stdin,
                                         stdout=stdout, stderr=stderr, cwd=cwd, env=env,
                                         start_new_session=True,
                                         preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_AS, (8 << 30, 8 << 30)))
            except OSError as error:
                return {"status": "launch_error", "error": str(error)}
            deadline = time.monotonic() + timeout
            while child.poll() is None:
                if os.fstat(stdout.fileno()).st_size > output_limit or os.fstat(stderr.fileno()).st_size > output_limit:
                    return {"status": "output_limit"}
                if time.monotonic() >= deadline:
                    return {"status": "timeout", "timeout_seconds": timeout}
                time.sleep(0.02)
            if os.fstat(stdout.fileno()).st_size > output_limit or os.fstat(stderr.fileno()).st_size > output_limit:
                return {"status": "output_limit", "returncode": child.returncode}
            stdout.seek(0)
            stderr.seek(0)
            out, err = stdout.read().decode(errors="replace"), stderr.read().decode(errors="replace")
            if child.returncode:
                return {"status": "crash", "returncode": child.returncode, "stderr": err[-4096:]}
            return {"status": "ok", "stdout": out, "stderr": err[-4096:]}
    finally:
        if child is not None:
            # A successful leader may have left descendants holding open files
            # or consuming resources. Clean up the group on every exit path.
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()


def checked_command(command, **kwargs):
    result = process(command, **kwargs)
    require(result["status"] == "ok", f"command failed: {command[0]}: {result}")
    return result["stdout"]


def revision(path):
    clean = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    return checked_command(["git", "--no-replace-objects", "-C", path, "rev-parse", "HEAD"], env=clean).strip()


def unique_json(text):
    def pairs(items):
        obj = {}
        for key, value in items:
            require(key not in obj, f"duplicate JSON key: {key}")
            obj[key] = value
        return obj
    return json.loads(text, object_pairs_hook=pairs)


def adapter_batch(descriptor, requests, timeout):
    for req in requests:
        validate_request(req)
    result = process(descriptor["command"], data="".join(json.dumps(req) + "\n" for req in requests),
                     cwd=descriptor.get("cwd"), env=descriptor.get("env"), timeout=timeout)
    if result["status"] != "ok":
        return [result] * len(requests)
    try:
        lines = result["stdout"].splitlines()
        require(len(lines) == len(requests), "adapter response count differs from request count")
        replies = [unique_json(line) for line in lines]
        for reply in replies:
            require(isinstance(reply, dict) and reply.get("status") in ("ok", "rejected", "panic"),
                    "invalid adapter response envelope")
            require(reply["status"] != "ok" or "answer" in reply, "missing adapter answer")
        return replies
    except (ValueError, RuntimeError) as error:
        return [{"status": "protocol_error", "error": str(error)}] * len(requests)


def sail_bits(value, width):
    return f"0x{value:0{width // 4}x}"


def sail_instruction(op):
    # Address conversion itself is performed by the Sail specification.
    address = lambda n: f"gpow({sail_bits(n, 64)})"
    if op[0] == "set":
        return f"Set({address(op[1])}, {sail_bits(integer(op[2]), 192)})"
    if op[0] == "deref":
        return f"Deref({', '.join(address(n) for n in op[1:4])}, {op[4]})"
    name = {"xor": "Xor", "mul": "Mul", "jump": "Jump", "blake": "Blake2s"}[op[0]]
    return f"{name}({', '.join(address(n) for n in op[1:])})"


def sail_source(requests):
    functions, calls = [], []
    for index, req in enumerate(requests):
        validate_request(req)
        lines = [f"function differential_case_{index}() -> unit = {{",
                 f'  print_endline("CASE {index}");']
        kind = req["kind"]
        if kind in ("field", "add"):
            a, b = integer(req["a"]), integer(req["b"])
            base = f"kmul({sail_bits(a & MASK, 64)}, {sail_bits(b & MASK, 64)})"
            ext = f"emul({sail_bits(a, 192)}, {sail_bits(b, 192)})"
            if kind == "add":
                base = f"({sail_bits(a & MASK, 64)} ^^ {sail_bits(b & MASK, 64)})"
                ext = f"({sail_bits(a, 192)} ^^ {sail_bits(b, 192)})"
            lines += [f"  differential_number(unsigned({base}));", f"  differential_number(unsigned({ext}));"]
        elif kind == "blake":
            lines += [f"  differential_number(unsigned(blake_compress({sail_bits(integer(req['message']), 512)}, "
                      f"{sail_bits(integer(req['cv']), 256)}, {sail_bits(integer(req['md']), 128)})));"]
        elif kind == "codec":
            for i, op in enumerate(req["program"]):
                lines.append(f"  let row_{i} = encode({sail_instruction(op)});")
                lines.extend(f"  differential_number(unsigned(row_{i}[{j}]));" for j in range(8))
                lines.append(f"  differential_number(if decode(row_{i}) == Some({sail_instruction(op)}) then 1 else 0);")
        elif kind == "image":
            p, m = len(req["program"]), req["memory_size"]
            lines += [f"  var program : vector({p}, instruction) = vector_init({p}, Xor(gpow(0x0000000000000000), gpow(0x0000000000000000), gpow(0x0000000000000000)));",
                      f"  var mem : vector({m}, eword) = vector_init({m}, sail_zeros(192));"]
            lines.extend(f"  program[{i}] = {sail_instruction(op)};" for i, op in enumerate(req["program"]))
            lines.extend(f"  mem[{i}] = {sail_bits(integer(value), 192)};" for i, value in req["cells"])
            pi = integer(req["input"][0]) | (integer(req["input"][1]) << 128)
            lines += [f"  let result = run_indexed(program, mem, {sail_bits(pi, 256)}, {req['fuel']});",
                      "  differential_number(differential_verdict(result.verdict));",
                      "  differential_number(unsigned(result.state.pc));",
                      "  differential_number(unsigned(result.state.fp));"]
        else:
            raise RuntimeError("Sail adapter does not generate Rust images")
        lines += ["  ()", "}"]
        functions.append("\n".join(lines))
        calls.append(f"  differential_case_{index}();")
    groups = []
    for offset in range(0, len(calls), 16):
        name = f"differential_group_{offset // 16}"
        functions.append(f"function {name}() -> unit = {{\n" + "\n".join(calls[offset:offset + 16]) + "\n  ()\n}")
        groups.append(f"  {name}();")
    functions.append("function main() -> unit = {\n" + "\n".join(groups) + '\n  print_endline("END")\n}\n')
    return "\n\n".join(functions)


def parse_sail(requests, output):
    lines = iter(output.splitlines())
    replies = []
    def number():
        value = next(lines)
        require(re.fullmatch(r"0|[1-9][0-9]*", value) is not None, "invalid Sail number")
        return int(value)
    try:
        for index, req in enumerate(requests):
            require(next(lines) == f"CASE {index}", "Sail response ordering differs")
            kind = req["kind"]
            if kind in ("field", "add"):
                base, extension = number(), number()
                uint(base, MASK, "Sail base result")
                uint(extension, (1 << 192) - 1, "Sail extension result")
                answer = {"base": f"{base:016x}", "extension": word(extension)}
            elif kind == "blake":
                digest = number()
                uint(digest, (1 << 256) - 1, "Sail BLAKE result")
                answer = [f"{(digest >> (64 * i)) & MASK:016x}" for i in range(4)]
            elif kind == "codec":
                rows = []
                for _ in req["program"]:
                    row = [number() for _ in range(8)]
                    require(all(x <= MASK for x in row), "Sail codec result exceeds u64")
                    require(number() == 1, "Sail codec roundtrip failed")
                    rows.append([f"{x:016x}" for x in row])
                answer = {"encoding": rows}
            else:
                verdict = number()
                require(verdict < len(VERDICTS), "invalid Sail verdict")
                pc, fp = number(), number()
                uint(pc, MASK, "Sail PC")
                uint(fp, MASK, "Sail FP")
                answer = {"verdict": VERDICTS[verdict], "pc": f"{pc:016x}", "fp": f"{fp:016x}"}
            replies.append({"status": "ok", "answer": answer})
        require(next(lines) == "END", "Sail output has no final marker")
        require(list(lines) == [], "Sail output has trailing lines")
        return replies
    except (StopIteration, ValueError, RuntimeError) as error:
        return [{"status": "protocol_error", "error": str(error)}] * len(requests)


class Sail:
    def __init__(self, sail_root, build, timeout):
        self.root, self.build, self.timeout = sail_root, build, timeout
        self.env = dict(os.environ)
        self.env["PATH"] = str(sail_root / "_deps/z3/bin") + os.pathsep + self.env["PATH"]
        self.build.mkdir(parents=True, exist_ok=True)
        self.artifacts = {}
        pins = unique_json((ROOT / "tests/differential/targets.json").read_text())
        self.source_hashes = importlib.import_module("differential_rust")._verify_tree(
            sail_root, pins["sail"]["revision"], timeout, label="Sail")
        self.compiler_binary = (sail_root / "_build/install/default/bin/sail").resolve(strict=True)
        self.compiler_hash = sha(self.compiler_binary)
        self.cc_version = checked_command(["cc", "--version"], timeout=timeout).splitlines()[0]
        self.compiler_version = checked_command([sail_root / "sail", "--version"], env=self.env, timeout=timeout).strip()
        validate_sail_version(self.compiler_version, pins["sail"]["revision"])

    def run(self, requests, name):
        if not requests:
            return []
        source = self.build / f"{name}.sail"
        source.write_text(sail_source(requests))
        target = self.build / name
        files = [ROOT / "spec" / f for f in ("field.sail", "blake2s.sail", "machine.sail", "encoding.sail")]
        files += [ROOT / "tests/differential/print.sail", source]
        runtime = self.root / "lib"
        runtime_files = [runtime / f for f in ("sail.c", "rts.c", "elf.c", "sail_failure.c")]
        inputs = {str(path): sha(path) for path in files + runtime_files}
        checked_command([self.root / "sail", "--no-color", "--memo-z3-path", self.build / "smt-cache", "-c", "-O", *files, "-o", target],
                        env=self.env, timeout=self.timeout)
        checked_command(["cc", "-O2", "-I", runtime, target.with_suffix(".c"),
                         *runtime_files, "-lgmp", "-o", target],
                        env=self.env, timeout=self.timeout)
        require({str(path): sha(path) for path in files + runtime_files} == inputs, "Sail build input changed during compilation")
        require(sha(self.compiler_binary) == self.compiler_hash, "Sail compiler binary changed during compilation")
        self.artifacts[name] = {"source_sha256": inputs[str(source)], "binary_sha256": sha(target),
                                "generated_c_sha256": sha(target.with_suffix(".c")),
                                "runtime_source_hashes": {path.name: inputs[str(path)] for path in runtime_files},
                                "sail_flags": ["-c", "-O"], "cc_flags": ["-O2", "-lgmp"]}
        first = process([target], env=self.env, timeout=self.timeout)
        second = process([target], env=self.env, timeout=self.timeout)
        require(first == second, "Sail replay is nondeterministic")
        if first["status"] != "ok":
            return [first] * len(requests)
        return parse_sail(requests, first["stdout"])


def generate(seed, count):
    rng = random.Random(seed)
    cases = []
    boundary = [0, 1, 2, 1 << 63, MASK, 1 << 64, 1 << 128, (1 << 192) - 1]
    pairs = [(a, b) for a in boundary for b in boundary]
    pairs += [(rng.getrandbits(192), rng.getrandbits(192)) for _ in range(count)]
    for index, (a, b) in enumerate(pairs):
        for kind in ("field", "add"):
            cases.append({"name": f"{kind}-{index}", "request": {"kind": kind, "a": word(a), "b": word(b)}})
    for index, flags in enumerate((0, 1, MASK, 0xFFFFFFFF, 0xFFFFFFFF00000000, 0x0123456789ABCDEF)):
        cases.append({"name": f"blake-flags-{index}", "request": {"kind": "blake",
                      "message": [f"{rng.getrandbits(64):016x}" for _ in range(8)],
                      "cv": [f"{rng.getrandbits(64):016x}" for _ in range(4)], "md": word(rng.getrandbits(64) | (flags << 64))}})
    for index in range(count):
        cases.append({"name": f"blake-random-{index}", "request": {"kind": "blake",
                      "message": [f"{rng.getrandbits(64):016x}" for _ in range(8)],
                      "cv": [f"{rng.getrandbits(64):016x}" for _ in range(4)], "md": word(rng.getrandbits(128))}})
    codec = [["xor", 0, 1, 65535], ["mul", 32768, 63, 64], ["set", 65535, word((1 << 192) - 1)],
             *[["deref", 0, 1, 65535, mode] for mode in ("Cell", "Pc", "Fp")],
             ["jump", 0, 32768, 65535], ["blake", 0, 1, 2, 3, 4, 5, 65535]]
    cases.append({"name": "codec-boundaries", "request": {"kind": "codec", "program": codec}})
    for index in range(max(1, count // 8)):
        a, b = word(rng.getrandbits(192)), word(rng.getrandbits(192))
        ops = [["set", 2, a], ["set", 3, b], ["mul", 2, 3, 4], ["xor", 2, 3, 5],
               ["set", 6, word(1 << 7)], ["deref", 6, 0, 4, "Cell"],
               ["deref", 6, 1, 4, "Pc"], ["deref", 6, 2, 4, "Fp"]]
        for offset in (10, 12, 11, 13, 14, 15, 16):
            ops.append(["set", offset, word(rng.getrandbits(128))])
        ops.append(["blake", 10, 12, 11, 13, 14, 17, 16])
        ops += [["set", 19, word(1)], ["set", 20, word(1 << 22)], ["set", 21, word(1)],
                ["jump", 19, 20, 21], ["set", 2, word(1)], ["set", 3, word(1)],
                ["set", 22, word(0)], ["jump", 22, 20, 21]]
        ops += [["xor", 0, 0, 23]] * (32 - len(ops))
        cases.append({"name": f"program-initialized-{index}", "expected_verdict": "Halted",
                      "mutations": [{"cell": cell, "xor": word(1), "verdict": "BadValue"}
                                    for cell in (2, 4, 5, 7, 8, 9, 17)]
                                   + [{"cell": cell, "xor": word(1 << 128), "verdict": "BadValue"}
                                      for cell in (6, 10, 16)],
                      "request": {"kind": "execute", "program": ops,
                      "input": [word(rng.getrandbits(128)), word(rng.getrandbits(128))]}})
    for case in unique_json((ROOT / "tests/differential/directed.json").read_text()):
        cases.append(deepcopy(case))
    return cases


def normalized(reply, kind):
    require(reply.get("status") == "ok", f"target {reply.get('status')}: {reply.get('error', '')}")
    answer = reply["answer"]
    if kind in ("field", "add"):
        require(isinstance(answer, dict), "invalid field result")
        words([answer.get("base")], 1, "base result")
        words(answer.get("extension"), 3, "extension result")
        return {"base": answer["base"], "extension": answer["extension"]}
    if kind == "blake":
        words(answer, 4, "BLAKE result")
        return answer
    if kind == "codec":
        require(isinstance(answer, dict) and isinstance(answer.get("encoding"), list), "invalid codec result")
        for row in answer["encoding"]:
            words(row, 8, "encoding row")
        return {"encoding": answer["encoding"]}
    require(isinstance(answer, dict) and answer.get("verdict") in (*VERDICTS, "Rejected"), "invalid image verdict")
    if answer["verdict"] == "Rejected":
        return "Rejected"
    return answer["verdict"]


def compare_primitive(replies, kind):
    values = [normalized(reply, kind) for reply in replies]
    require(all(value == values[0] for value in values[1:]), "semantic mismatch")


def validate_reply_request(reply, request):
    if request["kind"] == "codec" and reply.get("status") == "ok":
        answer = normalized(reply, "codec")
        require(len(answer["encoding"]) == len(request["program"]), "codec response row count differs from request")


def compare_image(sail, lean, expected):
    s, l = normalized(sail, "image"), normalized(lean, "image")
    require(s == expected, f"Sail verdict {s} differs from expected {expected}")
    require(l == s or (l == "Rejected" and s in ("BadAccess", "BadValue", "BadInstance")),
            f"checker mismatch: Sail {s}, leanerVM {l}")
    # Compare final state whenever the checker exposes it. Coarse failures do
    # not promise identical diagnostic registers across the two APIs.
    if s == "Halted":
        for register in ("pc", "fp"):
            words([lean["answer"].get(register)], 1, f"leanerVM {register}")
            require(lean["answer"][register] == sail["answer"][register], f"{register} mismatch")
        require(type(lean["answer"].get("steps")) is int and lean["answer"]["steps"] >= 0,
                "leanerVM omitted halt step count")
        if "expected_steps" in sail["answer"]:
            require(lean["answer"]["steps"] == sail["answer"]["expected_steps"], "main step count mismatch")


def attach_expected_count(case, reply):
    count = case.get("expected_main_cycles")
    if count is not None:
        uint(count, MAX_FUEL, "expected main cycles")
        if case.get("expected_verdict") == "Halted" and reply.get("status") == "ok":
            reply["answer"]["expected_steps"] = count


def runtime_artifacts(descriptor, timeout=1200):
    """Bind every available Lean interpreter artifact, including staged IR."""
    paths = [x.split("=", 1)[1] for x in descriptor["command"] if str(x).startswith("LEAN_PATH=")]
    require(len(paths) == 1, "Lean adapter must expose its exact interpreter search path")
    result = {}
    deadline = time.monotonic() + timeout
    for index, root in enumerate(map(Path, paths[0].split(os.pathsep))):
        require(root.is_dir(), "Lean runtime artifact directory is missing")
        digest, eligible_digest, count, eligible_count = hashlib.sha256(), hashlib.sha256(), 0, 0
        for artifact in sorted(root.rglob("*")):
            require(time.monotonic() < deadline, "Lean runtime artifact verification deadline exceeded")
            if not artifact.is_file() or artifact.suffix not in {".olean", ".private", ".server", ".ir", ".sig"}:
                continue
            require(not artifact.is_symlink(), "Lean runtime artifact symlinks are unsupported")
            file_digest = hashlib.sha256()
            with artifact.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1 << 20), b""):
                    file_digest.update(chunk)
            entry = str(artifact.relative_to(root)).encode() + b"\0" + file_digest.digest()
            digest.update(entry)
            count += 1
            if artifact.suffix != ".server":
                eligible_digest.update(entry)
                eligible_count += 1
        require(count > 0, "Lean interpreter search path has no artifacts")
        if index:
            owner = root.parents[3].name
            captured = descriptor.get("dependency_cache_hashes", {}).get(owner)
            require(captured == {"sha256": eligible_digest.hexdigest(), "artifacts": eligible_count},
                    f"Lean dependency cache changed since compilation: {owner}")
        result[f"search_path_{index}"] = {"sha256": digest.hexdigest(), "artifacts": count}
    oracle = Path(descriptor["command"][-1])
    expected = descriptor["source_hashes"].get("adapter/LeanerVMOracle.lean")
    require(oracle.is_file() and not oracle.is_symlink() and sha(oracle) == expected, "Lean staged adapter differs from its source receipt")
    result["adapter_sha256"] = expected
    return result


def image_cases(case, answer):
    require(isinstance(answer, dict), "Rust image response is not an object")
    for key in ("memory_size", "cells", "cycles", "main_cycles", "base_counts", "encoding", "unconstrained_reads"):
        require(key in answer, f"Rust image missing {key}")
    uint(answer["cycles"], MAX_FUEL, "Rust cycles")
    require(type(answer["main_cycles"]) is int and answer["main_cycles"] == answer["cycles"], "Rust filler cycles cannot be used as main fuel")
    base_counts = answer.get("base_counts")
    require(isinstance(base_counts, list) and len(base_counts) == 6
            and all(type(x) is int and x >= 0 for x in base_counts)
            and sum(base_counts) == answer["cycles"], "Rust main opcode counts differ from cycles")
    req = {"kind": "image", "program": case["request"]["program"], "input": case["request"]["input"],
           "memory_size": answer["memory_size"], "cells": answer["cells"], "fuel": answer["cycles"]}
    validate_request(req)
    words_rows = answer["encoding"]
    require(isinstance(words_rows, list) and len(words_rows) == len(req["program"]), "Rust encoding row count differs")
    for row in words_rows:
        words(row, 8, "Rust encoded row")
    expected = case.get("expected_verdict", "Halted")
    results = [(case["name"] + "-exact", deepcopy(req), expected)]
    if expected == "Halted":
        for label, fuel in (("zero", 0), ("insufficient", max(0, req["fuel"] - 1)), ("surplus", req["fuel"] + 1)):
            if fuel > MAX_FUEL:
                continue
            variant = deepcopy(req)
            variant["fuel"] = fuel
            results.append((case["name"] + "-" + label, variant, "Halted" if fuel >= req["fuel"] else "OutOfFuel"))
        variant = deepcopy(req)
        cells = dict(variant["cells"])
        cells[0] = word(integer(cells.get(0, word(0))) ^ 1)
        variant["cells"] = [[i, w] for i, w in sorted(cells.items())]
        results.append((case["name"] + "-public-corruption", variant, "BadInstance"))
    if "corrupt_cell" in case:
        mutations = [{"cell": case["corrupt_cell"], "xor": word(1), "verdict": "BadValue"}]
    else:
        mutations = case.get("mutations", [])
    for index, mutation in enumerate(mutations):
        variant = deepcopy(req)
        cells = dict(variant["cells"])
        cells[mutation["cell"]] = word(integer(cells.get(mutation["cell"], word(0))) ^ integer(mutation["xor"]))
        variant["cells"] = sorted(cells.items())
        # JSON arrays are the public representation; tuples are internal only.
        variant["cells"] = [[i, w] for i, w in variant["cells"]]
        results.append((case["name"] + f"-mutation-{index}", variant, mutation["verdict"]))
    return results


def failure_signature(observed, kind, request=None):
    """Keep reduction within the original failure class and target relation."""
    targets = ("sail", "leanvm", "leanervm") if kind not in ("image", "execute") else ("sail", "leanervm") if kind == "image" else ("leanvm",)
    values, states = [], []
    for target in targets:
        reply = observed.get(target, {"status": "absent"})
        state = reply.get("status", "protocol_error")
        try:
            if request is not None:
                validate_reply_request(reply, request)
            value = normalized(reply, kind) if kind != "execute" else reply.get("answer")
            if kind == "image" and value == "Halted":
                for register in ("pc", "fp"):
                    words([reply["answer"].get(register)], 1, register)
                if target == "leanervm":
                    require(type(reply["answer"].get("steps")) is int and reply["answer"]["steps"] >= 0,
                            "missing halt step count")
        except (RuntimeError, KeyError, TypeError, ValueError):
            value = None
            if state == "ok":
                state = "protocol_error"
        states.append(state)
        values.append(value)
    relation = [values[i] != values[j] for i in range(len(values)) for j in range(i + 1, len(values))]
    classes = tuple(values) if kind == "image" else ()
    if kind == "image" and values == ["Halted", "Halted"]:
        s, l = observed["sail"]["answer"], observed["leanervm"]["answer"]
        classes += tuple(s[key] != l[key] for key in ("pc", "fp"))
        classes += (s.get("expected_steps", l["steps"]) != l["steps"],)
    return (tuple(states), tuple(relation), classes)


def reduction_candidates(case):
    """Shrink data without introducing malformed or unsupported requests."""
    request = case["request"]
    kind = request["kind"]
    keys = ("a", "b") if kind in ("field", "add") else ("message", "cv", "md") if kind == "blake" else ()
    for key in keys:
        for i, limb in enumerate(request[key]):
            value = int(limb, 16)
            if value:
                for replacement in dict.fromkeys((0, value & (value - 1), value & MASK >> 1)):
                    if replacement == value:
                        continue
                    candidate = deepcopy(case)
                    candidate["request"][key][i] = f"{replacement:016x}"
                    yield candidate
    if kind == "codec":
        size = len(request["program"])
        if size > 1:
            for start in (0, size // 2):
                candidate = deepcopy(case)
                candidate["request"]["program"] = request["program"][start:start + size // 2]
                yield candidate
    if kind == "image":
        cells = request["cells"]
        for offset in range(0, len(cells), max(1, len(cells) // 2)):
            candidate = deepcopy(case)
            del candidate["request"]["cells"][offset:offset + max(1, len(cells) // 2)]
            yield candidate


def minimize_case(case, observed, evaluate, attempts):
    """Return a fresh reproduced smaller failure with the same signature."""
    signature = failure_signature(observed, case["request"]["kind"], case["request"])
    current, answers, used = deepcopy(case), observed, 0
    while used < attempts:
        changed = False
        for candidate in reduction_candidates(current):
            if used >= attempts:
                break
            used += 1
            validate_request(candidate["request"])
            new_answers, reason = evaluate(candidate, f"reduce-{used}")
            if reason and failure_signature(new_answers, candidate["request"]["kind"], candidate["request"]) == signature:
                current, answers, changed = candidate, new_answers, True
                break
        if not changed:
            break
    return current, answers, used


def coverage(corpus, observations):
    programs = [case["request"]["program"] for case in corpus if case["request"]["kind"] in ("codec", "execute", "image")]
    opcodes, modes = {}, {}
    for program in programs:
        for op in program:
            opcodes[op[0]] = opcodes.get(op[0], 0) + 1
            if op[0] == "deref":
                modes[op[4]] = modes.get(op[4], 0) + 1
    receipts = {target: 0 for target in ("sail", "leanvm", "leanervm")}
    verdicts = {}
    executed = dict.fromkeys(("xor", "mul", "set", "deref", "jump", "blake"), 0)
    for observation in observations:
        for target, reply in observation["observed"].items():
            require(reply.get("status") == "ok", "passing report contains a failed target")
            receipts[target] += 1
        if observation["kind"] == "image":
            expected = observation["expected_verdict"]
            verdicts[expected] = verdicts.get(expected, 0) + 1
        if observation["kind"] == "execute":
            for opcode, count in zip(executed, observation["observed"]["leanvm"]["answer"]["base_counts"], strict=True):
                executed[opcode] += count
    return {"instruction_occurrences": opcodes, "deref_modes": modes,
            "executed_instruction_counts": executed,
            "adapter_responses": receipts, "checked_image_verdicts": verdicts}


def source_snapshot():
    paths = list((ROOT / "spec").glob("*.sail")) + list((ROOT / "tests/differential").rglob("*"))
    paths += list((ROOT / "scripts").glob("differential*.py"))
    paths += [ROOT / "upstreams.json", ROOT / "tests/oracle.Cargo.lock", ROOT / "tests/test_differential.py"]
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths) if path.is_file() and "__pycache__" not in path.parts}


def fresh_outputs(build, replay):
    """Capture replay input before clearing potentially identical output paths."""
    text, read_error = None, None
    if replay is not None:
        try:
            text = replay.read_text()
        except OSError as error:
            read_error = error
    for name in ("report.json", "failure.json"):
        (build / name).unlink(missing_ok=True)
    if read_error is not None:
        raise read_error
    return text


def validate_sail_version(version, pin):
    require(pin in version, "Sail executable does not match its pinned source revision; rebuild Sail")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sail-root", type=Path, required=True)
    parser.add_argument("--leanvm", type=Path, required=True)
    parser.add_argument("--leanervm", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=20260928)
    parser.add_argument("--cases", type=int, default=16, help="random arithmetic/BLAKE cases; directed cases always run")
    parser.add_argument("--replay", type=Path, help="JSON corpus or saved failure, regenerated against actual targets")
    parser.add_argument("--build", type=Path, default=ROOT / "build/differential")
    parser.add_argument("--timeout", type=float, default=120, help="elapsed limit per process or Sail batch")
    parser.add_argument("--build-timeout", type=float, default=1200, help="separate adapter setup deadline, seconds")
    parser.add_argument("--minimize", type=int, default=0, help="maximum primitive failure reduction attempts")
    args = parser.parse_args()
    build = args.build.resolve()
    build.mkdir(parents=True, exist_ok=True)
    report = build / "report.json"
    failure = build / "failure.json"
    FAILURE_CONTEXT.update(path=failure, seed=args.seed)
    replay_text = fresh_outputs(build, args.replay)
    require(0 <= args.cases <= 512, "cases outside 0..512")
    require(1 <= args.timeout <= 600 and math.isfinite(args.timeout), "timeout outside 1..600 seconds")
    require(1 <= args.build_timeout <= 3600 and math.isfinite(args.build_timeout), "build timeout outside 1..3600 seconds")
    require(0 <= args.minimize <= 64, "minimize outside 0..64 attempts")
    sources = source_snapshot()
    pins = unique_json((ROOT / "tests/differential/targets.json").read_text())
    FAILURE_CONTEXT.update(source_hashes=sources, pins=pins)
    for name, path in (("sail", args.sail_root), ("leanvm", args.leanvm), ("leanervm", args.leanervm)):
        require(revision(path) == pins[name]["revision"], f"{name} revision differs from target pin")
        clean = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        require(checked_command(["git", "--no-replace-objects", "-C", path, "status", "--porcelain", "--untracked-files=no"], env=clean).strip() == "", f"{name} has tracked source changes")
    corpus = generate(args.seed, args.cases)
    if args.replay:
        replay = unique_json(replay_text)
        corpus = replay["cases"] if isinstance(replay, dict) and "cases" in replay else [replay["case"]] if isinstance(replay, dict) and "case" in replay else replay
    require(isinstance(corpus, list) and 1 <= len(corpus) <= 4096, "invalid corpus size")
    for case in corpus:
        require(isinstance(case, dict) and isinstance(case.get("name"), str) and "request" in case, "invalid corpus case")
        validate_request(case["request"])
        if case["request"]["kind"] == "image":
            require(case.get("expected_verdict") in VERDICTS[1:], "image replay needs a terminal expected verdict")
        if "expected_verdict" in case:
            require(case["expected_verdict"] in VERDICTS[1:], "invalid expected verdict")
        if "expected_main_cycles" in case:
            uint(case["expected_main_cycles"], MAX_FUEL, "expected main cycles")
    build.joinpath("corpus.json").write_text(json.dumps({"schema_version": 1, "seed": args.seed, "cases": corpus}, indent=2) + "\n")
    print(f"Building pinned adapters; {len(corpus)} corpus cases", flush=True)
    rust = importlib.import_module("differential_rust").build(ROOT, args.leanvm.resolve(), build / "rust", args.build_timeout)
    require(sha(rust["command"][0]) == rust["binary_sha256"], "Rust adapter binary changed since compilation")
    lean = importlib.import_module("differential_lean").build(ROOT, args.leanervm.resolve(), build / "lean", args.build_timeout)
    print("Verifying Lean runtime artifacts", flush=True)
    lean_runtime = runtime_artifacts(lean, args.build_timeout)
    sail = Sail(args.sail_root.resolve(), build / "sail", args.timeout)
    observations, counts = [], {"field": 0, "add": 0, "blake": 0, "codec": 0, "execute": 0, "image": 0}
    def evaluate(case, label):
        req = case["request"]
        observed = {"sail": sail.run([req], label)[0], "leanervm": adapter_batch(lean, [req], args.timeout)[0]}
        if req["kind"] != "image":
            observed["leanvm"] = adapter_batch(rust, [req], args.timeout)[0]
        try:
            if req["kind"] == "image":
                attach_expected_count(case, observed["sail"])
                compare_image(observed["sail"], observed["leanervm"], case["expected_verdict"])
            else:
                for reply in observed.values():
                    validate_reply_request(reply, req)
                compare_primitive([observed[target] for target in ("sail", "leanvm", "leanervm")], req["kind"])
            return observed, ""
        except RuntimeError as error:
            return observed, str(error)
    def record_error(case, observed, error):
        payload = {"schema_version": 1, "seed": args.seed, "case": case, "observed": observed,
                   "reason": str(error), "source_hashes": sources, "pins": pins}
        failure.write_text(json.dumps(payload, indent=2) + "\n")
        if args.minimize and case["request"]["kind"] != "execute":
            reduced, answers, used = minimize_case(case, observed, evaluate, args.minimize)
            payload.update(case=reduced, observed=answers, reduction_attempts=used,
                           original_case=case, signature=failure_signature(observed, case["request"]["kind"], case["request"]))
            failure.write_text(json.dumps(payload, indent=2) + "\n")
        raise RuntimeError(f"{case['name']}: {error}; replay {failure}") from error
    primitives = [case for case in corpus if case["request"]["kind"] not in ("execute", "image")]
    requests = [case["request"] for case in primitives]
    s = sail.run(requests, "primitives")
    r = adapter_batch(rust, requests, args.timeout)
    l = adapter_batch(lean, requests, args.timeout)
    require(r == adapter_batch(rust, requests, args.timeout), "Rust primitive replay is nondeterministic")
    require(l == adapter_batch(lean, requests, args.timeout), "leanerVM primitive replay is nondeterministic")
    for case, sr, rr, lr in zip(primitives, s, r, l, strict=True):
        observed = {"sail": sr, "leanvm": rr, "leanervm": lr}
        try:
            for reply in (sr, rr, lr):
                validate_reply_request(reply, case["request"])
            compare_primitive([sr, rr, lr], case["request"]["kind"])
        except RuntimeError as error:
            record_error(case, observed, error)
        counts[case["request"]["kind"]] += 1
        observations.append({"name": case["name"], "kind": case["request"]["kind"], "observed": observed})
    images = []
    for case in corpus:
        if case["request"]["kind"] != "execute":
            continue
        print(f"Executing {case['name']}", flush=True)
        rr = adapter_batch(rust, [case["request"]], args.timeout)[0]
        repeated = adapter_batch(rust, [case["request"]], args.timeout)[0]
        try:
            require(rr == repeated, "Rust image generation is nondeterministic")
            require(rr["status"] == "ok", f"Rust execution {rr['status']}")
            produced = image_cases(case, rr["answer"])
            codec_req = {"kind": "codec", "program": case["request"]["program"]}
            original = dict(case, expected_main_cycles=rr["answer"]["cycles"])
            images.extend((original, name, req, expected) for name, req, expected in produced)
            # Each generated program's encoding is checked independently by all
            # three targets as well as against the producing Rust execution.
            codec_s = sail.run([codec_req], f"codec-{counts['execute']}")[0]
            codec_l = adapter_batch(lean, [codec_req], args.timeout)[0]
            codec_r = {"status": "ok", "answer": {"encoding": rr["answer"]["encoding"]}}
            for reply in (codec_s, codec_r, codec_l):
                validate_reply_request(reply, codec_req)
            compare_primitive([codec_s, codec_r, codec_l], "codec")
            counts["codec"] += 1
            observations.append({"name": case["name"] + "-codec", "kind": "codec",
                                 "observed": {"sail": codec_s, "leanvm": codec_r, "leanervm": codec_l}})
        except RuntimeError as error:
            record_error(case, {"leanvm": rr}, error)
        counts["execute"] += 1
        observations.append({"name": case["name"], "kind": "execute", "observed": {"leanvm": rr}})
    # Explicit image replay is useful for reduced checker failures. It records
    # no claim that Rust itself executes an arbitrary immutable image.
    images.extend((case, case["name"], case["request"], case["expected_verdict"])
                  for case in corpus if case["request"]["kind"] == "image")
    for offset in range(0, len(images), 16):
        chunk = images[offset:offset + 16]
        requests = [entry[2] for entry in chunk]
        s = sail.run(requests, f"images-{offset // 16}")
        l = adapter_batch(lean, requests, args.timeout)
        require(l == adapter_batch(lean, requests, args.timeout), "leanerVM image replay is nondeterministic")
        for (original, name, req, expected), sr, lr in zip(chunk, s, l, strict=True):
            try:
                attach_expected_count(dict(original, expected_verdict=expected), sr)
                compare_image(sr, lr, expected)
            except RuntimeError as error:
                record_error({"name": name, "request": req, "expected_verdict": expected,
                              **({"expected_main_cycles": original["expected_main_cycles"]} if "expected_main_cycles" in original else {}),
                              "producer": original}, {"sail": sr, "leanervm": lr}, error)
            counts["image"] += 1
            observations.append({"name": name, "kind": "image", "expected_verdict": expected,
                                 "observed": {"sail": sr, "leanervm": lr}})
        print(f"Checked {min(offset + 16, len(images))}/{len(images)} immutable images", flush=True)
    require(source_snapshot() == sources, "source changed during the campaign")
    require(runtime_artifacts(lean, args.build_timeout) == lean_runtime, "Lean runtime artifacts changed during the campaign")
    require(sha(rust["command"][0]) == rust["binary_sha256"], "Rust adapter binary changed during the campaign")
    require(importlib.import_module("differential_rust")._verify_tree(args.leanvm.resolve(), pins["leanvm"]["revision"], args.timeout)
            == rust["source_hashes"], "Rust source changed during the campaign")
    require(importlib.import_module("differential_rust")._verify_tree(args.sail_root.resolve(), pins["sail"]["revision"], args.timeout,
                                                                   label="Sail") == sail.source_hashes, "Sail source changed during the campaign")
    require(sha(sail.compiler_binary) == sail.compiler_hash, "Sail compiler changed during the campaign")
    measured = coverage(corpus, observations)
    if not args.replay:
        require(all(counts[k] > 0 for k in counts), "campaign omitted a required case kind")
        require(set(measured["instruction_occurrences"]) == {"set", "xor", "mul", "deref", "jump", "blake"}, "campaign omitted an opcode")
        require(set(measured["deref_modes"]) == {"Cell", "Pc", "Fp"}, "campaign omitted a DEREF mode")
        require(all(value > 0 for value in measured["executed_instruction_counts"].values()), "campaign did not execute every opcode")
        require(all(value > 0 for value in measured["adapter_responses"].values()), "campaign omitted a target")
    # Successful reports are created only after every adapter and replay gate.
    result = {"schema_version": 1, "status": "pass", "protocol": "leanisa-jsonl-v1", "seed": args.seed,
              "campaign": "replay" if args.replay else "directed-and-seeded", "coverage": measured,
              "limits": {"runtime_address_space_gib": 8, "runtime_timeout_seconds": args.timeout,
                         "runtime_output_bytes": 16 << 20, "adapter_build_timeout_seconds": args.build_timeout},
              "counts": counts, "pins": pins, "source_hashes": sources, "corpus_sha256": sha(build / "corpus.json"),
              "adapters": {"leanvm": {k: v for k, v in rust.items() if k not in ("command", "cwd", "env")},
                           "leanervm": {**{k: v for k, v in lean.items() if k not in ("command", "cwd", "env")},
                                        "runtime_artifact_hashes": lean_runtime},
                           "sail": {"mode": "generated-c", "compiler_sha256": sail.compiler_hash,
                                    "compiler_version": sail.compiler_version, "cc_version": sail.cc_version,
                                    "source_hashes": sail.source_hashes, "artifacts": sail.artifacts}},
              "observations": observations}
    report.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Three-target differential campaign PASS: {counts}; {report}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        path = FAILURE_CONTEXT.get("path")
        if path is not None and not path.exists():
            path.write_text(json.dumps({"schema_version": 1, "status": "startup_or_campaign_failure",
                                        **{key: value for key, value in FAILURE_CONTEXT.items() if key != "path"},
                                        "reason": str(error)}, indent=2) + "\n")
        print(f"differential campaign failed: {error}", file=sys.stderr)
        raise SystemExit(1)
