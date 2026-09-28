/-
JSON-lines adapter for pinned leanerVM

This adapter translates fixtures into leanerVM carriers and calls its field operations,
BLAKE2s compression, canonical bytecode entry encoder/decoder, and immutable-image checker.
It supplies no replacement instruction semantics. Run with `lean --run`, whose interpreter
loads definitions on demand; a native executable at this dependency pin eagerly enumerates
`Fintype BF64` at startup. Build and process limits are imposed by the Python driver.
-/
import LeanerVM.Semantics.Checker
import LeanerVM.Arithmetization.Bytecode
import Lean.Data.Json

open Lean LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization

namespace LeanerVMOracle

private def str (s : String) : Json := .str s
private def obj (xs : List (String × Json)) : Json := Json.mkObj xs
private def arr (xs : Array Json) : Json := .arr xs
private def field (j : Json) (name : String) : Except String Json := j.getObjVal? name
private def array (j : Json) : Except String (Array Json) := j.getArr?
private def string (j : Json) : Except String String := j.getStr?
private def natural (j : Json) : Except String Nat := j.getNat?

private def parseHex (j : Json) : Except String K := do
  let s ← string j
  if s.length != 16 then throw "expected sixteen hexadecimal digits"
  let mut n := 0
  for c in s.toList do
    let d ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
      else throw "expected lowercase hexadecimal digits"
    n := n * 16 + d
  pure (BitVec.ofNat 64 n)

private def hex (x : K) : Json := str x.toHex

private def word (j : Json) : Except String E := do
  let xs ← array j
  if xs.size != 3 then throw "expected three field limbs"
  pure (E.ofLimbs (← parseHex xs[0]!) (← parseHex xs[1]!) (← parseHex xs[2]!))

private def wordJson (x : E) : Json := arr #[hex (x.limb 0), hex (x.limb 1), hex (x.limb 2)]

private def offset (j : Json) : Except String K := do
  let n ← natural j
  if n ≥ 2 ^ 32 then throw "operand exponent exceeds u32"
  pure (gpow n)

private def instruction (j : Json) : Except String Instr := do
  let xs ← array j
  if xs.isEmpty then throw "empty instruction"
  let name ← string xs[0]!
  let arity := if name == "set" then 3 else if name == "deref" then 5
    else if name == "blake" then 8 else 4
  if xs.size != arity then throw "wrong instruction arity"
  match name with
  | "xor" => pure (.xor (← offset xs[1]!) (← offset xs[2]!) (← offset xs[3]!))
  | "mul" => pure (.mulNative (← offset xs[1]!) (← offset xs[2]!) (← offset xs[3]!))
  | "set" => pure (.setConstant (← offset xs[1]!) (← word xs[2]!))
  | "deref" =>
    let mode ← match ← string xs[4]! with
      | "Cell" => pure DerefMode.cell
      | "Pc" => pure DerefMode.pc
      | "Fp" => pure DerefMode.fp
      | _ => throw "unknown dereference mode"
    pure (.deref (← offset xs[1]!) (← offset xs[2]!) (← offset xs[3]!) mode)
  | "jump" => pure (.jump (← offset xs[1]!) (← offset xs[2]!) (← offset xs[3]!))
  | "blake" =>
    let m0 ← offset xs[1]!; let m1 ← offset xs[2]!; let m2 ← offset xs[3]!
    let m3 ← offset xs[4]!
    pure (.blake2s ![m0,m1,m2,m3] (← offset xs[5]!) (← offset xs[6]!) (← offset xs[7]!))
  | _ => throw "unknown instruction"

private def instructions (j : Json) : Except String (Array Instr) := do
  (← array j).mapM instruction

private def logSize (n : Nat) : Except String Nat := do
  if n == 0 || n > 2 ^ 20 then throw "image/program size exceeds adapter limit"
  let k := n.log2
  if 2 ^ k != n then throw "image/program size is not a power of two"
  pure k

private def program (code : Array Instr) : Except String Program := do
  let k ← logSize code.size
  if h : k ≤ maxLogBytecode then
    pure ⟨k, h, fun i => code[i.val]?.getD (.xor 1 1 1)⟩
  else throw "program size exceeds bytecode bound"

private def checkError : CheckError → String
  | .publicBoundary => "publicBoundary"
  | .invalidStep => "invalidStep"
  | .finalFrame => "finalFrame"
  | .fuelExhausted => "fuelExhausted"

private def imageAnswer (j : Json) : Except String Json := do
  let prog ← program (← instructions (← field j "program"))
  let n ← natural (← field j "memory_size")
  let k ← logSize n
  let fuel ← natural (← field j "fuel")
  if fuel > 1000000 then throw "fuel exceeds adapter limit"
  let words ← array (← field j "input")
  if words.size != 2 then throw "expected two public words"
  let w0 ← word words[0]!
  let w1 ← word words[1]!
  if w0.limb 2 != 0 || w1.limb 2 != 0 then
    pure (obj [("verdict", str "Rejected"), ("raw", str "publicBoundary")])
  else
    let mut cells : Array (Nat × E) := #[]
    for c in ← array (← field j "cells") do
      let pair ← array c
      if pair.size != 2 then throw "expected index and word"
      let idx ← natural pair[0]!
      if idx ≥ n then throw "cell index exceeds image"
      if cells.any (fun x => x.1 == idx) then throw "duplicate cell index"
      cells := cells.push (idx, ← word pair[1]!)
    let image : MemImage k := fun i =>
      (cells.find? (fun x => x.1 == i.val)).map Prod.snd |>.getD 0
    let input : PublicInput := ⟨![w0.limb 0,w0.limb 1,w1.limb 0,w1.limb 1]⟩
    match checkWithinFuel prog input image fuel with
    | .ok steps => pure (obj [("verdict", str "Halted"), ("steps", toJson steps),
        ("pc", hex prog.finalPc), ("fp", hex 1)])
    | .error e => pure (obj [("verdict", str (if e == .fuelExhausted then "OutOfFuel" else "Rejected")),
        ("raw", str (checkError e))])

private def blakeAnswer (j : Json) : Except String Json := do
  let message ← array (← field j "message")
  let cv ← array (← field j "cv")
  if message.size != 8 || cv.size != 4 then throw "wrong BLAKE limb count"
  let ms ← message.mapM parseHex
  let hs ← cv.mapM parseHex
  let md ← word (← field j "md")
  if md.limb 2 != 0 then throw "noncanonical BLAKE metadata"
  let m : Vector UInt32 16 := Vector.ofFn fun i =>
    if i.val % 2 == 0 then lowWord ms[i.val / 2]! else highWord ms[i.val / 2]!
  let h : Vector UInt32 8 := Vector.ofFn fun i =>
    if i.val % 2 == 0 then lowWord hs[i.val / 2]! else highWord hs[i.val / 2]!
  let v := compress h m (unpackMetadata md).1 (unpackMetadata md).2.1 (unpackMetadata md).2.2
  pure (arr ((Array.range 4).map fun i => hex (ofWords v[i*2]! v[i*2+1]!)))

private def answer (j : Json) : Except String Json := do
  match ← string (← field j "kind") with
  | "field" | "add" =>
    let a ← word (← field j "a")
    let b ← word (← field j "b")
    let adding := (← string (← field j "kind")) == "add"
    let base := if adding then a.limb 0 + b.limb 0 else a.limb 0 * b.limb 0
    let extension := if adding then a + b else a * b
    pure (obj [("base",hex base),("extension",wordJson extension)])
  | "blake" => blakeAnswer j
  | "codec" =>
    let code ← instructions (← field j "program")
    pure (obj [("encoding",arr (code.map fun i => arr ((entry i).toArray.map hex)))])
  | "decode" =>
    let xs ← array (← field j "entry")
    if xs.size != 8 then throw "expected eight entry coordinates"
    let values ← xs.mapM parseHex
    let v : Vector K 8 := Vector.ofFn fun i => values[i.val]!
    match decode v with
    | none => pure (obj [("verdict",str "Rejected")])
    | some i => pure (obj [("verdict",str "Accepted"),("entry",arr ((entry i).toArray.map hex))])
  | "image" => imageAnswer j
  | _ => throw "unknown fixture kind"

/-- Evaluate one request, distinguishing malformed input from a semantic rejection. -/
def respond (j : Json) : Json :=
  match answer j with
  | .ok a => obj [("status",str "ok"),("answer",a)]
  | .error e => obj [("status",str "error"),("error",str e)]

end LeanerVMOracle

/-- Read JSON lines until EOF, emitting exactly one JSON response per input line. -/
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let response := match Json.parse line with
      | .ok j => LeanerVMOracle.respond j
      | .error e => Json.mkObj [("status",.str "error"),("error",.str e)]
    output.putStrLn response.compress
    output.flush
