import Arithmetic

/-! Executable policy regressions. These exercise the Lean functions on concrete
values; they are not additional kernel-certified arithmetic theorems. The general
simulation and runner theorems are in Arithmetic.lean. -/
namespace Leanisa.Proofs.ArithmeticChecks
open Leanisa.Functions

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError s!"MUL policy regression: {label}")

private def rightUnknown : PartialMemory 3 := fun i =>
  if i = 0 then some 3 else if i = 1 then none else some 6

private def leftUnknown : PartialMemory 3 := fun i =>
  if i = 0 then none else if i = 1 then some 3 else some 6

#eval do
  check ((mulAssignWithAdvice rightUnknown 1 2 0 1 2).map
    (fun (memory : PartialMemory 3) => (memory 0, memory 1, memory 2)) == some (some 3, some 2, some 6))
    "candidate for the right operand"
  check ((mulAssignWithAdvice leftUnknown 0 2 0 1 2).map
    (fun (memory : PartialMemory 3) => (memory 0, memory 1, memory 2)) == some (some 2, some 3, some 6))
    "candidate for the left operand"
  check (mulAssignWithAdvice rightUnknown 1 3 0 1 2).isNone
    "incorrect candidate must conflict with the known result"
  check (mulAssignWithAdvice (observeZero rightUnknown 1).2 1 2 0 1 2).isNone
    "advice cannot replace a previously observed zero"
  check (mulAssign (fun (_ : Fin 1) => some 1) 0 0 0).isSome
    "fully aliased one is consistent"
  check (mulAssign (fun (_ : Fin 1) => some 2) 0 0 0).isNone
    "fully aliased two would change the observed input"
  check (mulAssign (fun (_ : Fin 1) => none) 0 0 0).isSome
    "fully aliased unset cell fixes zero"
  -- Valid checked advice need not come from division; a zero factor imposes no
  -- unique solution. This is broader than the pinned Rust inverse-based policy.
  let zeroProduct : PartialMemory 3 := fun i => if i = 1 then none else some 0
  check ((mulAssignWithAdvice zeroProduct 1 7 0 1 2).map (fun (memory : PartialMemory 3) => memory 1) ==
    some (some 7)) "a verified zero product admits compatible advice"
  -- y * y² = y + 1 checks extension reduction rather than only base-field limbs.
  let y : Word := 0x000000000000000000000000000000010000000000000000
  let y2 : Word := 0x000000000000000100000000000000000000000000000000
  let extension : PartialMemory 3 := fun i =>
    if i = 0 then some y else if i = 1 then some y2 else none
  check ((mulAssign extension 0 1 2).map (fun (memory : PartialMemory 3) => memory 2) == some (some (y ^^^ 1)))
    "cubic extension reduction"

end Leanisa.Proofs.ArithmeticChecks
