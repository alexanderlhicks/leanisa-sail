import CircularProbe

namespace Leanisa.Proofs.I1a.Checks
open Sail Leanisa.Functions Leanisa.Proofs.I1a

private def entry (a : BitVec 64) : address_entry := ⟨a, 0⟩
private def oneEmpty : Vector address_entry 1 := #v[entry 0]
private def oneHit : Vector address_entry 1 := #v[entry 1]
private def oneMiss : Vector address_entry 1 := #v[entry 2]
private def threeFirst : Vector address_entry 3 := #v[entry 2, entry 2, entry 1]
private def threeWrap : Vector address_entry 3 := #v[entry 1, entry 2, entry 2]
private def threeLast : Vector address_entry 3 := #v[entry 2, entry 1, entry 2]
private def threeFullMiss : Vector address_entry 3 := #v[entry 2, entry 2, entry 2]
private def threeCollision : Vector address_entry 3 := #v[entry 1, entry 2, entry 4]
private def threeZero : Vector address_entry 3 := #v[entry 2, entry 0, entry 2]

theorem zero_capacity :
    address_slot (#v[] : Vector address_entry 0) 1 = circularProbe #v[] 1 ∧
    address_slot (#v[] : Vector address_entry 0) 1 = none := by decide +kernel

theorem singleton_empty :
    address_slot oneEmpty 1 = circularProbe oneEmpty 1 ∧
    address_slot oneEmpty 1 = some 0 := by decide +kernel

theorem singleton_hit :
    address_slot oneHit 1 = circularProbe oneHit 1 ∧
    address_slot oneHit 1 = some 0 := by decide +kernel

theorem singleton_full_miss :
    address_slot oneMiss 1 = circularProbe oneMiss 1 ∧
    address_slot oneMiss 1 = none := by decide +kernel

theorem nonpower_first :
    address_slot threeFirst 1 = circularProbe threeFirst 1 ∧
    address_slot threeFirst 1 = some 2 := by decide +kernel

theorem wrap_to_zero :
    address_slot threeWrap 1 = circularProbe threeWrap 1 ∧
    address_slot threeWrap 1 = some 0 := by decide +kernel

theorem last_permitted :
    address_slot threeLast 1 = circularProbe threeLast 1 ∧
    address_slot threeLast 1 = some 1 := by decide +kernel

theorem full_miss :
    address_slot threeFullMiss 1 = circularProbe threeFullMiss 1 ∧
    address_slot threeFullMiss 1 = none := by decide +kernel

theorem wrong_key_same_start :
    startSlot 3 1 = startSlot 3 4 ∧
    address_slot threeCollision 1 = circularProbe threeCollision 1 ∧
    address_slot threeCollision 1 = some 0 := by decide +kernel

theorem zero_target :
    address_slot threeZero 0 = circularProbe threeZero 0 ∧
    address_slot threeZero 0 = some 1 := by decide +kernel

end Leanisa.Proofs.I1a.Checks
