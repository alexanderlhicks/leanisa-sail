import EncodedOperands

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Functions Sail
namespace Leanisa.Proofs.Encoded

private theorem frame_access {m : Nat} (s : machine_state) (frame offset : Nat)
    (target : Fin m) (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (index : target.val = frame + offset) :
    kmul s.fp (gAddress offset) = gAddress target.val :=
  encoded_access s.fp (gAddress offset) frame offset target bound frameRep rfl index

/-- One compatible SET assignment, keeping the immediate unchanged. -/
theorem encoded_set {m : Nat} (s : machine_state) (frame offset : Nat)
    (target : Fin m) (value : Word) {before after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (index : target.val = frame + offset)
    (assigned : assign before target value = some after) :
    IsaStep s before (.Set (gAddress offset, value)) after (advancedState s) [] := by
  exact .arithmetic (.setXor (.set (gAddress offset) target value
    (frame_access s frame offset target bound frameRep index) assigned))

/-- Ordered XOR observations and assignment remain the exact policy operation. -/
theorem encoded_xor {m : Nat} (s : machine_state) (frame oa ob oc : Nat)
    (a b c : Fin m) {before after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (ia : a.val = frame + oa) (ib : b.val = frame + ob) (ic : c.val = frame + oc)
    (assigned : xorAssign before a b c = some after) :
    IsaStep s before (.Xor (gAddress oa, gAddress ob, gAddress oc))
      after (advancedState s) [] := by
  exact .arithmetic (.setXor (.xor (gAddress oa) (gAddress ob) (gAddress oc) a b c
    (frame_access s frame oa a bound frameRep ia)
    (frame_access s frame ob b bound frameRep ib)
    (frame_access s frame oc c bound frameRep ic) assigned))

/-- Ordered MUL product operation; aliases remain governed by `mulAssign`. -/
theorem encoded_mul {m : Nat} (s : machine_state) (frame oa ob oc : Nat)
    (a b c : Fin m) {before after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (ia : a.val = frame + oa) (ib : b.val = frame + ob) (ic : c.val = frame + oc)
    (assigned : mulAssign before a b c = some after) :
    IsaStep s before (.Mul (gAddress oa, gAddress ob, gAddress oc))
      after (advancedState s) [] := by
  exact .arithmetic (.mul (gAddress oa) (gAddress ob) (gAddress oc) a b c
    (frame_access s frame oa a bound frameRep ia)
    (frame_access s frame ob b bound frameRep ib)
    (frame_access s frame oc c bound frameRep ic) assigned)

/-- Checked advice stays an explicit premise and does not assert solver success. -/
theorem encoded_mul_advice {m : Nat} (s : machine_state) (frame oa ob oc : Nat)
    (a b c hint : Fin m) (value : Word) {before after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (ia : a.val = frame + oa) (ib : b.val = frame + ob) (ic : c.val = frame + oc)
    (assigned : mulAssignWithAdvice before hint value a b c = some after) :
    IsaStep s before (.Mul (gAddress oa, gAddress ob, gAddress oc))
      after (advancedState s) [] := by
  exact .arithmetic (.mulAdvice (gAddress oa) (gAddress ob) (gAddress oc) a b c hint value
    (frame_access s frame oa a bound frameRep ia)
    (frame_access s frame ob b bound frameRep ib)
    (frame_access s frame oc c bound frameRep ic) assigned)

/-- All three JUMP reads and K guards are unconditional, including fallthrough. -/
theorem encoded_jump {m : Nat} (s : machine_state) (frame oc od ofp : Nat)
    (c d f : Fin m) (vc vd vf : Word) {before after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (ic : c.val = frame + oc) (id : d.val = frame + od) (iffp : f.val = frame + ofp)
    (reads : Observed before [(c, vc), (d, vd), (f, vf)] after)
    (kc : in_k vc = true) (kd : in_k vd = true) (kf : in_k vf = true) :
    IsaStep s before (.Jump (gAddress oc, gAddress od, gAddress ofp))
      after (jumpState s vc vd vf) [] := by
  exact .jump (.checked (gAddress oc) (gAddress od) (gAddress ofp) c d f vc vd vf
    (frame_access s frame oc c bound frameRep ic)
    (frame_access s frame od d bound frameRep id)
    (frame_access s frame ofp f bound frameRep iffp) reads kc kd kf)

/-- Fallthrough permits arbitrary K-valued loaded destination and frame words. -/
theorem encoded_jump_fallthrough {m : Nat} (s : machine_state) (frame oc od ofp : Nat)
    (c d f : Fin m) (vc vd vf : Word) {before after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (ic : c.val = frame + oc) (id : d.val = frame + od) (iffp : f.val = frame + ofp)
    (reads : Observed before [(c, vc), (d, vd), (f, vf)] after)
    (kc : in_k vc = true) (kd : in_k vd = true) (kf : in_k vf = true)
    (zero : lowK vc = 0) :
    IsaStep s before (.Jump (gAddress oc, gAddress od, gAddress ofp))
      after (advancedState s) [] := by
  simpa [jumpState, zero] using
    encoded_jump s frame oc od ofp c d f vc vd vf bound frameRep ic id iffp reads kc kd kf

/-- A taken JUMP gives represented next registers only from explicit loaded representations. -/
theorem encoded_jump_taken {m : Nat} (s : machine_state) (frame oc od ofp : Nat)
    (c d f : Fin m) (vc vd vf : Word) (nextPC nextFrame : Nat)
    {before after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (ic : c.val = frame + oc) (id : d.val = frame + od) (iffp : f.val = frame + ofp)
    (reads : Observed before [(c, vc), (d, vd), (f, vf)] after)
    (kc : in_k vc = true) (kd : in_k vd = true) (kf : in_k vf = true)
    (nonzero : lowK vc ≠ 0) (pcRep : lowK vd = gAddress nextPC)
    (nextFrameRep : lowK vf = gAddress nextFrame) :
    IsaStep s before (.Jump (gAddress oc, gAddress od, gAddress ofp))
      after ⟨gAddress nextPC, gAddress nextFrame⟩ [] := by
  have zeroEq : (0 : BitVec 64) = 0#64 := by decide
  have branch : (lowK vc != (0#64)) = true := by
    rw [← zeroEq]
    exact bne_iff_ne.mpr nonzero
  simpa [jumpState, branch, pcRep, nextFrameRep] using
    encoded_jump s frame oc od ofp c d f vc vd vf bound frameRep ic id iffp reads kc kd kf

end Leanisa.Proofs.Encoded
