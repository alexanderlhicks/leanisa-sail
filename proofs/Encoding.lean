import Leanisa

namespace Leanisa.Proofs
open Sail Leanisa.Functions instruction deref_mode

/-- The candidate-producing expression from the extracted decoder. The
canonicality loop is accounted for separately in `decode_characterization`. -/
private def decodeCandidate (row : Vector (BitVec 64) 8) : Option instruction :=
  match row[0]! with
  | 1 => some (.Xor (row[1]!, row[2]!, row[3]!))
  | 2 => some (.Mul (row[1]!, row[2]!, row[3]!))
  | 4 => some (.Set (row[1]!, row[4]! +++ (row[3]! +++ row[2]!)))
  | 8 =>
    if row[4]! == 0 && row[5]! == 0 then some (.Deref (row[1]!, row[2]!, row[3]!, .Cell))
    else if row[4]! == 1 && row[5]! == 0 then some (.Deref (row[1]!, row[2]!, row[3]!, .Pc))
    else if row[4]! == 0 && row[5]! == 1 then some (.Deref (row[1]!, row[2]!, row[3]!, .Fp))
    else none
  | 16 => some (.Jump (row[1]!, row[2]!, row[3]!))
  | 32 => some (.Blake2s (row[1]!, row[2]!, row[3]!, row[4]!, row[5]!, row[6]!, row[7]!))
  | _ => none

private theorem assemble_word (k : BitVec 192) :
    Sail.BitVec.extractLsb k 191 128 +++
      (Sail.BitVec.extractLsb k 127 64 +++ Sail.BitVec.extractLsb k 63 0) = k := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_append_extractLsb'

@[local simp] private theorem getElem_vectorUpdate {α : Type} {n : Nat} (v : Vector α n)
    (i j : Nat) (a : α) (hj : j < n) :
    (vectorUpdate v i a)[j] = if i = j then a else v[j] := by
  change (v.setIfInBounds i a)[j] = _
  exact Vector.getElem_setIfInBounds hj

@[local simp] private theorem mode_beq (a b : deref_mode) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

private theorem candidate_encode (ins : instruction) : decodeCandidate (encode ins) = some ins := by
  cases ins with
  | Xor operands => rcases operands with ⟨a, b, c⟩; simp [decodeCandidate, encode]
  | Mul operands => rcases operands with ⟨a, b, c⟩; simp [decodeCandidate, encode]
  | Set operands =>
    rcases operands with ⟨o, k⟩
    simpa [decodeCandidate, encode] using assemble_word k
  | Deref operands => rcases operands with ⟨a, b, c, mode⟩; cases mode <;> simp [decodeCandidate, encode]
  | Jump operands => rcases operands with ⟨a, b, c⟩; simp [decodeCandidate, encode]
  | Blake2s operands => rcases operands with ⟨a, b, c, d, cv, out, md⟩; simp [decodeCandidate, encode]

private def checkRange : IntRange := { start := 0, stop := 7 }

private def checkBody (encoded row : Vector (BitVec 64) 8)
    (i : Int) (_ : i ∈ checkRange) (_ : Unit) :
    ExceptM (Option instruction) (ForInStep Unit) :=
  if encoded[i]! != row[i]! then .error none else .ok (.yield ())

private def AgreeFrom (encoded row : Vector (BitVec 64) 8) (j : Nat) : Prop :=
  ∀ k : Fin 8, j ≤ k.val → encoded.get k = row.get k

private instance (encoded row : Vector (BitVec 64) 8) (j : Nat) :
    Decidable (AgreeFrom encoded row j) := inferInstanceAs (Decidable (∀ k : Fin 8,
      j ≤ k.val → encoded.get k = row.get k))

private theorem check_loop (encoded row : Vector (BitVec 64) 8) (j : Nat) (hj : j ≤ 8)
    (hs : ((j : Int) - checkRange.start) % checkRange.step = 0) :
    IntRange.forIn'.loop (m := ExceptM (Option instruction)) checkRange (checkBody encoded row)
      () (j : Int) hs = if AgreeFrom encoded row j then .ok () else .error none := by
  rw [IntRange.forIn'.loop]
  by_cases inside : j < 8
  · have hin : (j : Int) ∈ checkRange := by simp [checkRange, Membership.mem]; omega
    simp only [dif_pos hin]
    have element (v : Vector (BitVec 64) 8) : v[(j : Int)]! = v.get ⟨j, inside⟩ := by
      change v[j]! = _
      simp [Vector.get, inside]
    by_cases equal : encoded.get ⟨j, inside⟩ = row.get ⟨j, inside⟩
    · simp only [checkBody, element, equal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
      change IntRange.forIn'.loop (m := ExceptM (Option instruction)) checkRange
        (checkBody encoded row) () ((j + 1 : Nat) : Int) _ = _
      rw [check_loop encoded row (j + 1) (by omega)]
      have next : AgreeFrom encoded row j ↔ AgreeFrom encoded row (j + 1) := by
        constructor
        · intro all k hk; exact all k (by omega)
        · intro all k hk
          by_cases sameIndex : k.val = j
          · have index : k = ⟨j, inside⟩ := Fin.ext sameIndex
            subst k
            exact equal
          · exact all k (by omega)
      simp only [next]
    · have notAll : ¬ AgreeFrom encoded row j := fun all => equal (all ⟨j, inside⟩ (Nat.le_refl j))
      simp only [checkBody, element, bne_iff_ne.mpr equal, ↓reduceIte, if_neg notAll,
        bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
      rfl
  · have hout : (j : Int) ∉ checkRange := by simp [checkRange, Membership.mem]; omega
    have all : AgreeFrom encoded row j := by intro k hk; have := k.isLt; omega
    simp only [dif_neg hout, if_pos all]
    rfl
termination_by 8 - j

private theorem decode_characterization (row : Vector (BitVec 64) 8) :
    decode row = match decodeCandidate row with
      | none => none
      | some ins => if encode ins = row then some ins else none := by
  simp only [decode, pure_bind, ExceptT.bind_throw]
  change ExceptM.run (match decodeCandidate row with
    | none => pure none
    | some ins => do
      let _ ← IntRange.forIn'.loop (m := ExceptM (Option instruction)) checkRange
        (checkBody (encode ins) row) () (0 : Int) (by simp [checkRange])
      pure (some ins)) = _
  cases candidate : decodeCandidate row with
  | none => rfl
  | some ins =>
    dsimp only
    have agree : AgreeFrom (encode ins) row 0 ↔ encode ins = row := by
      constructor
      · intro all
        apply Vector.ext
        intro i hi
        exact all ⟨i, hi⟩ (Nat.zero_le i)
      · intro same
        subst row
        intro k _
        rfl
    have checked := congrArg
      (fun result : ExceptM (Option instruction) Unit => ExceptM.run (do
        let _ ← result
        pure (some ins)))
      (check_loop (encode ins) row 0 (by omega) (by simp [checkRange]))
    by_cases same : encode ins = row
    · simpa only [agree, if_pos same] using checked
    · simpa only [agree, if_neg same] using checked

/-- Every typed instruction round-trips through the actual extracted decoder.
All 192 immediate bits and arbitrary 64-bit operands are admitted. -/
theorem decode_encode (ins : instruction) : decode (encode ins) = some ins := by
  rw [decode_characterization, candidate_encode]
  simp

/-- Successful decoding preserves every word of the canonical input row. -/
theorem encode_of_decode {row : Vector (BitVec 64) 8} {ins : instruction}
    (accepted : decode row = some ins) : encode ins = row := by
  rw [decode_characterization] at accepted
  cases candidate : decodeCandidate row with
  | none => simp [candidate] at accepted
  | some actual =>
    simp only [candidate] at accepted
    split at accepted
    next canonical =>
      have same : actual = ins := Option.some.inj accepted
      simpa only [same] using canonical
    next noncanonical => contradiction

/-- The encoding loses no instruction information. -/
theorem encode_injective {first second : instruction} (same : encode first = encode second) :
    first = second := by
  have decoded := congrArg decode same
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

/-- The accepted rows are exactly the image of the typed encoder. -/
theorem canonical_iff_accepted (row : Vector (BitVec 64) 8) :
    (∃ ins, encode ins = row) ↔ ∃ ins, decode row = some ins := by
  constructor
  · rintro ⟨ins, rfl⟩
    exact ⟨ins, decode_encode ins⟩
  · rintro ⟨ins, accepted⟩
    exact ⟨ins, encode_of_decode accepted⟩

def SupportedOpcode (opcode : BitVec 64) : Prop :=
  opcode = 1 ∨ opcode = 2 ∨ opcode = 4 ∨ opcode = 8 ∨ opcode = 16 ∨ opcode = 32

theorem encode_supported (ins : instruction) : SupportedOpcode (encode ins)[0]! := by
  cases ins with
  | Xor operands => rcases operands with ⟨a, b, c⟩; simp [SupportedOpcode, encode]
  | Mul operands => rcases operands with ⟨a, b, c⟩; simp [SupportedOpcode, encode]
  | Set operands => rcases operands with ⟨a, k⟩; simp [SupportedOpcode, encode]
  | Deref operands => rcases operands with ⟨a, b, c, mode⟩; simp [SupportedOpcode, encode]
  | Jump operands => rcases operands with ⟨a, b, c⟩; simp [SupportedOpcode, encode]
  | Blake2s operands => rcases operands with ⟨a, b, c, d, cv, out, md⟩; simp [SupportedOpcode, encode]

theorem decode_unknown_opcode (row : Vector (BitVec 64) 8)
    (unsupported : ¬ SupportedOpcode row[0]!) : decode row = none := by
  cases accepted : decode row with
  | none => rfl
  | some ins =>
    have supported := encode_supported ins
    rw [encode_of_decode accepted] at supported
    exact False.elim (unsupported supported)

def ValidDerefFlags (row : Vector (BitVec 64) 8) : Prop :=
  (row[4]! = 0 ∧ row[5]! = 0) ∨ (row[4]! = 1 ∧ row[5]! = 0) ∨
    (row[4]! = 0 ∧ row[5]! = 1)

theorem encode_deref_flags (ins : instruction) (opcode : (encode ins)[0]! = 8) :
    ValidDerefFlags (encode ins) := by
  cases ins with
  | Xor operands => rcases operands with ⟨a, b, c⟩; simp [encode] at opcode
  | Mul operands => rcases operands with ⟨a, b, c⟩; simp [encode] at opcode
  | Set operands => rcases operands with ⟨a, k⟩; simp [encode] at opcode
  | Deref operands => rcases operands with ⟨a, b, c, mode⟩; cases mode <;> simp [ValidDerefFlags, encode]
  | Jump operands => rcases operands with ⟨a, b, c⟩; simp [encode] at opcode
  | Blake2s operands => rcases operands with ⟨a, b, c, d, cv, out, md⟩; simp [encode] at opcode

theorem decode_invalid_deref_flags (row : Vector (BitVec 64) 8) (opcode : row[0]! = 8)
    (invalid : ¬ ValidDerefFlags row) : decode row = none := by
  cases accepted : decode row with
  | none => rfl
  | some ins =>
    have same := encode_of_decode accepted
    have flags := encode_deref_flags ins (by simpa only [same] using opcode)
    exact False.elim (invalid (by simpa only [same] using flags))

/-- Opcode-specific lower bounds for unused trailing positions. The rejection
theorem separately requires the index to be within the eight-word row. -/
def UnusedPosition (row : Vector (BitVec 64) 8) (i : Nat) : Prop :=
  ((row[0]! = 1 ∨ row[0]! = 2 ∨ row[0]! = 16) ∧ 4 ≤ i) ∨
    (row[0]! = 4 ∧ 5 ≤ i) ∨ (row[0]! = 8 ∧ 6 ≤ i)

theorem encode_unused_zero (ins : instruction) (i : Nat) (hi : i < 8)
    (unused : UnusedPosition (encode ins) i) : (encode ins)[i]! = 0 := by
  cases ins with
  | Xor operands =>
    rcases operands with ⟨a, b, c⟩
    simp [UnusedPosition, encode] at unused
    simp [encode, hi, vectorInit, show ¬ 0 = i by omega, show ¬ 1 = i by omega,
      show ¬ 2 = i by omega, show ¬ 3 = i by omega]
  | Mul operands =>
    rcases operands with ⟨a, b, c⟩
    simp [UnusedPosition, encode] at unused
    simp [encode, hi, vectorInit, show ¬ 0 = i by omega, show ¬ 1 = i by omega,
      show ¬ 2 = i by omega, show ¬ 3 = i by omega]
  | Set operands =>
    rcases operands with ⟨a, k⟩
    simp [UnusedPosition, encode] at unused
    simp [encode, hi, vectorInit, show ¬ 0 = i by omega, show ¬ 1 = i by omega,
      show ¬ 2 = i by omega, show ¬ 3 = i by omega, show ¬ 4 = i by omega]
  | Deref operands =>
    rcases operands with ⟨a, b, c, mode⟩
    simp [UnusedPosition, encode] at unused
    simp [encode, hi, vectorInit, show ¬ 0 = i by omega, show ¬ 1 = i by omega,
      show ¬ 2 = i by omega, show ¬ 3 = i by omega, show ¬ 4 = i by omega, show ¬ 5 = i by omega]
  | Jump operands =>
    rcases operands with ⟨a, b, c⟩
    simp [UnusedPosition, encode] at unused
    simp [encode, hi, vectorInit, show ¬ 0 = i by omega, show ¬ 1 = i by omega,
      show ¬ 2 = i by omega, show ¬ 3 = i by omega]
  | Blake2s operands =>
    rcases operands with ⟨a, b, c, d, cv, out, md⟩
    simp [UnusedPosition, encode] at unused

theorem decode_nonzero_unused (row : Vector (BitVec 64) 8) (i : Nat) (hi : i < 8)
    (unused : UnusedPosition row i) (nonzero : row[i]! ≠ 0) : decode row = none := by
  cases accepted : decode row with
  | none => rfl
  | some ins =>
    have same := encode_of_decode accepted
    have zero := encode_unused_zero ins i hi (by simpa only [same] using unused)
    exact False.elim (nonzero (by simpa only [same] using zero))

end Leanisa.Proofs

#print axioms Leanisa.Proofs.decode_encode
#print axioms Leanisa.Proofs.encode_of_decode
#print axioms Leanisa.Proofs.encode_injective
#print axioms Leanisa.Proofs.canonical_iff_accepted
#print axioms Leanisa.Proofs.decode_unknown_opcode
#print axioms Leanisa.Proofs.decode_invalid_deref_flags
#print axioms Leanisa.Proofs.decode_nonzero_unused
