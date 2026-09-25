import ExtensionMultiplication

/-
Directed kernel checks for exact Sail extension arithmetic and representation.
Basis and omitted-term witnesses exercise the included extension proofs.
Local recursion limits accommodate the fixed nine base products, each with
exactly 64 actual loop iterations.
-/

noncomputable section
open Leanisa.Proofs.Extension
namespace Leanisa.Proofs.ExtensionChecks

def e0 : BitVec 192 := pack (1#64) (0#64) (0#64)
def e1 : BitVec 192 := pack (0#64) (1#64) (0#64)
def e2 : BitVec 192 := pack (0#64) (0#64) (1#64)

set_option maxRecDepth 20000 in
theorem basis_one_high : Leanisa.Functions.emul e0 e2 = e2 := by decide +kernel

set_option maxRecDepth 20000 in
theorem basis_middle_high : Leanisa.Functions.emul e1 e2 = pack (1#64) (1#64) (0#64) := by decide +kernel

set_option maxRecDepth 20000 in
theorem basis_high_high : Leanisa.Functions.emul e2 e2 = pack (0#64) (1#64) (1#64) := by decide +kernel

set_option maxRecDepth 20000 in
theorem high_carry_product :
    Leanisa.Functions.emul (pack (0#64) (0#64) (0x8000000000000000#64)) (pack (0#64) (0#64) (2#64)) =
      pack (0#64) (0x1b#64) (0x1b#64) := by decide +kernel

set_option maxRecDepth 20000 in
theorem mixed_product :
    Leanisa.Functions.emul (pack (1#64) (2#64) (3#64)) (pack (4#64) (5#64) (6#64)) =
      pack (7#64) (4#64) (10#64) := by decide +kernel

theorem omitted_p3_low_counterexample : Leanisa.Functions.emul e1 e2 ≠ pack (0#64) (1#64) (0#64) := by
  rw [basis_middle_high]
  decide

theorem omitted_p3_middle_counterexample : Leanisa.Functions.emul e1 e2 ≠ pack (1#64) (0#64) (0#64) := by
  rw [basis_middle_high]
  decide

theorem omitted_p4_middle_counterexample : Leanisa.Functions.emul e2 e2 ≠ pack (0#64) (0#64) (1#64) := by
  rw [basis_high_high]
  decide

theorem omitted_p4_high_counterexample : Leanisa.Functions.emul e2 e2 ≠ pack (0#64) (1#64) (0#64) := by
  rw [basis_high_high]
  decide

theorem bit_63_packing : (0x8000000000000000#192) =
    pack (0x8000000000000000#64) (0x0#64) (0x0#64) := by decide

theorem bit_63_slices :
    limb0 (0x8000000000000000#192) = 0x8000000000000000#64 ∧
    limb1 (0x8000000000000000#192) = 0x0#64 ∧
    limb2 (0x8000000000000000#192) = 0x0#64 := by decide

theorem bit_64_packing : (0x10000000000000000#192) =
    pack (0x0#64) (0x1#64) (0x0#64) := by decide

theorem bit_64_slices :
    limb0 (0x10000000000000000#192) = 0x0#64 ∧
    limb1 (0x10000000000000000#192) = 0x1#64 ∧
    limb2 (0x10000000000000000#192) = 0x0#64 := by decide

theorem bit_127_packing : (0x80000000000000000000000000000000#192) =
    pack (0x0#64) (0x8000000000000000#64) (0x0#64) := by decide

theorem bit_127_slices :
    limb0 (0x80000000000000000000000000000000#192) = 0x0#64 ∧
    limb1 (0x80000000000000000000000000000000#192) = 0x8000000000000000#64 ∧
    limb2 (0x80000000000000000000000000000000#192) = 0x0#64 := by decide

theorem bit_128_packing : (0x100000000000000000000000000000000#192) =
    pack (0x0#64) (0x0#64) (0x1#64) := by decide

theorem bit_128_slices :
    limb0 (0x100000000000000000000000000000000#192) = 0x0#64 ∧
    limb1 (0x100000000000000000000000000000000#192) = 0x0#64 ∧
    limb2 (0x100000000000000000000000000000000#192) = 0x1#64 := by decide

theorem bit_191_packing : (0x800000000000000000000000000000000000000000000000#192) =
    pack (0x0#64) (0x0#64) (0x8000000000000000#64) := by decide

theorem bit_191_slices :
    limb0 (0x800000000000000000000000000000000000000000000000#192) = 0x0#64 ∧
    limb1 (0x800000000000000000000000000000000000000000000000#192) = 0x0#64 ∧
    limb2 (0x800000000000000000000000000000000000000000000000#192) = 0x8000000000000000#64 := by decide

theorem all_ones_slices :
    limb0 (0xffffffffffffffffffffffffffffffffffffffffffffffff#192) = 0xffffffffffffffff#64 ∧
    limb1 (0xffffffffffffffffffffffffffffffffffffffffffffffff#192) = 0xffffffffffffffff#64 ∧
    limb2 (0xffffffffffffffffffffffffffffffffffffffffffffffff#192) = 0xffffffffffffffff#64 := by
  decide

theorem coefficient_beyond_high (a : BitVec 192) (i : Nat) (hi : 3 ≤ i) :
    (wordPoly a).coeff i = 0 := by
  rw [wordPoly_coeff]
  simp [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]

set_option maxRecDepth 20000 in
theorem actual_zero_squared : Leanisa.Functions.emul (0#192) (0#192) = 0#192 := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem actual_all_ones_squared :
    Leanisa.Functions.emul (0xffffffffffffffffffffffffffffffffffffffffffffffff#192)
      (0xffffffffffffffffffffffffffffffffffffffffffffffff#192) =
      pack (0x5555555555555513#64) (0x5555555555555513#64) (0#64) := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem actual_embedded_high_carry :
    Leanisa.Functions.emul (Leanisa.Functions.embed_k (0x8000000000000000#64))
      (Leanisa.Functions.embed_k (2#64)) = Leanisa.Functions.embed_k (0x1b#64) := by
  decide +kernel

theorem actual_embed_membership (a : BitVec 64) :
    Leanisa.Functions.in_k (Leanisa.Functions.embed_k a) = true := by
  apply (in_k_embedding _).mpr
  rw [embed_packing, (unpack_pack a (0#64) (0#64)).1, ← embed_packing]

theorem middle_basis_outside_base : Leanisa.Functions.in_k e1 = false := by decide

theorem high_basis_outside_base : Leanisa.Functions.in_k e2 = false := by decide

theorem actual_embedded_product_closed (a b : BitVec 64) :
    Leanisa.Functions.in_k
      (Leanisa.Functions.emul (Leanisa.Functions.embed_k a) (Leanisa.Functions.embed_k b)) = true := by
  rw [emul_embed]
  exact actual_embed_membership _

set_option maxRecDepth 20000 in
theorem actual_mixed_high_limbs :
    Leanisa.Functions.emul (pack (0x8000000000000000#64) (0xffffffffffffffff#64) (0x123456789abcdef#64))
      (pack (0xdeadbeef#64) (0x8000000000000000#64) (0xffffffffffffffff#64)) =
      pack (0x59708c264dfa4b93#64) (0x11a8dea3ae121c98#64) (0x8361c80d3c3ea015#64) := by decide +kernel

end Leanisa.Proofs.ExtensionChecks
