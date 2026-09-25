/-
Constructs supported finite address domains from the fixed generator order.
Concrete policy operand mappings and all observation, completion, and
resolution premises remain explicit.
-/
import GeneratorOrder

noncomputable section
open Leanisa.Proofs Leanisa.Proofs.Quotient Leanisa.Functions
namespace Leanisa.Proofs.Supported

theorem supported_domain (n : Nat) (bound : n ≤ 2^32) : GPowerDomain n := by
  refine ⟨gAddress_origin, ?_, ?_⟩
  · intro i hi
    exact gAddress_successor i (by omega)
  · intro i j equal
    have mapped := congrArg toK equal
    rw [toK_gAddress i.val (by omega), toK_gAddress j.val (by omega)] at mapped
    have hi : i.val < orderOf (AdjoinRoot.root modulus) := by
      have h := root_order_gt_two_pow_32
      omega
    have hj : j.val < orderOf (AdjoinRoot.root modulus) := by
      have h := root_order_gt_two_pow_32
      omega
    apply Fin.ext
    exact pow_injOn_Iio_orderOf hi hj mapped

theorem supported_nonzero (i : Nat) (bound : i < 2^32) : gAddress i ≠ 0#64 := by
  intro zero
  have mapped := congrArg toK zero
  rw [toK_gAddress i (by omega), toK_zero] at mapped
  have complement : i + (18446744073709551615 - i) = 18446744073709551615 := by omega
  have period := root_period
  rw [← complement, pow_add, mapped, zero_mul] at period
  have words : (0#64) = 1#64 := toK_injective (by rw [toK_zero, toK_one]; exact period)
  exact (by decide : (0#64) ≠ 1#64) words

theorem supported_read {n : Nat} (mem : Vector Word n) (bound : n ≤ 2^32) (i : Fin n) :
    read_memory mem (gAddress i.val) = ⟨mem.get i, true⟩ :=
  read_memory_gAddress mem (supported_domain n bound) i

theorem supported_fetch {n : Nat} (program : Vector Leanisa.instruction n)
    (bound : n ≤ 2^32) (i : Fin n) :
    fetch program (gAddress i.val) = some (program.get i) :=
  fetch_gAddress program (supported_domain n bound) i

end Leanisa.Proofs.Supported

