import Encoding

/-! Kernel-checked uses of the canonicality interface for deliberately malformed
raw rows. The fields not constrained below remain arbitrary. -/
namespace Leanisa.Proofs.EncodingChecks
open Leanisa.Functions

theorem both_deref_flags_rejected (row : Vector (BitVec 64) 8)
    (opcode : row[0]! = 8) (pcFlag : row[4]! = 1) (fpFlag : row[5]! = 1) :
    decode row = none := by
  apply decode_invalid_deref_flags row opcode
  simp_all [ValidDerefFlags]

theorem nonboolean_pc_flag_rejected (row : Vector (BitVec 64) 8)
    (opcode : row[0]! = 8) (nonzero : row[4]! ≠ 0) (nonone : row[4]! ≠ 1) :
    decode row = none := by
  apply decode_invalid_deref_flags row opcode
  simp_all [ValidDerefFlags]

theorem nonboolean_fp_flag_rejected (row : Vector (BitVec 64) 8)
    (opcode : row[0]! = 8) (nonzero : row[5]! ≠ 0) (nonone : row[5]! ≠ 1) :
    decode row = none := by
  apply decode_invalid_deref_flags row opcode
  simp_all [ValidDerefFlags]

theorem final_unused_set_word_rejected (row : Vector (BitVec 64) 8)
    (opcode : row[0]! = 4) (nonzero : row[7]! ≠ 0) : decode row = none := by
  apply decode_nonzero_unused row 7 (by decide) _ nonzero
  simp_all [UnusedPosition]

theorem combined_opcode_rejected (row : Vector (BitVec 64) 8)
    (opcode : row[0]! = 3) : decode row = none := by
  apply decode_unknown_opcode row
  simp_all [SupportedOpcode]

/-- No part of a SET immediate can be discarded by canonical encoding. -/
theorem set_immediate_preserved (offset : BitVec 64) (first second : BitVec 192)
    (encodedSame : encode (.Set (offset, first)) = encode (.Set (offset, second))) :
    first = second := by
  have instructionSame := encode_injective encodedSame
  cases instructionSame
  rfl

end Leanisa.Proofs.EncodingChecks

#print axioms Leanisa.Proofs.EncodingChecks.both_deref_flags_rejected
#print axioms Leanisa.Proofs.EncodingChecks.nonboolean_pc_flag_rejected
#print axioms Leanisa.Proofs.EncodingChecks.nonboolean_fp_flag_rejected
#print axioms Leanisa.Proofs.EncodingChecks.final_unused_set_word_rejected
#print axioms Leanisa.Proofs.EncodingChecks.combined_opcode_rejected
#print axioms Leanisa.Proofs.EncodingChecks.set_immediate_preserved
