import Observations

namespace Leanisa.Proofs
open Sail Leanisa.Functions

def lowChunk (v : Word) : BitVec 128 := Sail.BitVec.extractLsb v 127 0

def embedChunk (v : BitVec 128) : Word := 0#64 +++ v

@[simp] theorem lowChunk_embedChunk (v : BitVec 128) : lowChunk (embedChunk v) = v := by
  exact BitVec.extractLsb'_append_eq_right

@[simp] theorem in_chunk_embedChunk (v : BitVec 128) : in_chunk (embedChunk v) = true := by
  simp only [in_chunk, embedChunk, Sail.BitVec.extractLsb, beq_iff_eq]
  exact BitVec.extractLsb'_append_eq_left

/-- The actual extracted compression function and the ISA's chunk order.
No separate cryptographic reference or Rust refinement is assumed here. -/
def compressionResult (m0 m1 m2 m3 cv0 cv1 md : Word) : BitVec 256 :=
  blake_compress
    (lowChunk m3 +++ (lowChunk m2 +++ (lowChunk m1 +++ lowChunk m0)))
    (lowChunk cv1 +++ lowChunk cv0) (lowChunk md)

def compressionLow (m0 m1 m2 m3 cv0 cv1 md : Word) : Word :=
  embedChunk (Sail.BitVec.extractLsb (compressionResult m0 m1 m2 m3 cv0 cv1 md) 127 0)

def compressionHigh (m0 m1 m2 m3 cv0 cv1 md : Word) : Word :=
  embedChunk (Sail.BitVec.extractLsb (compressionResult m0 m1 m2 m3 cv0 cv1 md) 255 128)

theorem step_blake_of_reads {n : Nat} (mem : Vector Word n) (s : machine_state)
    (o0 o1 o2 o3 ocv oout omd : BitVec 64) (m0 m1 m2 m3 cv0 cv1 md : Word)
    (r0 : read_memory mem (kmul s.fp o0) = ⟨m0, true⟩)
    (r1 : read_memory mem (kmul s.fp o1) = ⟨m1, true⟩)
    (r2 : read_memory mem (kmul s.fp o2) = ⟨m2, true⟩)
    (r3 : read_memory mem (kmul s.fp o3) = ⟨m3, true⟩)
    (rc0 : read_memory mem (kmul s.fp ocv) = ⟨cv0, true⟩)
    (rc1 : read_memory mem (advance (kmul s.fp ocv)) = ⟨cv1, true⟩)
    (ro0 : read_memory mem (kmul s.fp oout) =
      ⟨compressionLow m0 m1 m2 m3 cv0 cv1 md, true⟩)
    (ro1 : read_memory mem (advance (kmul s.fp oout)) =
      ⟨compressionHigh m0 m1 m2 m3 cv0 cv1 md, true⟩)
    (rmd : read_memory mem (kmul s.fp omd) = ⟨md, true⟩)
    (c0 : in_chunk m0 = true) (c1 : in_chunk m1 = true)
    (c2 : in_chunk m2 = true) (c3 : in_chunk m3 = true)
    (cc0 : in_chunk cv0 = true) (cc1 : in_chunk cv1 = true) (cmd : in_chunk md = true) :
    step s (.Blake2s (o0, o1, o2, o3, ocv, oout, omd)) mem =
      ⟨advancedState s, .Running⟩ := by
  simp only [step, step_indexed, read_memory_indexed_empty, r0, r1, r2, r3,
    rc0, rc1, ro0, ro1, rmd]
  have chunk (v : BitVec 128) : Sail.BitVec.extractLsb (embedChunk v) 127 0 = v :=
    lowChunk_embedChunk v
  simp only [compressionLow, compressionHigh, chunk,
    in_chunk_embedChunk, c0, c1, c2, c3, cc0, cc1, cmd]
  simp [compressionResult, lowChunk, advancedState,
    show (status.Running == status.Running) = true from rfl]

/-- All seven input chunks are observed before two compatible output writes.
Repeated indices, including input/output aliases, require consistent values. -/
inductive BlakeStep {m : Nat} (s : machine_state) :
    PartialMemory m → instruction → PartialMemory m → Prop where
  | checked {before observed intermediate after}
      (o0 o1 o2 o3 ocv oout omd : BitVec 64)
      (i0 i1 i2 i3 ic0 ic1 io0 io1 imd : Fin m) (m0 m1 m2 m3 cv0 cv1 md : Word)
      (maps0 : kmul s.fp o0 = gAddress i0.val)
      (maps1 : kmul s.fp o1 = gAddress i1.val)
      (maps2 : kmul s.fp o2 = gAddress i2.val)
      (maps3 : kmul s.fp o3 = gAddress i3.val)
      (mapsc0 : kmul s.fp ocv = gAddress ic0.val)
      (mapsc1 : advance (kmul s.fp ocv) = gAddress ic1.val)
      (mapso0 : kmul s.fp oout = gAddress io0.val)
      (mapso1 : advance (kmul s.fp oout) = gAddress io1.val)
      (mapsmd : kmul s.fp omd = gAddress imd.val)
      (reads : Observed before
        [(i0, m0), (i1, m1), (i2, m2), (i3, m3), (ic0, cv0), (ic1, cv1), (imd, md)] observed)
      (c0 : in_chunk m0 = true) (c1 : in_chunk m1 = true)
      (c2 : in_chunk m2 = true) (c3 : in_chunk m3 = true)
      (cc0 : in_chunk cv0 = true) (cc1 : in_chunk cv1 = true) (cmd : in_chunk md = true)
      (write0 : assign observed io0 (compressionLow m0 m1 m2 m3 cv0 cv1 md) = some intermediate)
      (write1 : assign intermediate io1 (compressionHigh m0 m1 m2 m3 cv0 cv1 md) = some after) :
      BlakeStep s before (.Blake2s (o0, o1, o2, o3, ocv, oout, omd)) after

theorem BlakeStep.evolves {m : Nat} {s : machine_state}
    {before after : PartialMemory m} {ins}
    (operation : BlakeStep s before ins after) : Evolves before after := by
  cases operation with
  | checked o0 o1 o2 o3 ocv oout omd i0 i1 i2 i3 ic0 ic1 io0 io1 imd
      m0 m1 m2 m3 cv0 cv1 md maps0 maps1 maps2 maps3 mapsc0 mapsc1 mapso0 mapso1 mapsmd
      reads c0 c1 c2 c3 cc0 cc1 cmd write0 write1 =>
    exact .trans reads.evolves (.trans (.assignment io0 _ write0) (.assignment io1 _ write1))

theorem BlakeStep.simulates {m : Nat} (mem : Vector Word m) (domain : GPowerDomain m)
    {s : machine_state} {before after later : PartialMemory m} {ins}
    (operation : BlakeStep s before ins after) (continuation : Evolves after later)
    (finished : Completes later (vectorImage mem)) :
    step s ins mem = ⟨advancedState s, .Running⟩ := by
  cases operation with
  | checked o0 o1 o2 o3 ocv oout omd i0 i1 i2 i3 ic0 ic1 io0 io1 imd
      m0 m1 m2 m3 cv0 cv1 md maps0 maps1 maps2 maps3 mapsc0 mapsc1 mapso0 mapso1 mapsmd
      reads c0 c1 c2 c3 cc0 cc1 cmd write0 write1 =>
    have tail := Evolves.trans (.assignment io1 _ write1) continuation
    have allWrites := Evolves.trans (.assignment io0 _ write0) tail
    apply step_blake_of_reads mem s o0 o1 o2 o3 ocv oout omd m0 m1 m2 m3 cv0 cv1 md
    · exact reads.lookup mem domain allWrites finished i0 m0 (by simp) _ maps0
    · exact reads.lookup mem domain allWrites finished i1 m1 (by simp) _ maps1
    · exact reads.lookup mem domain allWrites finished i2 m2 (by simp) _ maps2
    · exact reads.lookup mem domain allWrites finished i3 m3 (by simp) _ maps3
    · exact reads.lookup mem domain allWrites finished ic0 cv0 (by simp) _ mapsc0
    · exact reads.lookup mem domain allWrites finished ic1 cv1 (by simp) _ mapsc1
    · exact completed_cell_lookup mem domain finished io0 _
        (execution_extends tail _ _ (assign_fixes_value write0)) _ mapso0
    · exact completed_cell_lookup mem domain finished io1 _
        (execution_extends continuation _ _ (assign_fixes_value write1)) _ mapso1
    · exact reads.lookup mem domain allWrites finished imd md (by simp) _ mapsmd
    · exact c0
    · exact c1
    · exact c2
    · exact c3
    · exact cc0
    · exact cc1
    · exact cmd

end Leanisa.Proofs

#print axioms Leanisa.Proofs.BlakeStep.simulates
