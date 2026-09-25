import EncodedDereference

noncomputable section
open Leanisa Leanisa.Proofs Leanisa.Functions Sail
namespace Leanisa.Proofs.Encoded

/-- Nine bounded effective accesses, seven ordered chunk observations, and two
compatible ordered output assignments for the actual Sail compression step. -/
theorem encoded_blake {m : Nat} (s : machine_state)
    (frame o0 o1 o2 o3 ocv oout omd : Nat)
    (i0 i1 i2 i3 ic0 ic1 io0 io1 imd : Fin m)
    (m0 m1 m2 m3 cv0 cv1 md : Word)
    {before observed intermediate after : PartialMemory m}
    (bound : m ≤ 2^32) (frameRep : s.fp = gAddress frame)
    (index0 : i0.val = frame + o0)
    (index1 : i1.val = frame + o1)
    (index2 : i2.val = frame + o2)
    (index3 : i3.val = frame + o3)
    (indexCv : ic0.val = frame + ocv) (indexCvNext : ic1.val = ic0.val + 1)
    (indexOut : io0.val = frame + oout) (indexOutNext : io1.val = io0.val + 1)
    (indexMd : imd.val = frame + omd)
    (reads : Observed before
      [(i0, m0), (i1, m1), (i2, m2), (i3, m3), (ic0, cv0), (ic1, cv1), (imd, md)] observed)
    (c0 : in_chunk m0 = true) (c1 : in_chunk m1 = true)
    (c2 : in_chunk m2 = true) (c3 : in_chunk m3 = true)
    (cc0 : in_chunk cv0 = true) (cc1 : in_chunk cv1 = true) (cmd : in_chunk md = true)
    (write0 : assign observed io0 (compressionLow m0 m1 m2 m3 cv0 cv1 md) = some intermediate)
    (write1 : assign intermediate io1 (compressionHigh m0 m1 m2 m3 cv0 cv1 md) = some after) :
    IsaStep s before (.Blake2s (gAddress o0, gAddress o1, gAddress o2,
      gAddress o3, gAddress ocv, gAddress oout, gAddress omd))
      after (advancedState s) [] := by
  exact .blake (.checked
    (gAddress o0) (gAddress o1) (gAddress o2) (gAddress o3)
    (gAddress ocv) (gAddress oout) (gAddress omd)
    i0 i1 i2 i3 ic0 ic1 io0 io1 imd m0 m1 m2 m3 cv0 cv1 md
    (encoded_access s.fp (gAddress o0) frame o0 i0 bound frameRep rfl index0)
    (encoded_access s.fp (gAddress o1) frame o1 i1 bound frameRep rfl index1)
    (encoded_access s.fp (gAddress o2) frame o2 i2 bound frameRep rfl index2)
    (encoded_access s.fp (gAddress o3) frame o3 i3 bound frameRep rfl index3)
    (encoded_access s.fp (gAddress ocv) frame ocv ic0 bound frameRep rfl indexCv)
    (encoded_adjacent s.fp (gAddress ocv) frame ocv ic0 ic1 bound frameRep rfl
      indexCv indexCvNext)
    (encoded_access s.fp (gAddress oout) frame oout io0 bound frameRep rfl indexOut)
    (encoded_adjacent s.fp (gAddress oout) frame oout io0 io1 bound frameRep rfl
      indexOut indexOutNext)
    (encoded_access s.fp (gAddress omd) frame omd imd bound frameRep rfl indexMd)
    reads c0 c1 c2 c3 cc0 cc1 cmd write0 write1)

end Leanisa.Proofs.Encoded
