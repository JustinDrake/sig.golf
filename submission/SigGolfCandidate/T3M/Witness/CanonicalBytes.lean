import SigGolfCandidate.T3M.Witness.Roundtrip

/-! Byte rewriting for a digest-derived authentication schedule. These lemmas
establish frame properties for the witness adapter; no certificate is claimed.
-/
namespace SigGolfCandidate.T3M.CanonicalBytes
open SigGolfCandidate.T3

def patchList (w : WBytes) (replacement : Nat → Option UInt8) : List UInt8 :=
  (List.range 25240).map fun i => (replacement i).getD (wbyte w i)

def patch (w : WBytes) (replacement : Nat → Option UInt8) : WBytes :=
  BitVec.ofNat (8*25240) (readLE (patchList w replacement))

theorem byte_of_list (L : List UInt8) (hl : L.length≤25240) (i : Nat) :
    (wbyte (BitVec.ofNat (8*25240) (readLE L)) i).toNat = (L.getD i 0).toNat := by
  unfold wbyte
  have he := extract_readLE L 25240 hl i 1
  change (UInt8.ofBitVec ((BitVec.ofNat (8*25240) (readLE L)).extractLsb' (8*i) (8*1))).toNat = _
  rw [he, UInt8.toNat_ofBitVec, BitVec.toNat_ofNat, take_one_drop]
  exact Nat.mod_eq_of_lt (L.getD i 0).toNat_lt

theorem byte_patch (w : WBytes) (replacement : Nat → Option UInt8) (i : Nat)
    (hi : i<25240) :
    wbyte (patch w replacement) i = (replacement i).getD (wbyte w i) := by
  apply UInt8.toNat.inj
  unfold patch
  rw [byte_of_list _ (by simp [patchList])]
  rw [List.getD_eq_getElem _ _ (by simpa [patchList] using hi)]
  simp only [patchList, List.getElem_map, List.getElem_range]

theorem byte_patch_frame (w : WBytes) (replacement : Nat → Option UInt8) (i : Nat)
    (hi : i<25240) (h : replacement i=none) :
    wbyte (patch w replacement) i = wbyte w i := by
  rw [byte_patch w replacement i hi, h]
  rfl

/-- Equal bytes give equal little-endian extracts, including arbitrary byte
windows. It avoids reasoning about a 201,920-bit witness as one integer. -/
theorem extract_eq_of_bytes (w v : WBytes) (off k : Nat)
    (h : ∀ j, j<k → wbyte w (off+j)=wbyte v (off+j)) :
    w.extractLsb' (8*off) (8*k) = v.extractLsb' (8*off) (8*k) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro bit hb
  have hq : bit/8<k := by omega
  have he := congrArg (fun x : UInt8 => x.toBitVec.getLsbD (bit%8)) (h (bit/8) hq)
  simp only [wbyte, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb'] at he ⊢
  have hr : bit%8<8 := Nat.mod_lt _ (by decide)
  simp only [decide_eq_true hr, decide_eq_true hb, Bool.true_and] at he ⊢
  have hp : 8*(off+bit/8)+bit%8=8*off+bit := by omega
  simpa only [hp] using he

theorem extract_patch_frame (w : WBytes) (replacement : Nat → Option UInt8)
    (off k : Nat) (hend : off+k≤25240)
    (h : ∀ j, j<k → replacement (off+j)=none) :
    (patch w replacement).extractLsb' (8*off) (8*k) = w.extractLsb' (8*off) (8*k) := by
  apply extract_eq_of_bytes
  intro j hj
  exact byte_patch_frame w replacement (off+j) (by omega) (h j hj)

theorem digest_patch_frame (w : WBytes) (replacement : Nat → Option UInt8)
    (off : Nat) (hend : off+16≤25240)
    (h : ∀ j, j<16 → replacement (off+j)=none) :
    wdig (patch w replacement) off = wdig w off := by
  exact extract_patch_frame w replacement off 16 hend h

theorem le32_patch_frame (w : WBytes) (replacement : Nat → Option UInt8)
    (off : Nat) (hend : off+4≤25240)
    (h : ∀ j, j<4 → replacement (off+j)=none) :
    wle32 (patch w replacement) off = wle32 w off := by
  exact extract_patch_frame w replacement off 4 hend h

end SigGolfCandidate.T3M.CanonicalBytes
