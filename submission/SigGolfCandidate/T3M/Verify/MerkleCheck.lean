import SigGolfCandidate.T3M.Verify.MerkleCheckA
import SigGolfCandidate.T3M.Verify.MerkleCheckB
import SigGolfCandidate.T3M.Verify.MerkleCheckC

/-! # V3: every Merkle shape block and every compare copy, kernel-checked

`mkBlockCheck_at`: for every layer, chunk and chunk value, the table-word entry and all levels of the shape block
(`MerkleCheckA`: layers 3, 2; `MerkleCheckB`: layer 1; `MerkleCheckC`: layer 0 and the compare copies);
`mkEnt_of`, `mkLvl_of`: its parts; `cmpCheck_at`: the 64 compare copies. -/

namespace SigGolfCandidate.T3M

theorem mkBlockCheck_at (lay ci sh : Nat) (hlay : lay < 4) (hci : ci < mkNch lay) (hsh : sh < 2 ^ mkBits lay ci) :
    mkBlockCheck lay ci sh = true := by
  have hall : ∀ lo n, mkChunkCheck lay ci lo n = true → lo ≤ sh → sh < lo + n → mkBlockCheck lay ci sh = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h sh (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · have hci' : ci < 2 := by simpa [mkNch] using hci
    interval_cases ci
    · exact hall 0 64 mkChunk_00 (by omega) (by simpa [mkBits] using hsh)
    · exact hall 0 64 mkChunk_01 (by omega) (by simpa [mkBits] using hsh)
  all_goals (have hci0 : ci = 0 := by simp [mkNch] at hci; omega); subst hci0
  · have : sh < 128 := by simpa [mkBits, hL] using hsh
    by_cases h64 : sh < 64
    · exact hall 0 64 mkChunk_1a (by omega) (by omega)
    · exact hall 64 64 mkChunk_1b (by omega) (by omega)
  · exact hall 0 64 mkChunk_2 (by omega) (by simpa [mkBits, hL] using hsh)
  · exact hall 0 64 mkChunk_3 (by omega) (by simpa [mkBits, hL] using hsh)

theorem mkEnt_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) : mkEntCheck lay ci sh = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h; exact h.1

theorem mkLvl_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) (kk : Nat) (hkk : kk < mkBits lay ci) :
    mkLvlCheck lay ci sh kk = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 kk (List.mem_range.mpr hkk)


end SigGolfCandidate.T3M
