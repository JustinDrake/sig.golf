import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ChainCode
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (regionBytes merkleBytes chainBytes leafBytes regionBytes_length region_merkle region_chain
  region_prefix region_leaf merkleBytes_window chainBytes_window leafBytes_window_zero leafBytes_window_succ)
set_option linter.unusedSimpArgs false
theorem wordsOf_getD (L : List UInt8) (m : Nat) (hL : L.length = 8 * m) (i : Nat) (hi : i < m) :
    (wordsOf L).getD i 0 = BitVec.ofNat 64 (readLE (window L (8 * i) 8)) := by
  rw [wordsOf_eq_range m L hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hw : readLE (window L (8 * i) 8) < 2 ^ 64 := by
    have := readLE_lt (window L (8 * i) 8)
    have hl : (window L (8 * i) 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L (8 * i) 8) < 256 ^ (window L (8 * i) 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hw, show 2 ^ (64 * i) = 256 ^ (8 * i) by rw [pow_mul, pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop, show 2 ^ 64 = 256 ^ 8 by norm_num, SigGolfCandidate.T3M.readLE_take]
  rfl
theorem window_split16 (L : List UInt8) (o : Nat) (h : o + 16 ≤ L.length) :
    readLE (window L o 16) = readLE (window L o 8) + 2 ^ 64 * readLE (window L (o + 8) 8) := by
  unfold window
  rw [show (L.drop o).take 16 = (L.drop o).take 8 ++ (L.drop (o + 8)).take 8 by
      rw [show 16 = 8 + 8 from rfl, List.take_add, List.drop_drop, Nat.add_comm]]
  rw [SigGolfCandidate.T3M.readLE_append, List.length_take, Nat.min_eq_left (by simp; omega)]
  norm_num
theorem words_of_window16 (L : List UInt8) (hL : L.length = 1024) (o : Nat) (ho : o % 8 = 0) (ho' : o + 16 ≤ 1024)
    (d : Digest) (hd : window L o 16 = bytesLE 16 d) :
    (wordsOf L).getD (o / 8) 0 = d.extractLsb' 0 64 ∧ (wordsOf L).getD (o / 8 + 1) 0 = d.extractLsb' 64 64 := by
  have h1 := wordsOf_getD L 128 (by omega) (o / 8) (by omega)
  have h2 := wordsOf_getD L 128 (by omega) (o / 8 + 1) (by omega)
  rw [show 8 * (o / 8) = o by omega] at h1
  rw [show 8 * (o / 8 + 1) = o + 8 by omega] at h2
  have hs := window_split16 L o (by omega)
  rw [hd, SigGolfCandidate.T3M.readLE_bytesLE] at hs
  have hlo : readLE (window L o 8) < 2 ^ 64 := by
    have := readLE_lt (window L o 8)
    have hl : (window L o 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L o 8) < 256 ^ (window L o 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    have := d.isLt
    omega
section windows
variable (c : Nat) (op : WCT9.Opening)
theorem win_chainVal (t : Fin 7) : window (regionBytes c op) (offC t.val + 48) 16 = bytesLE 16 (op.values t) := by
  rcases t with ⟨_ | i, ht⟩
  · rw [show offC 0 + 48 = 880 by rfl, region_leaf _ _ _ _ le_rfl (by omega), Nat.sub_self, leafBytes_window_zero]
    rfl
  · have hi : i < 6 := by omega
    rw [show offC (i + 1) + 48 = 448 + (64 * (5 - i) + 48) by unfold offC; omega,
      region_chain _ _ _ _ (by omega) (by omega),
      show 448 + (64 * (5 - i) + 48) - 448 = 64 * (5 - (⟨i, hi⟩ : Fin 6).val) + 48 by simp,
      chainBytes_window _ _ _ (by omega), window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
    rfl
theorem win_leafSlot (t : Fin 7) : window (regionBytes c op) (slotC t.val) 16 = bytesLE 16 (op.values t) := by
  rcases t with ⟨_ | i, ht⟩
  · exact win_chainVal c op ⟨0, ht⟩
  · have hi : i < 6 := by omega
    rw [show slotC (i + 1) = 880 + (32 + 16 * i) by unfold slotC; simp; omega,
      region_leaf _ _ _ _ (by omega) (by omega),
      show 880 + (32 + 16 * i) - 880 = 32 + 16 * (⟨i, hi⟩ : Fin 6).val by simp, leafBytes_window_succ]
    rfl
theorem win_chainPad (t : Nat) (ht : t < 7) (o : Nat) (ho : o = 0 ∨ o = 16 ∨ o = 32) :
    window (regionBytes c op) (offC t + o) 16 = zeros 16 := by
  rcases t with _ | i
  · rw [show offC 0 + o = 832 + o by rfl, region_prefix _ _ _ _ (by omega) (by omega)]
  · have hi : i < 6 := by omega
    rw [show offC (i + 1) + o = 448 + (64 * (5 - i) + o) by unfold offC; omega,
      region_chain _ _ _ _ (by omega) (by omega),
      show 448 + (64 * (5 - i) + o) - 448 = 64 * (5 - (⟨i, hi⟩ : Fin 6).val) + o by simp,
      chainBytes_window _ _ _ (by omega), window_append_left _ _ _ _ (by simp [zeros]; omega),
      window_zeros _ _ _ (by omega)]
theorem win_sib (l : Fin 7) :
    window (regionBytes c op) (64 * (6 - l.val) + 48 * (1 - c / 2 ^ l.val % 2)) 16 = bytesLE 16 (op.path l) := by
  have hl := l.isLt
  have hb : c / 2 ^ l.val % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [region_merkle _ _ _ _ (by omega), merkleBytes_window _ _ _ _ (by omega)]
  split
  · rename_i h; rw [h, show 48 * (1 - 1) = 0 by rfl, window_append_left _ _ _ _ (by simp [bytesLE_length]),
      window_full _ _ (bytesLE_length _ _)]
  · rename_i h
    rw [show 48 * (1 - c / 2 ^ l.val % 2) = 48 by omega, window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
theorem win_mpad (l : Fin 7) : window (regionBytes c op) (64 * (6 - l.val) + 32) 16 = zeros 16 := by
  have hl := l.isLt
  rw [region_merkle _ _ _ _ (by omega), merkleBytes_window _ _ _ _ (by omega)]
  split
  · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length])]
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]), window_zeros _ _ _ (by omega)]
end windows
theorem zeros16 : zeros 16 = bytesLE 16 (0 : Digest) := (Verify.bytesLE16_zero).symm
theorem placed_digAt {N : HashOutput} {sig : WCT9.Signature} {s : MachineState} (hp : Placed N sig s) (k : Nat)
    (hk : k < 9) (o : Nat) (ho : o % 8 = 0) (ho' : o + 16 ≤ 1024) (d : Digest)
    (hd : window (regionBytes (WCT9.child N ⟨k, hk⟩).val (sig.openings ⟨k, hk⟩)) o 16 = bytesLE 16 d) :
    DigAt s (regBase k + o) d := by
  have hw := words_of_window16 _ (regionBytes_length _ _) o ho ho' d hd
  have hk' : (⟨k % 9, Nat.mod_lt _ (by decide)⟩ : WCT9.Coord) = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
  constructor
  · rw [show regBase k + o = regBase k + 8 * (o / 8) by omega, hp k (o / 8) hk (by omega), regionWord, hk']
    exact hw.1
  · rw [show regBase k + o + 8 = regBase k + 8 * (o / 8 + 1) by omega, hp k (o / 8 + 1) hk (by omega), regionWord, hk']
    exact hw.2
end ClaudeWCT.W9.Machine.Expand
