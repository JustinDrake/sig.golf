import SigGolfCandidate.T3M.FullCache.MacPass
import SigGolfCandidate.T3M.Bytes

namespace SigGolfCandidate.T3M.FullCache.MacPass
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)

theorem readWords_getD (t : MachineState) : ∀ (n a i : Nat), i < n →
    (t.readWords (BitVec.ofNat 64 a) n).getD i 0 = t.getMem (BitVec.ofNat 64 (a + 8 * i))
  | 0, _, _, h => by omega
  | n + 1, a, i, h => by
      have e : BitVec.ofNat 64 a + 8 = BitVec.ofNat 64 (a + 8) := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [MachineState.readWords_succ, e]
      cases i with
      | zero => simp
      | succ i =>
        rw [List.getD_cons_succ, readWords_getD t n (a + 8) i (by omega)]
        congr 2; omega

/-- Doublewords that spell a byte list: their 32-bit chunks are the list's. -/
theorem chunksOf_of_wordsToNat : ∀ (n : Nat) (R : List Word) (l : List UInt8), R.length = n →
    l.length = 8 * n → wordsToNat R = T3.readLE l → chunksOf (R.map BitVec.toNat) = chunks32 l
  | 0, R, l, hR, hl, _ => by
      rw [List.length_eq_zero_iff.mp hR, List.length_eq_zero_iff.mp (by omega : l.length = 0)]
      rfl
  | n + 1, R, l, hR, hl, h => by
      obtain ⟨w, R', rfl⟩ : ∃ w R', R = w :: R' := by
        cases R with
        | nil => simp at hR
        | cons w R' => exact ⟨w, R', rfl⟩
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, l', rfl⟩ :
          ∃ b0 b1 b2 b3 b4 b5 b6 b7 l', l = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l' := by
        match l, hl with
        | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l', _ => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        | [], h => simp at h <;> omega
        | [_], h => simp at h <;> omega
        | [_, _], h => simp at h <;> omega
        | [_, _, _], h => simp at h <;> omega
        | [_, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _, _, _], h => simp at h <;> omega
      simp only [List.length_cons] at hR hl
      have hw := w.isLt
      have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
      have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
      simp only [wordsToNat, T3M.readLE_cons] at h
      have hsplit : w.toNat = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat +
          256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) ∧
          wordsToNat R' = T3.readLE l' := by
        constructor <;> omega
      have ih := chunksOf_of_wordsToNat n R' l' (by omega) (by omega) hsplit.2
      simp only [List.map_cons, chunksOf, List.flatMap_cons, List.cons_append, List.nil_append, chunks32]
      rw [show List.flatMap (fun w => [w % 2 ^ 32, w / 2 ^ 32]) (List.map BitVec.toNat R') =
        chunksOf (R'.map BitVec.toNat) from rfl, ih]
      congr 1
      · rw [hsplit.1]; omega
      · congr 1
        rw [hsplit.1]; omega

/-- **One pass over the region**, given as bytes. -/
theorem mac_pass_region {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat) (region : List UInt8)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0xA0000)
    (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 0x80020) 16380) = T3.readLE region) :
    ∃ u, Steps image s 425894 622454 u ∧ u.pc = pc + 160 ∧
      u.getReg .x14 =
        BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) (chunks32 region)) +
          s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 →
        u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hR := readWords_length s (BitVec.ofNat 64 0x80020) 16380
  have hch := chunksOf_of_wordsToNat 16380 _ region hR (by rw [hlen]) hreg
  have := mac_pass hc s hpc B ((s.readWords (BitVec.ofNat 64 0x80020) 16380).map BitVec.toNat) h22 hB hB' h18
    h19 (by rw [List.length_map, hR]) (fun i hi => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, ← readWords_getD s 16380 0x80020 i hi,
        List.getD_eq_getElem?_getD]
      cases h : (s.readWords (BitVec.ofNat 64 0x80020) 16380)[i]? with
      | none =>
        exfalso
        rw [List.getElem?_eq_none_iff, hR] at h
        omega
      | some w => rfl)
  rwa [hch] at this


end SigGolfCandidate.T3M.FullCache.MacPass
