import SigGolfCandidate.T3M.Expand.Layer
import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3M.Expand.LayersBlocks
import SigGolfCandidate.T3M.Search.BCCounterSearch

section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chainCount height)
open SigGolfCandidate.T3M.Search (NODE NOUT ENC)
theorem rl_mk_finish {tc : MachineState} {sig : Signature} {lay : Layer} {tree leaf P WM j : Nat}
    {value : Digest} {u : MachineState} (hj : j < height lay) (hlow : lay ≠ 0) (hfinal : j + 1 = height lay) (htree : tree < 2 ^ 32) (hleaf : leaf < 2 ^ height lay)
    (hP0 : 0x7000 ≤ P) (hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hWM8 : WM % 8 = 0) (hWM : 0x800 + 64 * (height lay - 1) ≤ WM) (hWM' : WM + 64 ≤ 0x7000)
    (c5 : tc.getReg .x5 = 0) (c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val)
    (c9 : tc.getReg .x9 = BitVec.ofNat 64 tree) (c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf)
    (c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay))
    (cpath : DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j))
    (cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0) (cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (hI : MkInv tc sig lay leaf P WM j value u) (ret : Nat) (c1 : tc.getReg .x1 = pcOf ret) :
    ∃ t k, Steps image u k k t ∧ k ≤ 45 ∧ t.pc = pcOf ret ∧
      DigAt t ENC (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ∧
      DigAt t (ENC + 48) (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value) ∧
      (∀ q < height lay, DigAt t (WM - 64 * q + sideOff leaf q) (lpath sig lay q)) ∧
      RegsExcept tc t mkRegs ∧
      Frame tc t (fun A => MkW leaf WM (height lay) A ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  have hH := height_le lay
  have hlay := lay.isLt
  have hleaf' : leaf < 2 ^ 12 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) hH)
  have g : ∀ r, r ∉ mkRegs → u.getReg r = tc.getReg r := fun r h => hI.regs.get h
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1076_spec u hI.pc j (height lay) (by omega) (by omega) hI.x20
    (by rw [g _ (by decide)]; exact c15)
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ := rl1077_spec t1 p1 leaf j (by omega) (by omega)
    (by rw [r1.get (by decide), g _ (by decide)]; exact c18) (by rw [r1.get (by decide)]; exact hI.x20)
  have fu2 : Frame u t2 (fun _ => False) := (f1.trans f2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u t2 [.x28] := (r1.trans r2).mono (by decide)
  have hpu : DigAt u (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) :=
    cpath.frame hI.frame (by omega) (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
      (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
  set P' := P + 16 * chainCount lay + 16 * j with hP'def
  set M := WM - 64 * j with hMdef
  have h22 : t2.getReg .x22 = BitVec.ofNat 64 P' := by rw [ru2.get (by decide)]; exact hI.x22
  have h24 : t2.getReg .x24 = BitVec.ofNat 64 M := by rw [ru2.get (by decide)]; exact hI.x24
  have hval2 : DigAt t2 NOUT value := hI.val.frame fu2 (by decide) (by simp) (by simp)
  have hpu2 : DigAt t2 P' (lpath sig lay j) := hpu.frame fu2 (by omega) (by simp) (by simp)
  have hn32 : t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn32]
  have hn40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn40]
  obtain ⟨t3, k3, s3, hk3, p3, nl, nr, wsib, r3, f3⟩ : ∃ t3 k3, Steps image t2 k3 k3 t3 ∧ k3 ≤ 19 ∧
      t3.pc = pcOf 1117 ∧
      DigAt t3 NODE (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ∧
      DigAt t3 (NODE + 48) (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value) ∧
      DigAt t3 (M + sideOff leaf j) (lpath sig lay j) ∧
      RegsExcept t2 t3 [.x6, .x7, .x29, .x30] ∧
      Frame t2 t3 (fun A => A = M + sideOff leaf j ∨ A = M + sideOff leaf j + 8 ∨ A = NODE ∨ A = NODE + 8 ∨
        A = NODE + 48 ∨ A = NODE + 56) := by
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · rw [if_pos hb] at p2
      obtain ⟨t3, s3, p3, m48, m56, n0, n8, n48, n56, r3, f3⟩ := rl1099_spec t2 p2 P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 48 := by unfold sideOff; rw [if_neg (by omega)]
      refine ⟨t3, 18, s3, by omega, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_pos hb]; exact ⟨n0.trans hval2.1, n8.trans hval2.2⟩
      · rw [if_pos hb]; exact ⟨n48.trans hpu2.1, n56.trans hpu2.2⟩
      · rw [hso]; exact ⟨m48.trans hpu2.1, by rw [show M + 48 + 8 = M + 56 by omega]; exact m56.trans hpu2.2⟩
      · rw [hso]; exact f3
    · rw [if_neg hb] at p2
      obtain ⟨t3, s3, p3, m0, m8, n0, n8, n48, n56, r3, f3⟩ := rl1080_spec t2 p2 P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 0 := by unfold sideOff; rw [if_pos (by omega)]
      refine ⟨t3, 19, s3, le_refl _, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_neg hb]; exact ⟨n0.trans hpu2.1, n8.trans hpu2.2⟩
      · rw [if_neg hb]; exact ⟨n48.trans hval2.1, n56.trans hval2.2⟩
      · rw [hso]; exact ⟨m0.trans hpu2.1, m8.trans hpu2.2⟩
      · rw [hso]; simpa using f3
  have g3' : RegsExcept tc t3 mkRegs := ((hI.regs.trans ru2).trans r3).mono (by decide)
  have g3 : ∀ r, r ∉ mkRegs → t3.getReg r = tc.getReg r := fun r h => g3'.get h
  have hz : BCBlocks.remaining t3 = 0 := by
    rw [bc_remaining hj hH (by rw [g3 _ (by decide)]; exact c15)
      (by rw [r3.get (by decide), ru2.get (by decide)]; exact hI.x20)]
    rw [show height lay - j - 1 = 0 by omega]; rfl
  have hl : t3.getReg .x8 ≠ 0 := by
    rw [g3 _ (by decide), c8]
    intro he
    have hv := congrArg BitVec.toNat he
    change lay.val % 2 ^ 64 = 0 at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    exact hlow (Fin.ext hv)
  obtain ⟨t, st, pt, m0, m8, m48, m56, rt, ft⟩ := BCBlocks.finish_spec t3 p3 ret hz hl
    (by rw [g3 _ (by decide)]; exact c1)
  refine ⟨t, 1 + 3 + k3 + 18, ((s1.trans s2).trans s3).trans st, by omega, pt,
    ⟨m0.trans nl.1, m8.trans nl.2⟩, ⟨m48.trans nr.1, m56.trans nr.2⟩, ?_, ?_, ?_⟩
  · intro q hq
    have hs := sideOff_le leaf q
    by_cases he : q = j
    · subst q
      exact wsib.frame ft (by omega) (by simp only [BCBlocks.ENC]; omega) (by simp only [BCBlocks.ENC]; omega)
    · have hqj : q < j := by omega
      have hw := hI.wit q hqj
      have hs2 := sideOff_le leaf j
      have hne : WM - 64 * q + sideOff leaf q + 16 ≤ M + sideOff leaf j ∨ M + 64 ≤ WM - 64 * q + sideOff leaf q := by
        unfold sideOff at hs hs2 ⊢; split_ifs <;> omega
      exact ((hw.frame fu2 (by omega) (by simp) (by simp)).frame f3 (by omega)
        (by simp only [NODE]; omega) (by simp only [NODE]; omega)).frame ft (by omega)
        (by simp only [BCBlocks.ENC]; omega) (by simp only [BCBlocks.ENC]; omega)
  · exact (g3'.trans rt).mono (by decide)
  · have fall := ((hI.frame.trans fu2).trans f3).trans ft
    refine fall.mono (fun A hA h => ?_)
    rcases h with ((h | h) | h) | h
    · left
      unfold MkW at h ⊢
      rcases h with h | h | h | h | h | h | h | ⟨q, hq, hqv⟩
      all_goals first | omega | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, by omega, hqv⟩)))))))
    · exact h.elim
    · left
      unfold MkW
      rcases h with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj, Or.inl h⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj, Or.inr h⟩))))))
      all_goals omega
    · exact Or.inr h
end SigGolfCandidate.T3M.Expand
end

section


namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chain chainInput shortHash pad64 zero16 header chainCount height
  width maxDigit route recoverLayer leafHash nodeHash)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option maxHeartbeats 2000000
def RlPairPost (s0 : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat)
    (pair : Digest × Digest) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t ENC pair.1 ∧ DigAt t (ENC + 48) pair.2 ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval sig lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath sig lay j)) ∧
    RegsExcept s0 t rlRegs ∧
    Frame s0 t (fun A => (RlScratch A ∨ RlWit lay (route index lay).1 WC WM A) ∨ A = ENC + 48 ∨ A = ENC + 56)
theorem recoverLayerPair_eq (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    WCT9.recoverLayerPair sig index lay digits =
      ((List.finRange (chainCount lay)).mapM fun i => chain lay (route index lay).2 (route index lay).1 i.val
        (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i)) >>=
      fun ends => leafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
        (List.finRange (height lay - 1)).foldlM (fun value j => do
          let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
          let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
          nodeHash 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
            pair.1 pair.2) value >>= fun top =>
          pure (if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0 then
            (top, (sig.layers lay).path (WCT9.topLevel lay)) else
            ((sig.layers lay).path (WCT9.topLevel lay), top)) := rfl
theorem recoverLayerPair_tbsim {sk : BitVec 256} {s0 : MachineState} {wsig : WCT9.Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 (WCT9.toT3Signature wsig) index lay digits P WC WM ret) (hlow : lay ≠ 0) :
    TBSim image sk s0 (rlCost lay) (WCT9.recoverLayerPair wsig index lay digits)
      (RlPairPost s0 (WCT9.toT3Signature wsig) index lay WC WM ret) := by
  let sig := WCT9.toT3Signature wsig
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hpre.hidx
  have hleaf : leaf < 2 ^ height lay := route_lt index lay
  have hH := height_le lay
  have hleaf32 : leaf < 2 ^ 32 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hN := chainCount_cases' lay
  have hlay := lay.isLt
  have hPb := hpre.hP'
  have hWC := hpre.hWC
  have hWMC := hpre.hWMC
  have hWM := hpre.hWM
  have hP0 := hpre.hP
  obtain ⟨t1, st1, p1, x19, c24, l24, l16, r1, f1⟩ := rl997_spec s0 hpre.pc lay.val tree leaf htree hpre.x8 hpre.x9
    hpre.x18
  have f1g : ∀ A, A < 2 ^ 64 → A ≠ CHAIN + 24 → A ≠ LEAFPK + 16 → A ≠ LEAFPK + 24 →
      t1.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 h3 => f1.get hA (by rintro (h | h | h) <;> contradiction)
  have hI0 : ChainsInv t1 lay tree leaf P WC (chainCount lay) (csN4 lay) (lval sig lay) [] t1 := by
    refine ⟨p1, ⟨?_, ?_, ?_, ?_, x19, ?_, ?_, ?_, ?_⟩, ?_, fun j hj => absurd hj (by simp), fun j hj => absurd hj (by simp),
      RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [r1.get (by decide), hpre.x5]
    · rw [r1.get (by decide), hpre.x8]
    · rw [r1.get (by decide), hpre.x9]
    · rw [r1.get (by decide), hpre.x18]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide), hpre.c0]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide), hpre.c8]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide), hpre.c32]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide), hpre.c40]
    · rw [r1.get (by decide), hpre.x23]; simp
  rw [recoverLayerPair_eq]
  refine (TBSim.steps st1 (TBSim.bind (W₂ := 10 + 8 * leafBlocks' lay + 13 + height lay * 60)
    (rl_chains (sk := sk) hpre r1 f1 hI0) (fun ends u hu => ?_))).mono (by unfold rlCost; omega) (fun _ _ h => h)
  obtain ⟨hlen, hC⟩ := hu
  have hN58 : chainCount lay ≤ 58 := by omega
  obtain ⟨v1, sv1, pv1, rv1, fv1⟩ := rl1010_spec u hC.pc (chainCount lay) (chainCount lay) (by omega) (by omega)
    (by rw [hC.ctx.x19, hlen]) (by rw [hC.regs.get (by decide), r1.get (by decide)]; exact hpre.x26)
  rw [if_pos (le_refl _)] at pv1
  obtain ⟨v2, sv2, pv2, h10, h11, h12, rv2, fv2⟩ := rl1063_spec v1 pv1 (chainCount lay) (by omega)
    (by rw [rv1.get (by decide), hC.regs.get (by decide), r1.get (by decide)]; exact hpre.x26)
  have fu2 : Frame u v2 (fun _ => False) := (fv1.trans fv2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u v2 [.x6, .x10, .x11, .x12] := (rv1.trans rv2).mono (by decide)
  have fs2 : Frame s0 v2 (fun A => ((A = CHAIN + 24 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨ ChW WC ends.length A) ∨
      False) := (f1.trans hC.frame).trans fu2
  have hfar : ∀ A, A < 2 ^ 64 → (A = LEAFPK + 880 ∨ A = LEAFPK + 888) →
      v2.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA hA'
    refine fs2.get hA ?_
    rintro ((h | h) | h)
    · simp only [CHAIN, LEAFPK] at h hA'; omega
    · exact not_ChW_hdr (by simp only [LEAFPK]; omega) (Or.inr (Or.inr hA')) (by omega) h
    · exact h
  have hhd16 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = BitVec.ofNat 64 (513 + 65536 * lay.val) := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inl rfl) (by omega)), l16]
  have hhd24 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = BitVec.ofNat 64 (tree + 2 ^ 32 * leaf) := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inr (Or.inl rfl)) (by omega)), l24]
  have hw : v2.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks' lay) =
      wordsOf (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
        (ends.drop 1).flatMap (bytesLE 16))) := by
    rw [leafInput_words' lay tree leaf ends hlen]
    have h0 : DigAt v2 LEAFPK (ends.getD 0 0) := by
      have := (hC.slots 0 (by omega)).frame fu2 (by decide) (by simp) (by simp)
      simpa [slotOff] using this
    have hrest : DigsAt v2 (LEAFPK + 32) (ends.drop 1) := by
      intro c hc
      simp only [List.length_drop] at hc
      have := (hC.slots (c + 1) (by omega)).frame fu2 (by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega)
        (by simp) (by simp)
      simp only [slotOff, if_neg (show c + 1 ≠ 0 by omega)] at this
      rw [show LEAFPK + 32 + 16 * c = LEAFPK + (16 * (c + 1) + 16) by ring]
      simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
    have hhd : v2.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
        [BitVec.ofNat 64 (hdr0 2 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf)] := by
      rw [readWords_two, hhd16, show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, hhd24,
        hdr0_eq 2 lay.val tree 0 (by decide) (by omega) htree (by decide), hdr1_eq tree leaf htree hleaf32]
      congr 2
    rcases leafBlocks'_cases lay with ⟨hb15, hn'⟩ | ⟨hb11, hn'⟩
    · have hz : v2.readWords (BitVec.ofNat 64 (LEAFPK + 880)) 2 = [0, 0] := by
        rw [readWords_two, hfar _ (by decide) (Or.inl rfl), show LEAFPK + 880 + 8 = LEAFPK + 888 from rfl,
          hfar _ (by decide) (Or.inr rfl), hpre.l944, hpre.l952]
      have hb : 8 * leafBlocks' lay = 2 + (2 + (2 * (ends.drop 1).length + 2)) := by
        simp only [List.length_drop, hlen, hb15, hn']
      rw [hb, readWords_add, readWords_add, readWords_add, h0.words, hhd, hrest.words,
        show LEAFPK + 8 * 2 + 8 * 2 + 8 * (2 * (ends.drop 1).length) = LEAFPK + 880 by
          simp only [List.length_drop, hlen, hn', LEAFPK], hz, if_pos hn']
      simp only [List.append_assoc]
    · have hb : 8 * leafBlocks' lay = 2 + (2 + 2 * (ends.drop 1).length) := by
        simp only [List.length_drop, hlen, hb11, hn']
      rw [hb, readWords_add, readWords_add, h0.words, hhd, hrest.words, if_neg (by omega)]
      simp only [List.append_assoc, List.append_nil]
  have hl := leafInput_length' lay tree leaf ends hlen
  have hB : 1 ≤ leafBlocks' lay := by rcases leafBlocks'_cases lay with h | h <;> omega
  have h11' : v2.getReg .x11 = BitVec.ofNat 64 (64 * leafBlocks' lay) := by
    rw [h11]; unfold leafBlocks'; congr 1; omega
  have hq : hashInput v2 = toQ (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
      (ends.drop 1).flatMap (bytesLE 16))) := by
    refine hashInput_toQ v2 _ (leafBlocks' lay - 1) LEAFPK (by rw [hl]; congr 1; omega) h10 (by decide) (by decide)
      (by rw [h11']; congr 2; omega) (by rcases leafBlocks'_cases lay with h | h <;> omega)
      (by rw [show 8 * (leafBlocks' lay - 1 + 1) = 8 * leafBlocks' lay by omega]; exact hw)
  have hblk : (toQ (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 lay.val tree 0 leaf) ++
      (ends.drop 1).flatMap (bytesLE 16)))).blocks = leafBlocks' lay := by
    rw [blocks_toQ ⟨by rw [hl]; omega, by rw [hl]; omega⟩, hl]; omega
  have hv : hashArgumentsValid v2 = true :=
    hashArgs_const v2 LEAFPK (64 * leafBlocks' lay) NOUT h10 h11' h12 (by decide)
      (by rcases leafBlocks'_cases lay with h | h <;> omega) (by rcases leafBlocks'_cases lay with h | h <;>
        simp only [LEAFPK] <;> omega) (by decide) (by decide)
  have rs2 : RegsExcept s0 v2 oneRegs := ((r1.trans hC.regs).trans ru2).mono (by decide)
  have h5 : v2.getReg .x5 = 0 := by rw [rs2.get (by decide), hpre.x5]
  unfold leafHash
  refine (TBSim.steps (sv1.trans sv2) (tb_shortHash_bind' (W := 13 + height lay * 60) (fetch_1072 v2 pv2) h5 hv hq
    (fun a => ?_))).mono (by rw [hblk]; omega) (fun _ _ h => h)
  set tc := writeHash v2 a with htc
  have pc3 : tc.pc = pcOf 1073 := by rw [htc, pc_writeHash, pv2, pcOf_add4]
  have rtc : RegsExcept s0 tc oneRegs := fun r hr => by rw [htc, getReg_writeHash]; exact rs2 r hr
  have fwc := Frame.writeHash v2 a NOUT h12 (by decide)
  have ftc : Frame s0 tc (fun A => (((A = CHAIN + 24 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨ ChW WC ends.length A) ∨
      False) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) := fs2.trans fwc
  have hfar' : ∀ A, A < 2 ^ 64 → WC + 64 ≤ A → (A < CHAIN ∨ CHAIN + 80 ≤ A) → (A < LEAFPK ∨ LEAFPK + 960 ≤ A) →
      (A < NOUT ∨ NOUT + 32 ≤ A) → tc.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    refine ftc.get hA ?_
    rintro (((h | h) | h) | h)
    · simp only [CHAIN, LEAFPK] at h h2 h3; omega
    · exact not_ChW_of (by omega) h1 (by simp only [CHAIN] at h2 ⊢; omega) (by simp only [LEAFPK] at h3 ⊢; omega) h
    · exact h
    · simp only [NOUT] at h h4; omega
  obtain ⟨v4, sv4, pv4, x20, x22, rv4, fv4⟩ := rl1073_spec tc pc3 P (chainCount lay) (by omega)
    (by rw [rtc.get (by decide), hpre.x16]) (by rw [rtc.get (by decide), hpre.x26])
  have hM0 : MkInv tc sig lay leaf P WM 0 (a.extractLsb' 0 128) v4 := by
    refine ⟨pv4, x20, by rw [x22]; congr 1, ?_, by omega, ?_, fun j hj => absurd hj (by omega), rv4.mono (by decide),
      fv4.mono (fun _ _ h => h.elim)⟩
    · rw [rv4.get (by decide), rtc.get (by decide), hpre.x24]; congr 1
    · exact (DigAt.writeHash_lo v2 a NOUT h12 (by decide)).frame fv4 (by decide) (by simp) (by simp)
  have c5 : tc.getReg .x5 = 0 := by rw [rtc.get (by decide), hpre.x5]
  have c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [rtc.get (by decide), hpre.x8]
  have c9 : tc.getReg .x9 = BitVec.ofNat 64 tree := by rw [rtc.get (by decide), hpre.x9]
  have c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf := by rw [rtc.get (by decide), hpre.x18]
  have c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay) := by rw [rtc.get (by decide), hpre.x15]
  have cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [hfar' _ (by decide) (by simp only [NODE]; omega) (by simp only [NODE, CHAIN]; omega)
      (by simp only [NODE, LEAFPK]; omega) (by simp only [NODE, NOUT]; omega), hpre.n32]
  have cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [hfar' _ (by decide) (by simp only [NODE]; omega) (by simp only [NODE, CHAIN]; omega)
      (by simp only [NODE, LEAFPK]; omega) (by simp only [NODE, NOUT]; omega), hpre.n40]
  have cpath : ∀ j < height lay, DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) := by
    intro j hj
    have hp := hpre.path j hj
    have e : lpath sig lay j = (sig.layers lay).path ⟨j, hj⟩ := by unfold lpath; rw [dif_pos hj]
    rw [e]
    exact ⟨(hfar' _ (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega)
      (by simp only [NOUT]; omega)).trans hp.1, (hfar' _ (by omega) (by omega) (by simp only [CHAIN]; omega)
      (by simp only [LEAFPK]; omega) (by simp only [NOUT]; omega)).trans hp.2⟩
  have hfold := tb_foldlM_finRange (image := image) (sk := sk) (height lay - 1)
    (fun value j => do
      let other := (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j)
      let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      nodeHash 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1 pair.2)
    (a.extractLsb' 0 128) 60 (fun j value w => MkInv tc sig lay leaf P WM j value w)
    (fun i acc w hw => rl_mk_step (by omega) (Or.inl (by omega)) htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM (by omega)
      c5 c8 c9 c18 c15 (cpath i.val (by omega)) cn32 cn40 hw) hM0
  have hHp : 0 < height lay := by fin_cases lay <;> decide
  refine (TBSim.steps sv4 (TBSim.bind (W₂ := 45) hfold (fun root w hw => ?_))).mono (by omega) (fun _ _ h => h)
  obtain ⟨t, k, st, hk, pt, pl, pr, pwi, rt, ft⟩ := rl_mk_finish (by omega) hlow (by omega)
    htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM (by omega)
    c5 c8 c9 c18 c15 (cpath (height lay - 1) (by omega)) cn32 cn40 hw ret
    (by rw [rtc.get (by decide)]; exact hpre.x1)
  have hpath : lpath sig lay (height lay - 1) = (wsig.layers lay).path (WCT9.topLevel lay) := by
    unfold lpath
    rw [dif_pos (by omega)]
    rfl
  refine (TBSim.steps st (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  refine ⟨pt, ?_, ?_, ?_, pwi, (rtc.trans rt).mono (by decide), ?_⟩
  · simpa only [hpath, hleaf_def, apply_ite Prod.fst, Prod.fst] using pl
  · simpa only [hpath, hleaf_def, apply_ite Prod.snd, Prod.snd] using pr
  · intro i hi
    have hv := hC.wvals i (by omega)
    have hWi : WM + 64 ≤ WC - 64 * i + 48 := by omega
    exact (((hv.frame fu2 (by omega) (by simp) (by simp)).frame fwc (by omega)
      (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)).frame ft (by omega)
      (by rintro (h | h); exact not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega) h; simp only [ENC] at h; omega)
      (by rintro (h | h); exact not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega) h; simp only [ENC] at h; omega))
  · refine (ftc.trans ft).mono (fun A hA h => ?_)
    rcases h with (((hX | hC) | hF) | hN) | hT
    · left; left
      unfold RlScratch
      rcases hX with h | h | h <;> simp only [CHAIN, LEAFPK] at h ⊢ <;> omega
    · unfold ChW StepW at hC
      rcases hC with (h | h) | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
      · left; left; unfold RlScratch; omega
      · left; left; unfold RlScratch; omega
      · have hlt := slotOff_lt (show c < chainCount lay by omega)
        left; left; unfold RlScratch; simp only [LEAFPK] at h ⊢; omega
      · left; right; left; exact ⟨c, by omega, h⟩
    · exact hF.elim
    · left; left; unfold RlScratch; omega
    · rcases hT with hM | hE
      · unfold MkW at hM
        rcases hM with h | h | h | h | h | h | h | ⟨j, hj, h⟩
        all_goals first | (left; left; unfold RlScratch; omega) | (left; right; right; exact ⟨j, hj, h⟩)
      · unfold RlScratch
        simp only [ENC] at hE
        simp only [ENC]
        omega
end SigGolfCandidate.T3M.Expand
end

section

namespace SigGolfCandidate.T3M.Expand.BC
open OracleComp SigGolfCandidate.T3
open ClaudeWCT
def recoverMsg (sig : WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) : M WCT9.LayerMsg :=
  if lay = 0 then do
    let root ← recoverLayer (WCT9.toT3Signature sig) index lay digits
    pure (.forest root)
  else do
    let pair ← WCT9.recoverLayerPair sig index lay digits
    pure (.pair pair.1 pair.2)
def layerRun (sig : WCT9.Signature) (index : Nat) : Nat → WCT9.LayerMsg → M (Option (Digest × List (BitVec 32)))
  | 0, msg => match msg with
    | .forest root => pure (some (root, []))
    | .pair _ _ => pure none
  | n + 1, msg => WCT9.expandLayersBC sig index (n + 1) msg
theorem layerRun_succ (sig : WCT9.Signature) (index n : Nat) (hn : n < 4) (value : WCT9.LayerMsg) :
    layerRun sig index (n + 1) value =
      WCT9.layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0
          counterLimit >>= fun r => match r with
        | some (counter, digits) => recoverMsg sig index (Fin.ofNat 4 n) digits >>= fun msg =>
            layerRun sig index n msg >>= fun r' => match r' with
              | some (root, counters) => pure (some (root, counters ++ [counter]))
              | none => pure none
        | none => pure none := by
  conv_lhs => unfold layerRun; unfold WCT9.expandLayersBC
  dsimp only
  congr 1
  funext r
  rcases r with _ | ⟨c, ds⟩
  · rfl
  · cases n with
    | zero => simp [recoverMsg, layerRun, bind_assoc]
    | succ n =>
      have hl : (Fin.ofNat 4 (n + 1) : Layer) ≠ 0 := by
        intro he
        have hv := congrArg Fin.val he
        change (n + 1) % 4 = 0 at hv
        rw [Nat.mod_eq_of_lt hn] at hv
        omega
      simp only [Nat.succ_ne_zero, ↓reduceIte, recoverMsg, if_neg hl, bind_assoc, pure_bind]
      congr 1
      funext pair
      change (WCT9.expandLayersBC sig index (n + 1) (.pair pair.1 pair.2) >>= _) = _
      congr 1
      funext r'
      rcases r' with _ | ⟨root, counters⟩ <;> rfl
end SigGolfCandidate.T3M.Expand.BC
end

section




namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit counterLimit decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsW csRegs csT csOk
  KernAt kernAt_expand topDigits lowDigits decode_top decode_low)
open SigGolfCandidate.T3M.Search.BC (CsArgs CsPre CsPost counterSearch_tbsim)
open ClaudeWCT
set_option autoImplicit false
theorem decode_digit_le {lay : Layer} {v : Digest} {ds : List Nat} (h : decode lay v = some ds) :
    ∀ i < chainCount lay, ds.getD i 0 ≤ maxDigit lay i := fun i hi => T3.decode_digit_max h i hi
def entryOf : Nat → Nat
  | 0 => 342
  | n + 1 => lE (Fin.ofNat 4 n)
theorem lR2_eq (n : Nat) (hn : n < 4) : lR2 (Fin.ofNat 4 n) = entryOf n := by
  interval_cases n <;> rfl
theorem lE_eq (n : Nat) : lE (Fin.ofNat 4 n) = entryOf (n + 1) := rfl
def SigLayersAt (s : MachineState) (sig : WCT9.Signature) : Prop :=
  ∀ lay : Layer, (∀ i (h : i < chainCount lay), DigAt s (lP lay + 16 * i) ((sig.layers lay).values ⟨i, h⟩)) ∧
    (∀ j (h : j < height lay), DigAt s (lP lay + 16 * chainCount lay + 16 * j) ((sig.layers lay).path ⟨j, h⟩))
structure LZero (s : MachineState) : Prop where
  c0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  c8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  c32 : s.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0
  c40 : s.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
  n32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  l944 : s.getMem (BitVec.ofNat 64 (LEAFPK + 880)) = 0
  l952 : s.getMem (BitVec.ofNat 64 (LEAFPK + 888)) = 0
  e40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
structure LInv (sig : WCT9.Signature) (index n : Nat) (value : WCT9.LayerMsg) (s : MachineState) : Prop where
  pc : s.pc = pcOf (entryOf n)
  hn : n ≤ 4
  x5 : s.getReg .x5 = 0
  hidx : index < 2 ^ 31
  idx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt s ENC (Search.BC.left value)
  right : n ≠ 0 → DigAt s (ENC + 48) (Search.BC.right value)
  terminal : n = 0 → ∃ root, value = .forest root
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  sigl : SigLayersAt s sig
  z : LZero s
  table : Search.TableOK s
def HalfAt (t : MachineState) (D k : Nat) (v : BitVec 32) : Prop :=
  (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 = v
def HalfFrame (s t : MachineState) (n : Nat) : Prop :=
  ∀ D k, (D = 0x41e8 ∨ D = 0x4e68 ∨ D = 0x5aa8 ∨ D = 0x820 ∨ D = 0x810 ∨ D = 0x818) → k < 2 → (∀ lay : Layer, lay.val < n → ¬ (lD lay = D ∧ lk lay = k)) →
    (t.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 = (s.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32
def lRegs : List Reg :=
  [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
    .x25, .x26, .x27, .x28, .x29, .x30]
def RlScratch (A : Nat) : Prop := Expand.RlScratch A ∨ A = ENC + 48 ∨ A = ENC + 56
def LW (index n : Nat) (A : Nat) : Prop :=
  CsW A ∨ RlScratch A ∨ ∃ lay : Layer, lay.val < n ∧ (A = lD lay ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A)
def LayerOut (t : MachineState) (sig : WCT9.Signature) (index : Nat) (lay : Layer) (c : BitVec 32) : Prop :=
  HalfAt t (lD lay) (lk lay) c ∧ (∀ i < chainCount lay, DigAt t (lWC lay - 64 * i + 48) (lval (WCT9.toT3Signature sig) lay i)) ∧
    (∀ j < height lay, DigAt t (lWM lay - 64 * j + sideOff (route index lay).1 j) (lpath (WCT9.toT3Signature sig) lay j))
def LPost (s : MachineState) (sig : WCT9.Signature) (index n : Nat) :
    Option (Digest × List (BitVec 32)) → MachineState → Prop
  | none, t => Search.FailedAt 354 t
  | some (root, counters), t => t.pc = pcOf 342 ∧ t.getReg .x5 = 0 ∧ DigAt t ENC root ∧ counters.length = n ∧
      (∀ lay : Layer, lay.val < n → LayerOut t sig index lay (counters.getD lay.val 0)) ∧
      HalfFrame s t n ∧ RegsExcept s t lRegs ∧ Frame s t (LW index n)
def layCost (lay : Layer) : Nat := lK lay + (10 + 2 ^ 22 * csT lay + csOk lay) + 10 + rlCost lay
def lcost : Nat → Nat
  | 0 => 0
  | n + 1 => layCost (Fin.ofNat 4 n) + lcost n
theorem ltable (lay : Layer) :
    0x7000 ≤ lP lay ∧ lP lay + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616 ∧ lP lay % 8 = 0 ∧
    lWC lay % 8 = 0 ∧ lWM lay % 8 = 0 ∧ 0x800 + 64 * (height lay - 1) ≤ lWM lay ∧
    lWM lay + 64 + 64 * (chainCount lay - 1) ≤ lWC lay ∧ lWC lay + 64 ≤ 0x7000 ∧ lD lay + 8 ≤ 0x7000 ∧
    0x810 ≤ lD lay ∧ lk lay < 2 := by
  fin_cases lay <;> decide
theorem fin_ofNat_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := by
  simp [Fin.ofNat, Nat.mod_eq_of_lt hn]
theorem replaceWord32_get (w : BitVec 64) (k : Nat) (hk : k < 2) (v : BitVec 32) :
    (replaceWord32 w k v).extractLsb' (32 * k) 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : Nat.testBit 4294967295 i = true := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
  interval_cases k <;>
  · simp only [replaceWord32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    simp (config := { decide := true }) [show i < 64 by omega, show 32 + i < 64 by omega, hi, hm]
theorem replaceWord32_other (w : BitVec 64) (k k' : Nat) (hk : k < 2) (hk' : k' < 2) (hne : k ≠ k')
    (v : BitVec 32) : (replaceWord32 w k v).extractLsb' (32 * k') 32 = w.extractLsb' (32 * k') 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : Nat.testBit 4294967295 i = true := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
  have hm2 : Nat.testBit 4294967295 (32 + i) = false := by
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp
  interval_cases k <;> interval_cases k' <;> simp at hne <;>
  · simp only [replaceWord32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    simp (config := { decide := true }) [show i < 64 by omega, show 32 + i < 64 by omega, hi, hm, hm2]
theorem rlWit_range {lay : Layer} {leaf A : Nat} (h : RlWit lay leaf (lWC lay) (lWM lay) A) :
    lWM lay - 64 * (height lay - 1) ≤ A ∧ A + 8 ≤ lWC lay + 64 := by
  have htab := ltable lay
  rcases h with ⟨i, hi, h | h⟩ | ⟨j, hj, h | h⟩ <;>
    first | omega | (have := sideOff_le leaf j; omega)
theorem ltable_disj (lay lay' : Layer) (h : lay ≠ lay') :
    lWC lay + 64 ≤ lWM lay' - 64 * (height lay' - 1) ∨ lWC lay' + 64 ≤ lWM lay - 64 * (height lay - 1) := by
  fin_cases lay <;> fin_cases lay' <;> simp_all <;> decide
theorem lhalf_inj (lay lay' : Layer) (h1 : lD lay = lD lay') (h2 : lk lay = lk lay') : lay = lay' := by
  fin_cases lay <;> fin_cases lay' <;> simp_all [lD, lk]
theorem ltable_lo (lay : Layer) : 0x3148 ≤ lWM lay - 64 * (height lay - 1) := by
  fin_cases lay <;> decide
theorem counter_ne_wit (counter lay : Layer) (leaf : Nat) :
    ¬ RlWit lay leaf (lWC lay) (lWM lay) (lD counter) := by
  intro h
  unfold RlWit at h
  rcases h with ⟨i, hi, h⟩ | ⟨j, hj, h⟩
  · fin_cases counter <;> fin_cases lay <;> norm_num [lD, lWC, chainCount] at * <;> omega
  · unfold sideOff at h
    fin_cases counter <;> fin_cases lay <;> norm_num [lD, lWM, height] at * <;> split_ifs at h <;> omega
end SigGolfCandidate.T3M.Expand.BC
end

section

namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route chainCount height)
open SigGolfCandidate.T3M.Search (ENC)
open ClaudeWCT
def RecoverPost (s0 : MachineState) (sig : WCT9.Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat)
    (msg : WCT9.LayerMsg) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t ENC (Search.BC.left msg) ∧
    (lay ≠ 0 → DigAt t (ENC + 48) (Search.BC.right msg)) ∧
    (lay = 0 → ∃ root, msg = .forest root) ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval (WCT9.toT3Signature sig) lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath (WCT9.toT3Signature sig) lay j)) ∧
    RegsExcept s0 t rlRegs ∧ Frame s0 t (fun A => RlScratch A ∨ RlWit lay (route index lay).1 WC WM A)
theorem recoverMsg_tbsim {sk : BitVec 256} {s0 : MachineState} {sig : WCT9.Signature} {index : Nat} {lay : Layer}
    {digits : List Nat} {P WC WM ret : Nat}
    (hpre : RlPre s0 (WCT9.toT3Signature sig) index lay digits P WC WM ret) :
    TBSim image sk s0 (rlCost lay) (recoverMsg sig index lay digits) (RecoverPost s0 sig index lay WC WM ret) := by
  unfold recoverMsg
  split_ifs with ht
  · refine (TBSim.bind (W₂ := 0) (recoverLayer_tbsim hpre ht) (fun root t h => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨pc, enc, cv, pv, regs, frame⟩ := h
    refine TBSim.pure ⟨pc, enc, (fun hn => False.elim (hn ht)), (fun _ => ⟨root, rfl⟩), cv, pv, regs, ?_⟩
    exact frame.mono (by intro A hA h; rcases h with h | h; exact Or.inl (Or.inl h); exact Or.inr h)
  · refine (TBSim.bind (W₂ := 0) (recoverLayerPair_tbsim hpre ht) (fun pair t h => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨pc, enc, right, cv, pv, regs, frame⟩ := h
    refine TBSim.pure ⟨pc, enc, (fun _ => right), (fun he => False.elim (ht he)), cv, pv, regs, ?_⟩
    exact frame.mono (by intro A hA h; rcases h with (h | h) | h; exact Or.inl (Or.inl h); exact Or.inr h; exact Or.inl (Or.inr h))
end SigGolfCandidate.T3M.Expand.BC
end

section

namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit counterLimit decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsW csRegs csT csOk
  KernAt kernAt_expand topDigits lowDigits decode_top decode_low)
open SigGolfCandidate.T3M.Search.BC (CsArgs CsPre CsPost counterSearch_tbsim)
open ClaudeWCT
set_option autoImplicit false
section step
variable {sk : BitVec 256}
theorem layer_step {sig : WCT9.Signature} {index n : Nat} {value : WCT9.LayerMsg} {s : MachineState} (hn : n < 4)
    (hI : LInv sig index (n + 1) value s)
    (ih : ∀ v' s', LInv sig index n v' s' →
      TBSim image sk s' (lcost n) (layerRun sig index n v') (LPost s' sig index n)) :
    TBSim image sk s (lcost (n + 1)) (layerRun sig index (n + 1) value) (LPost s sig index (n + 1)) := by
  set lay : Layer := Fin.ofNat 4 n with hlay
  have hlv : lay.val = n := fin_ofNat_val n hn
  have htab := ltable lay
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hI.hidx
  have hleaf : leaf < 2 ^ height lay := route_lt index lay
  have hH := height_le lay
  have hleaf32 : leaf < 2 ^ 32 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨t1, s1, p1, x1, x8, x15, x26, x27, x17, x18, x9, r1, f1⟩ :=
    lentry_spec lay s (by rw [hI.pc]; rfl) index hI.hidx hI.idx
  have g1 : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => f1.get hA (fun h => h)
  obtain ⟨x, hx, hx32⟩ := hI.c32
  have htable1 : Search.TableOK t1 := hI.table.frame f1 (by intro i hi h; exact h)
  have hcs : CsPre 354 ⟨lay, tree, leaf, value, lR1 lay⟩ t1 :=
    ⟨p1, x1, by rw [r1.get (by decide)]; exact hI.x5, x8, x9, x18, x17, x26, x27, htree, hleaf32,
      by rw [g1 _ (by decide)]; exact hI.enc.1, by rw [g1 _ (by decide)]; exact hI.enc.2,
      ⟨x, hx, by rw [g1 _ (by decide)]; exact hx32⟩, by rw [g1 _ (by decide)]; exact hI.z.e40,
      by rw [g1 _ (by decide)]; exact (hI.right (by omega)).1, by rw [g1 _ (by decide)]; exact (hI.right (by omega)).2, htable1⟩
  rw [layerRun_succ _ _ _ hn]
  refine (TBSim.steps s1 (TBSim.bind (W₂ := 10 + rlCost lay + lcost n)
    (counterSearch_tbsim (sk := sk) kernAt_expand hcs) (fun r t2 h2 => ?_))).mono
    (by simp only [lcost, layCost, ← hlay, Search.BC.csT, Search.BC.csOk, csT, csOk]; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, ds⟩
  · obtain ⟨p2, h5, h10, _⟩ := h2
    exact (TBSim.pure (Q := LPost s sig index (n + 1)) (a := none) ⟨p2, h5, h10⟩).mono (by omega) (fun _ _ h => h)
  · obtain ⟨p2, hc, x19, e32, ⟨v, hdec⟩, hlen, hdig, r2, f2, _⟩ := h2
    dsimp only at p2 hc x19 e32 hdec hlen hdig
    change Frame t1 t2 CsW at f2
    obtain ⟨t3, s3, p3, x1', hD, x16, x23, x24, r3, f3⟩ := lpost_spec lay t2 p2 c.toNat x19
    have g3 : ∀ r, r ∉ [Reg.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] → r ∉ csRegs →
        r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = s.getReg r :=
      fun r h1 h2 h3 => by rw [r3.get h3, r2.get h2, r1.get h1]
    have g3' : ∀ r, r ∉ csRegs → r ∉ [Reg.x1, .x16, .x23, .x24, .x28] → t3.getReg r = t1.getReg r :=
      fun r h2 h3 => by rw [r3.get h3, r2.get h2]
    have m3 : ∀ A, A < 2 ^ 64 → ¬ CsW A → A ≠ lD lay → t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
      fun A hA h1 h2 => by rw [f3.get hA h2, f2.get hA h1, g1 A hA]
    have hcsw : ∀ A, (A < 0x20260 ∨ 0x20460 ≤ A) → ¬ CsW A := by
      intro A hA h; unfold CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
    have hrl : RlPre t3 (WCT9.toT3Signature sig) index lay ds (lP lay) (lWC lay) (lWM lay) (lR2 lay) := by
      refine ⟨p3, x1', by rw [g3 _ (by decide) (by decide) (by decide)]; exact hI.x5,
        by rw [g3' _ (by decide) (by decide)]; exact x8, by rw [g3' _ (by decide) (by decide)]; exact x9,
        by rw [g3' _ (by decide) (by decide)]; exact x18, by rw [g3' _ (by decide) (by decide)]; exact x15,
        by rw [g3' _ (by decide) (by decide)]; exact x26, by rw [g3' _ (by decide) (by decide)]; exact x27,
        x16, x23, x24, hI.hidx, htab.1, htab.2.1, htab.2.2.1, htab.2.2.2.1, htab.2.2.2.2.1, htab.2.2.2.2.2.1,
        htab.2.2.2.2.2.2.1, htab.2.2.2.2.2.2.2.1, ?_, decode_digit_le hdec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [Frame.getByte f3 (by simp only [DIGITS]; omega)
          (by have := htab.2.2.2.2.2.2.2.2.1; simp only [DIGITS]; omega)]
        exact hdig i hi
      · intro i hi
        have hv := (hI.sigl lay).1 i hi
        have hb := htab.2.1
        exact ⟨(m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.1,
          (m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.2⟩
      · intro j hj
        have hv := (hI.sigl lay).2 j hj
        have hb := htab.2.1
        exact ⟨(m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.1,
          (m3 _ (by omega) (hcsw _ (by omega)) (by omega)).trans hv.2⟩
      all_goals
        first
          | (rw [m3 _ (by decide) (hcsw _ (by simp only [CHAIN, NODE, LEAFPK]; omega))
              (by have := htab.2.2.2.2.2.2.2.2.1; simp only [CHAIN, NODE, LEAFPK]; omega)]
             first | exact hI.z.c0 | exact hI.z.c8 | exact hI.z.c32 | exact hI.z.c40 | exact hI.z.n32 |
               exact hI.z.n40 | exact hI.z.l944 | exact hI.z.l952)
    refine (TBSim.steps s3 (TBSim.bind (W₂ := lcost n) (recoverMsg_tbsim (sk := sk) hrl)
      (fun root t4 h4 => ?_))).mono (by omega) (fun _ _ h => h)
    obtain ⟨p4, e4, er4, form4, cv4, pv4, r4, f4⟩ := h4
    have hfar4 : ∀ A, A < 2 ^ 64 → ¬ CsW A → A ≠ lD lay → (A < 0x3148 ∨ 0x7000 ≤ A) → ¬ RlScratch A →
        t4.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      have hw : ¬ (RlScratch A ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) A) := by
        rintro (h | h)
        · exact h4 h
        · have := rlWit_range h; have := ltable_lo lay; omega
      rw [f4.get hA hw, m3 A hA h1 h2]
    have hd8 := htab.2.2.2.2.2.2.2.2.1
    have hd0 := htab.2.2.2.2.2.2.2.2.2.1
    have ncs : ∀ A, (A < 0x20260 ∨ (0x20260 + 40 ≤ A ∧ A < EOUT) ∨ 0x20460 ≤ A) → ¬ CsW A := by
      intro A hA h; unfold CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h hA; omega
    have nrl : ∀ A, ((A < CHAIN + 16 ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 48) ∨ CHAIN + 80 ≤ A) ∧
        (A < NODE ∨ (NODE + 32 ≤ A ∧ A < NODE + 48) ∨ NOUT + 32 ≤ A) ∧ (A < LEAFPK ∨ LEAFPK + 880 ≤ A) ∧
        A ≠ ENC ∧ A ≠ ENC + 8 ∧ A ≠ ENC + 48 ∧ A ≠ ENC + 56 ∧ (A % 8 = 0)) → ¬ RlScratch A := by
      intro A hA h; unfold RlScratch Expand.RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h hA; omega
    have hI4 : LInv sig index n root t4 := by
      have hx5 : t4.getReg .x5 = 0 := by
        rw [r4.get (by decide), g3 _ (by decide) (by decide) (by decide)]; exact hI.x5
      refine ⟨by rw [p4, hlay, lR2_eq n hn], by omega, hx5, hI.hidx, ?_, e4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfar4 IDXV (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
        exact hI.idx
      · intro hn0
        exact er4 (by intro he; have hv := congrArg Fin.val he; change lay.val = 0 at hv; omega)
      · intro hn0
        exact form4 (Fin.ext (by simpa only [Fin.val_zero] using hlv.trans hn0))
      · refine ⟨c.toNat, by omega, ?_⟩
        have hw : ¬ (RlScratch (ENC + 32) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (ENC + 32)) := by
          rintro (h | h)
          · exact nrl _ (by decide) h
          · have h1 := rlWit_range h; have := ltable_lo lay; have := htab.2.2.2.2.2.2.2.1
            simp only [ENC] at h1; omega
        rw [f4.get (by decide) hw, f3.get (by decide) (by simp only [ENC]; omega), e32]
      · intro lay'
        have htab' := ltable lay'
        have hb := htab'.2.1
        have hb0 := htab'.1
        have hb8 := htab'.2.2.1
        refine ⟨fun i hi => ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
        · rw [hfar4 (lP lay' + 16 * i) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').1 i hi).1
        · rw [hfar4 (lP lay' + 16 * i + 8) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').1 i hi).2
        · rw [hfar4 (lP lay' + 16 * chainCount lay' + 16 * j) (by omega) (ncs _ (by omega)) (by omega) (by omega)
            (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').2 j hj).1
        · rw [hfar4 (lP lay' + 16 * chainCount lay' + 16 * j + 8) (by omega) (ncs _ (by omega)) (by omega)
            (by omega) (nrl _ (by simp only [CHAIN, NODE, NOUT, LEAFPK, ENC]; omega))]
          exact ((hI.sigl lay').2 j hj).2
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfar4 CHAIN (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c0
        · rw [hfar4 (CHAIN + 8) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c8
        · rw [hfar4 (CHAIN + 32) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c32
        · rw [hfar4 (CHAIN + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.c40
        · rw [hfar4 (NODE + 32) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.n32
        · rw [hfar4 (NODE + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.n40
        · rw [hfar4 (LEAFPK + 880) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.l944
        · rw [hfar4 (LEAFPK + 888) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.l952
        · rw [hfar4 (ENC + 40) (by decide) (ncs _ (by decide)) (by simp only [IDXV, CHAIN, NODE, LEAFPK, ENC]; omega) (by decide) (nrl _ (by decide))]
          exact hI.z.e40
      · apply hI.table.frame (((f1.trans f2).trans f3).trans f4)
        intro i hi h
        rcases h with ((h | h) | h) | h
        · exact h
        · unfold CsW Search.DigW at h
          simp only [Search.TOP_DATA, ENC, EOUT, DIGITS] at h
          omega
        · have := htab.2.2.2.2.2.2.2.2.1
          simp only [Search.TOP_DATA] at h
          omega
        · rcases h with h | h
          · unfold RlScratch Expand.RlScratch at h
            simp only [Search.TOP_DATA, CHAIN, NODE, NOUT, LEAFPK, ENC] at h
            omega
          · have hh := rlWit_range h
            have hb := htab.2.2.2.2.2.2.2.1
            simp only [Search.TOP_DATA] at hh
            omega
    refine (TBSim.bind (W₂ := 0) (ih root t4 hI4) (fun r' t5 h5 => ?_)).mono (by omega) (fun _ _ h => h)
    rcases r' with _ | ⟨root', counters⟩
    · exact TBSim.pure h5
    · obtain ⟨p5, x5', e5, hlen5, hout5, hhf5, r5, f5⟩ := h5
      have hk := htab.2.2.2.2.2.2.2.2.2.2
      have hDv : lD lay = 0x41e8 ∨ lD lay = 0x4e68 ∨ lD lay = 0x5aa8 ∨ lD lay = 0x820 ∨ lD lay = 0x810 ∨ lD lay = 0x818 := by
        clear_value lay; fin_cases lay <;> simp [lD]
      have hlo := ltable_lo lay
      have hnotLW : ∀ A, RlWit lay (route index lay).1 (lWC lay) (lWM lay) A → ¬ LW index n A := by
        intro A hwit h
        have hrange := rlWit_range hwit
        rcases h with h | h | ⟨lay'', h'', h | h⟩
        · unfold CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
        · unfold RlScratch Expand.RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
        · rw [h] at hwit
          exact counter_ne_wit lay'' lay _ hwit
        · have hne : lay'' ≠ lay := fun he => by rw [he] at h''; omega
          have hr := rlWit_range h
          rcases ltable_disj lay'' lay hne with hd | hd <;> omega
      have hgetD : ∀ lay' : Layer, lay'.val < n → (counters ++ [c]).getD lay'.val 0 = counters.getD lay'.val 0 :=
        fun lay' h => List.getD_append _ _ _ _ (by omega)
      refine TBSim.pure ⟨p5, x5', e5, by simp [hlen5], ?_, ?_, ?_, ?_⟩
      · intro lay' hlay'
        by_cases hlt : lay'.val < n
        · rw [hgetD lay' hlt]; exact hout5 lay' hlt
        · have heq : lay' = lay := Fin.ext (by omega)
          rw [heq, List.getD_append_right _ _ _ _ (by omega), show lay.val - counters.length = 0 by omega]
          simp only [List.getD_cons_zero]
          refine ⟨?_, fun i hi => ?_, fun j hj => ?_⟩
          · unfold HalfAt
            rw [hhf5 (lD lay) (lk lay) hDv hk (fun lay'' h'' ⟨h1, h2⟩ => by
              have := lhalf_inj _ _ h1 h2; rw [this] at h''; omega)]
            have hw : ¬ (RlScratch (lD lay) ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) (lD lay)) := by
              rintro (h | h)
              · unfold RlScratch Expand.RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
              · exact counter_ne_wit lay lay _ h
            rw [f4.get (by omega) hw, hD, replaceWord32_get _ _ hk]
            apply BitVec.eq_of_toNat_eq
            simp
          · have hv := cv4 i hi
            exact hv.frame f5 (by omega)
              (hnotLW _ (Or.inl ⟨i, hi, Or.inl rfl⟩))
              (hnotLW _ (Or.inl ⟨i, hi, Or.inr (by omega)⟩))
          · have hv := pv4 j hj
            have hs := sideOff_le (route index lay).1 j
            exact hv.frame f5 (by omega)
              (hnotLW _ (Or.inr ⟨j, hj, Or.inl rfl⟩))
              (hnotLW _ (Or.inr ⟨j, hj, Or.inr rfl⟩))
      · intro D k hD3 hk' hnot
        have hDw : ¬ (RlScratch D ∨ RlWit lay (route index lay).1 (lWC lay) (lWM lay) D) := by
          rintro (h | h)
          · unfold RlScratch Expand.RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
          · rcases hD3 with rfl | rfl | rfl | rfl | rfl | rfl
            · exact counter_ne_wit 0 lay _ h
            · exact counter_ne_wit 1 lay _ h
            · exact counter_ne_wit 2 lay _ h
            · exact counter_ne_wit 3 lay _ h
            · have := rlWit_range h; have := ltable_lo lay; omega
            · have := rlWit_range h; have := ltable_lo lay; omega
        rw [hhf5 D k hD3 hk' (fun lay'' h'' => hnot lay'' (by omega)), f4.get (by omega) hDw]
        have hD2 : t2.getMem (BitVec.ofNat 64 D) = s.getMem (BitVec.ofNat 64 D) := by
          rw [f2.get (by omega) (ncs _ (by omega)), g1 D (by omega)]
        by_cases hDl : D = lD lay
        · have hkne : lk lay ≠ k := fun he => hnot lay (by omega) ⟨hDl.symm, he⟩
          rw [hDl, hD, replaceWord32_other _ _ _ hk hk' hkne, ← hDl, hD2]
        · rw [f3.get (by omega) hDl, hD2]
      · exact ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide)
      · refine ((((f1.trans f2).trans f3).trans f4).trans f5).mono (fun A _ h => ?_)
        rcases h with ((((h | h) | h) | h | h) | h)
        · exact h.elim
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨lay, by omega, Or.inl h⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨lay, by omega, Or.inr h⟩)
        · rcases h with h | h | ⟨lay'', h'', h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨lay'', by omega, h⟩)
theorem layers_tbsim {sig : WCT9.Signature} {index : Nat} :
    ∀ n (value : WCT9.LayerMsg) (s : MachineState), LInv sig index n value s →
      TBSim image sk s (lcost n) (layerRun sig index n value) (LPost s sig index n)
  | 0, value, s, hI => by
    obtain ⟨root, rfl⟩ := hI.terminal rfl
    refine TBSim.pure (Q := LPost s sig index 0) (a := some (root, [])) ⟨hI.pc, hI.x5, hI.enc, rfl,
      fun lay h => absurd h (by omega), fun _ _ _ _ _ => rfl, RegsExcept.refl _ _, Frame.refl _ _⟩
  | n + 1, value, s, hI => layer_step (by have := hI.hn; omega) hI
      (fun v' s' h' => layers_tbsim n v' s' h')
end step
end SigGolfCandidate.T3M.Expand.BC
end

section

namespace SigGolfCandidate.T3M.Expand
abbrev entryOf := BC.entryOf
abbrev SigLayersAt := BC.SigLayersAt
abbrev LZero := BC.LZero
abbrev LInv := BC.LInv
abbrev HalfAt := BC.HalfAt
abbrev HalfFrame := BC.HalfFrame
abbrev lRegs := BC.lRegs
abbrev LW := BC.LW
abbrev LayerOut := BC.LayerOut
abbrev LPost := BC.LPost
abbrev layCost := BC.layCost
abbrev lcost := BC.lcost
abbrev layers_tbsim := @BC.layers_tbsim
end SigGolfCandidate.T3M.Expand
end
