import SigGolfCandidate.T3M.Keygen.Leaf

/-!
# Sign: `build_leaf` with an unaligned root register for signature-only leaves

K's `buildLeaf_tsim` (`Keygen/Leaf.lean`) requires the root slot `dest` (register `s9`) to be
8-aligned even when the leaf is signature-only and `dest` is never written. At sign's first layer-0
call (word 446) `s9` still holds `counter_search`'s digit total (127), so that lemma does not apply.
This module is K's proof verbatim (theorems suffixed `S`) over `LeafPreS`, which asks
`dest % 8 = 0` only for `so = false`; `buildLeaf_tsimS` subsumes `buildLeaf_tsim`.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest chainCount width chain chainInput buildLeaf leafHash privatePair
  shortHash header pad64 zero16 privateInput)
open SphincsSecurity (bytesLE bytesLE_length)

/-- Entry conditions of `build_leaf` (offset 27), as K's `LeafPre` but with the root slot alignment
required only when the root is written (`so = false`). -/
structure LeafPreS (sk : BitVec 256) (s : MachineState) (A : LeafArgs) : Prop where
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x22 : s.getReg .x22 = BitVec.ofNat 64 A.digp
  x23 : s.getReg .x23 = BitVec.ofNat 64 A.valp
  x25 : s.getReg .x25 = BitVec.ofNat 64 A.dest
  x26 : s.getReg .x26 = BitVec.ofNat 64 A.n
  x27 : s.getReg .x27 = BitVec.ofNat 64 (n4 A.lay)
  x31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  z32 : s.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0
  z40 : s.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
  ztail : A.n = 58 → s.getMem (BitVec.ofNat 64 (LEAFPK + 944)) = 0 ∧
    s.getMem (BitVec.ofNat 64 (LEAFPK + 952)) = 0
  hdig : ∀ i < A.n, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i)
  hdigb : ∀ i < A.n, A.d i < 256 ∧ (A.so = false → A.d i ≤ 2 ^ width A.lay i - 1)
  hdigp : A.digp + A.n ≤ 2 ^ 24
  hdigW : ∀ i < A.n, ¬ LeafW A ((A.digp + i) / 8 * 8)
  hv8 : A.valp % 8 = 0
  hv : A.valp + 16 * A.n ≤ 2 ^ 24
  hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp
  hd8 : A.so = false → A.dest % 8 = 0
  hd : A.dest + 16 ≤ 2 ^ 24
  hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT)
  hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * A.n ≤ A.dest

section leaf
variable {image : Image} {b : Nat} (hsub : SubAt image b) (sk : BitVec 256) {s0 : MachineState}
  {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hsub hpre

/-- From the seed copy (offset 60, seed of chain `j` at `SEEDS + 16 (j % 2)`) to the `chain_run`
entry: the digit, the end step, the jump. -/
theorem leaf_prechainS {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 60)) (seed : Digest)
    (hseed : DigAt t (SEEDS + 16 * (j % 2)) seed) :
    ∃ u, Steps image t (17 + (if j < n4 A.lay then 1 else 0) + (if A.so then 1 else 0))
        (17 + (if j < n4 A.lay then 1 else 0) + (if A.so then 1 else 0)) u ∧ u.pc = pcOf b ∧
      ChainPre u A.lay A.tree A.leaf j (A.d j) (A.e j) (A.valp + 16 * j) (b + 79) ∧
      DigAt u (CHAIN + 48) seed ∧ RegsExcept t u [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] ∧
      Frame t u (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) := by
  have hn := chainCount_cases A.lay
  have hn4 := n4_le A.lay
  have hdb := hpre.hdigb j hj
  have hvs := hpre.hvs
  have hv := hpre.hv
  have hv8 := hpre.hv8
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r22 : t.getReg .x22 = BitVec.ofNat 64 A.digp := by rw [g _ (by simp [leafRegs]), hpre.x22]
  have r27 : t.getReg .x27 = BitVec.ofNat 64 (n4 A.lay) := by rw [g _ (by simp [leafRegs]), hpre.x27]
  have r31 : t.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [g _ (by simp [leafRegs]), hpre.x31]
  obtain ⟨t1, st1, t1pc, t1x28, t1c48, t1c56, t1r, t1f⟩ := sub60_spec hsub t hpc j A.digp ht.x19 r22
  have hw := hpre.hdigW j hj
  have hbyte : t1.getByte (BitVec.ofNat 64 (A.digp + j)) = BitVec.ofNat 8 (A.d j) := by
    rw [t1f.getByte (by have := hpre.hdigp; omega) (fun h => hw (by
        simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at h ⊢; omega)),
      ht.frame.getByte (by have := hpre.hdigp; omega) hw, hpre.hdig j hj]
  obtain ⟨t2, st2, t2pc, t2x17, t2r, t2f⟩ := sub72_spec hsub t1 t1pc (A.digp + j)
    (by have := hpre.hdigp; omega) (A.d j) hdb.1 t1x28 hbyte
  have e12 : RegsExcept t t2 [.x6, .x7, .x17, .x28, .x29, .x30] := (t1r.trans t2r).mono (by simp)
  obtain ⟨t3, st3, t3pc, t3x21, t3r, t3f⟩ := sub73_spec hsub t2 t2pc j (n4 A.lay) (by omega) (by omega)
    (by rw [e12.get (by simp)]; exact ht.x19) (by rw [e12.get (by simp)]; exact r27)
  have hseedv : DigAt t1 (CHAIN + 48) seed := ⟨t1c48.trans hseed.1, by
    rw [t1c56, show SEEDS + 16 * (j % 2) + 8 = SEEDS + 16 * (j % 2) + 8 from rfl]; exact hseed.2⟩
  -- the end step register: `3` for radix-4 chains, else `7`
  obtain ⟨t4, st4, t4pc, t4x21, t4r, t4f⟩ : ∃ t4, Steps image t3 (if j < n4 A.lay then 1 else 0)
      (if j < n4 A.lay then 1 else 0) t4 ∧ t4.pc = pcOf (b + 76) ∧
      t4.getReg .x21 = BitVec.ofNat 64 (if j < n4 A.lay then 3 else 7) ∧ RegsExcept t3 t4 [.x21] ∧
      Frame t3 t4 (fun _ => False) := by
    by_cases hjn : j < n4 A.lay
    · rw [if_pos hjn] at t3pc
      obtain ⟨t4, st4, t4pc, t4x21, t4r, t4f⟩ := sub75_spec hsub t3 t3pc
      exact ⟨t4, by simpa [hjn] using st4, t4pc, by simpa [hjn] using t4x21, t4r, t4f⟩
    · rw [if_neg hjn] at t3pc
      exact ⟨t3, by simpa [hjn] using Steps.refl t3, t3pc, by simpa [hjn] using t3x21,
        RegsExcept.refl _ _, Frame.refl _ _⟩
  have e14 : RegsExcept t t4 [.x6, .x7, .x17, .x21, .x28, .x29, .x30] :=
    ((e12.trans t3r).trans t4r).mono (by simp)
  obtain ⟨t5, st5, t5pc, t5r, t5f⟩ := sub76_spec hsub t4 t4pc A.so (by rw [e14.get (by simp)]; exact r31)
  -- signature-only leaves end the chain at the digit
  obtain ⟨t6, st6, t6pc, t6x21, t6r, t6f⟩ : ∃ t6, Steps image t5 (if A.so then 1 else 0)
      (if A.so then 1 else 0) t6 ∧ t6.pc = pcOf (b + 78) ∧
      t6.getReg .x21 = BitVec.ofNat 64 (A.e j) ∧ RegsExcept t5 t6 [.x21] ∧
      Frame t5 t6 (fun _ => False) := by
    cases hso : A.so
    · rw [hso, if_neg (by simp)] at t5pc
      refine ⟨t5, by simpa using Steps.refl t5, t5pc, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [t5r.get (by simp), t4x21, LeafArgs.e, hso]; rfl
    · rw [hso, if_pos rfl] at t5pc
      obtain ⟨t6, st6, t6pc, t6x21, t6r, t6f⟩ := sub77_spec hsub t5 t5pc
      refine ⟨t6, by simpa using st6, t6pc, ?_, t6r, t6f⟩
      rw [t6x21, t5r.get (by simp), t4r.get (by simp), t3r.get (by simp), t2x17, LeafArgs.e, hso]; rfl
  obtain ⟨u, st7, upc, ux1, ur, uf⟩ := sub78_spec hsub t6 t6pc
  have e1u : RegsExcept t u [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] :=
    (((e14.trans t5r).trans t6r).trans ur).mono (by simp)
  have f1u : Frame t u (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) :=
    (((((t1f.trans t2f).trans t3f).trans t4f).trans t5f).trans (t6f.trans uf)).mono (fun X _ h => by
      simp only [or_false] at h; exact h)
  have f2u : Frame t2 u (fun _ => False) :=
    ((((t3f.trans t4f).trans t5f).trans t6f).trans uf).mono (fun X _ h => by simp_all)
  have gu : ∀ r, r ∉ leafRegs → r ∉ [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] →
      u.getReg r = s0.getReg r := fun r h1 h2 => (e1u.get h2).trans (g r h1)
  have fr : ∀ X, X < 2 ^ 64 → ¬ LeafW A X → X ≠ CHAIN + 48 → X ≠ CHAIN + 56 →
      u.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 =>
    (f1u.get hX (by simp [h2, h3])).trans (ht.frame.get hX h1)
  have hL : ∀ X, (X = CHAIN ∨ X = CHAIN + 8 ∨ X = CHAIN + 32 ∨ X = CHAIN + 40) → ¬ LeafW A X := by
    intro X hX hw'
    simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at hX hw' hvs
    have := hpre.hds
    have := hpre.hdv
    simp only [CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at *
    omega
  refine ⟨u, ?_, upc, ⟨?_, ux1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hseedv.frame (((t2f.trans t3f).trans t4f).trans (t5f.trans (t6f.trans uf))) (by decide)
      (by simp) (by simp), e1u, f1u⟩
  · have := (st1.trans st2).trans ((st3.trans st4).trans ((st5.trans st6).trans st7))
    refine Steps.of_eq this ?_ ?_ <;> split_ifs <;> simp_all
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x5]
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x8]
  · rw [ur.get (by simp), t6r.get (by simp), t5r.get (by simp), t4r.get (by simp), t3r.get (by simp),
      t2x17]
  · rw [e1u.get (by simp)]; exact ht.x19
  · rw [ur.get (by simp)]; exact t6x21
  · rw [e1u.get (by simp)]; exact ht.x23
  · exact hpre.htree
  · omega
  · unfold LeafArgs.e; split_ifs with hso h4
    · exact le_refl _
    · have := hdb.2 (by simpa using hso); rw [width_pow, if_pos h4] at this; exact this
    · have := hdb.2 (by simpa using hso); rw [width_pow, if_neg h4] at this; exact this
  · unfold LeafArgs.e; split_ifs <;> omega
  · omega
  · omega
  · simp only [CHAIN, PRIV, LEAFPK] at hvs ⊢; omega
  · rw [fr CHAIN (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z0]
  · rw [fr (CHAIN + 8) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z8]
  · rw [fr (CHAIN + 32) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z32]
  · rw [fr (CHAIN + 40) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z40]
  · rw [f1u.get (by decide) (by simp), ht.w24]

set_option maxHeartbeats 1000000 in
/-- From the return of `chain_run` (offset 79) to the next loop head: the end slot (unless
signature-only), `VALP += 16`, `I += 1`. -/
theorem leaf_postchainS {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t u : MachineState}
    (ht : LeafInv s0 A j st t) (hupc : u.pc = pcOf (b + 79))
    (hur : RegsExcept t u ([.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] ++ chainRegs))
    (huf : Frame t u (fun X => (X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X))
    (v last : Digest) (hv : DigAt u (A.valp + 16 * j) v) (hl : DigAt u (CHAIN + 48) last) :
    ∃ w, Steps image u (4 + (if A.so then 0 else 11 + (if j = 0 then 0 else 1)))
        (4 + (if A.so then 0 else 11 + (if j = 0 then 0 else 1))) w ∧ w.pc = pcOf (b + 41) ∧
      LeafInv s0 A (j + 1) (if A.so then (st.1, st.2 ++ [v]) else (st.1 ++ [last], st.2 ++ [v])) w ∧
      Frame u w (fun X => slot j ≤ X ∧ X < slot j + 16) := by
  have hn : A.n = 58 ∨ A.n = 43 := chainCount_cases A.lay
  have hvs := hpre.hvs
  have hvb := hpre.hv
  have hv8 := hpre.hv8
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r31 : u.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [hur.get (by simp [chainRegs]), g _ (by simp [leafRegs]), hpre.x31]
  obtain ⟨u1, st1, u1pc, u1r, u1f⟩ := sub79_spec hsub u hupc A.so r31
  -- the end slot (`so = false`)
  obtain ⟨u2, st2, u2pc, u2r, u2f, u2s⟩ : ∃ u2, Steps image u1 (if A.so then 0 else 11 + (if j = 0 then 0 else 1))
      (if A.so then 0 else 11 + (if j = 0 then 0 else 1)) u2 ∧ u2.pc = pcOf (b + 92) ∧
      RegsExcept u1 u2 [.x6, .x7, .x28, .x29] ∧
      Frame u1 u2 (fun X => slot j ≤ X ∧ X < slot j + 16) ∧
      (A.so = false → DigAt u2 (slot j) last) := by
    cases hso : A.so
    · rw [hso, if_neg (by simp)] at u1pc
      have r19 : u1.getReg .x19 = BitVec.ofNat 64 j := by
        rw [u1r.get (by simp), hur.get (by simp [chainRegs])]; exact ht.x19
      obtain ⟨u3, st3, u3pc, u3x28, u3r, u3f⟩ := sub80_spec hsub u1 u1pc j (by omega) r19
      have hl1 : DigAt u1 (CHAIN + 48) last := hl.frame u1f (by decide) (by simp) (by simp)
      by_cases hj0 : j = 0
      · subst hj0
        rw [if_pos rfl] at u3pc
        obtain ⟨u4, st4, u4pc, u4a, u4b, u4r, u4f⟩ := sub83_spec hsub u3 u3pc (16 * 0) (by omega)
          (by decide) u3x28
        refine ⟨u4, by simpa using st3.trans st4, u4pc, (u3r.trans u4r).mono (by simp),
          (u3f.trans u4f).mono (fun X _ h => by simp [slot] at h ⊢; omega), fun _ => ?_⟩
        have hl3 := hl1.frame u3f (by decide) (by simp) (by simp)
        exact ⟨by rw [show slot 0 = LEAFPK + 16 * 0 from rfl, u4a]; exact hl3.1,
          by rw [show slot 0 + 8 = LEAFPK + 16 * 0 + 8 from rfl, u4b]; exact hl3.2⟩
      · rw [if_neg hj0] at u3pc
        obtain ⟨u4, st4, u4pc, u4x28, u4r, u4f⟩ := sub82_spec hsub u3 u3pc (16 * j) u3x28
        obtain ⟨u5, st5, u5pc, u5a, u5b, u5r, u5f⟩ := sub83_spec hsub u4 u4pc (16 * j + 16) (by omega)
          (by sc_omega) u4x28
        have hs : slot j = LEAFPK + (16 * j + 16) := by simp only [slot, if_neg hj0]; ring
        refine ⟨u5, by simpa [hj0] using st3.trans (st4.trans st5), u5pc,
          ((u3r.trans u4r).trans u5r).mono (by simp),
          ((u3f.trans u4f).trans u5f).mono (fun X _ h => by rw [hs]; simp at h ⊢; omega), fun _ => ?_⟩
        have hl4 := hl1.frame (u3f.trans u4f) (by decide) (by simp) (by simp)
        exact ⟨by rw [hs, u5a]; exact hl4.1, by rw [hs, u5b]; exact hl4.2⟩
    · rw [hso, if_pos rfl] at u1pc
      exact ⟨u1, by simpa using Steps.refl u1, u1pc, RegsExcept.refl _ _, Frame.refl _ _,
        fun h => by simp at h⟩
  have r19' : u2.getReg .x19 = BitVec.ofNat 64 j := by
    rw [u2r.get (by simp), u1r.get (by simp), hur.get (by simp [chainRegs])]; exact ht.x19
  have r23' : u2.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j) := by
    rw [u2r.get (by simp), u1r.get (by simp), hur.get (by simp [chainRegs])]; exact ht.x23
  obtain ⟨w, st6, wpc, wx19, wx23, wr, wf⟩ := sub92_spec hsub u2 u2pc j (A.valp + 16 * j) r19' r23'
  have hslot : ∀ c, c < A.n → LEAFPK ≤ slot c ∧ slot c + 16 ≤ LEAFPK + 16 * (A.n + 1) := by
    intro c hc; unfold slot; split_ifs <;> constructor <;> omega
  have hsj := hslot j hj
  have ftw : Frame t w (fun X => ((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
      (slot j ≤ X ∧ X < slot j + 16)) :=
    (((huf.trans u1f).trans u2f).trans wf).mono (fun X _ h => by
      rcases h with ((h | h) | h) | h
      · exact Or.inl h
      · exact h.elim
      · exact Or.inr h
      · exact h.elim)
  have fuw : Frame u w (fun X => slot j ≤ X ∧ X < slot j + 16) :=
    ((u1f.trans u2f).trans wf).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact h
      · exact h.elim)
  refine ⟨w, ?_, wpc, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fuw⟩
  · have := st1.trans (st2.trans st6)
    refine Steps.of_eq this ?_ ?_ <;> split_ifs <;> simp_all <;> omega
  · rw [wx19]
  · rw [wx23, show A.valp + 16 * j + 16 = A.valp + 16 * (j + 1) by ring]
  · rw [wr.get (by simp), u2r.get (by simp), u1r.get (by simp), hur.get (by simp [chainRegs])]; exact ht.x3
  · exact ((ht.regs.trans hur).trans ((u1r.trans u2r).trans wr)).mono (by decide)
  · refine (ht.frame.trans ftw).mono (fun X _ h => ?_)
    rcases h with h | ((h | h) | h)
    · exact h
    · exact LeafW_of_c48 h
    · exact LeafW_of_chainW hj h
    · exact LeafW_of_slot hj h
  · have := slot_hdr j
    rw [ftw.get (by decide) (by unfold ChainW; sc_omega), ht.w24]
  · have := slot_hdr j
    rw [ftw.get (by decide) (by unfold ChainW; sc_omega), ht.lh16]
  · have := slot_hdr j
    rw [ftw.get (by decide) (by unfold ChainW; sc_omega), ht.lh24]
  · have := ht.elen; split_ifs at this ⊢ with hso <;> simp_all
  · have := ht.vlen; split_ifs <;> simp_all
  · intro hso c hc
    rw [if_neg (by simp [hso])]
    simp only
    have hlen : st.1.length = j := by have := ht.elen; simpa [hso] using this
    by_cases hcj : c = j
    · subst hcj
      have hl5 : DigAt w (slot c) last :=
        (u2s hso).frame wf (by have := hsj; simp only [LEAFPK] at this; omega) (by simp) (by simp)
      simpa [List.getD_eq_getElem?_getD, hlen] using hl5
    · have hc' : c < j := by omega
      have hsc := slot_lt (show c < A.n by omega)
      have hsc0 := slot_ge c
      have hd := slot_disj hcj
      have hnot : ∀ X, slot c ≤ X → X < slot c + 16 →
          ¬ (((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
            (slot j ≤ X ∧ X < slot j + 16)) := by
        intro X h1 h2 h
        unfold ChainW at h
        sc_omega
      have hb64 : slot c + 8 < 2 ^ 64 := by
        have := hsc; simp only [LEAFPK] at this; omega
      have h2 : DigAt w (slot c) (st.1.getD c 0) :=
        (ht.ends hso c hc').frame ftw hb64 (hnot _ le_rfl (by omega)) (hnot _ (by omega) (by omega))
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : c < st.1.length)] using h2
  · have hsj0 := slot_ge j
    have hvw : DigAt w (A.valp + 16 * j) v :=
      hv.frame fuw (by omega) (by sc_omega) (by sc_omega)
    have hvals : DigsAt w A.valp st.2 :=
      ht.vals.frame ftw (by rw [ht.vlen]; omega) (fun X h1 h2 h => by
        rw [ht.vlen] at h2
        unfold ChainW at h
        sc_omega)
    have := hvals.snoc (d := v) (by rw [ht.vlen]; exact hvw)
    split_ifs <;> exact this

/-- One chain `j` from the seed copy (offset 60) to the next loop head. -/
theorem leaf_iterS {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 60)) (seed : Digest)
    (hseed : DigAt t (SEEDS + 16 * (j % 2)) seed) :
    TSim image sk t (A.iterK j) (A.iterC j) (A.e j) (A.e j) (halfUpd A st <$> chainProg A j seed)
      (fun st' u => u.pc = pcOf (b + 41) ∧ LeafInv s0 A (j + 1) st' u ∧
        Frame t u (fun X => X = CHAIN + 16 ∨ (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨
          (slot j ≤ X ∧ X < slot j + 16) ∨ (A.valp + 16 * j ≤ X ∧ X < A.valp + 16 * j + 16))) := by
  obtain ⟨u0, st0, u0pc, hcp, hcs, u0r, u0f⟩ := leaf_prechainS hsub sk hpre hj ht hpc seed hseed
  have hch := chainRun_tsim hsub sk hcp u0pc seed hcs
  rw [map_eq_bind_pure_comp]
  refine (TSim.steps st0 (TSim.bind (k₂ := 4 + (if A.so then 0 else 11 + (if j = 0 then 0 else 1)))
    (c₂ := 4 + (if A.so then 0 else 11 + (if j = 0 then 0 else 1))) (n₂ := 0) (b₂ := 0) hch
    (fun r u hu => ?_))).of_eq (by unfold chainProg; rfl) ?_ ?_ ?_ ?_
  · obtain ⟨hupc, hv, hl, hur, huf⟩ := hu
    obtain ⟨w, stw, wpc, hw, hfw⟩ := leaf_postchainS hsub sk hpre hj ht hupc (u0r.trans hur)
      (u0f.trans huf) r.1 r.2 hv hl
    refine TSim.pure_steps stw ⟨wpc, by simpa [halfUpd] using hw, ?_⟩
    refine ((u0f.trans huf).trans hfw).mono (fun X _ h => ?_)
    unfold ChainW at h
    rcases h with ((h | h) | h | h | h) | h
    · right; left; simp only [CHAIN] at h ⊢; omega
    · right; left; simp only [CHAIN] at h ⊢; omega
    · left; exact h
    · right; left; exact h
    · right; right; right; exact h
    · right; right; left; exact h
  all_goals (try unfold LeafArgs.iterK); (try unfold LeafArgs.iterC)
  all_goals first | omega | (split_ifs <;> omega)

/-- The PRF query of pair `p` (chain `2p` even): from the loop head, 18 steps and one HASH; the
continuation starts at the seed copy with the answer at `SEEDS`. -/
theorem leaf_prfS {p : Nat} (hp : 2 * p < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A (2 * p) st t) (hpc : t.pc = pcOf (b + 41)) {β : Type} {f : Digest × Digest → T3.M β}
    {k c n bl : Nat} {Q : β → MachineState → Prop}
    (hk : ∀ a : BitVec 256, ∀ u, LeafInv s0 A (2 * p) st u → u.pc = pcOf (b + 60) →
      DigAt u SEEDS (a.extractLsb' 0 128) → DigAt u (SEEDS + 16) (a.extractLsb' 128 128) →
      TSim image sk u k c n bl (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TSim image sk t (19 + k) (26 + c) (1 + n) (1 + bl)
      (privatePair 0 A.lay.val A.tree p A.leaf >>= f) Q := by
  have hn : A.n = 58 ∨ A.n = 43 := chainCount_cases A.lay
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [g _ (by simp [leafRegs]), hpre.x26]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec hsub t hpc (2 * p) A.n (by omega) (by omega) ht.x19 r26
  rw [if_pos hp] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub42_spec hsub t1 t1pc (2 * p) (by rw [t1r.get (by simp)]; exact ht.x19)
  rw [if_pos (by omega)] at t2pc
  have e12 : RegsExcept t t2 [.x6] := (t1r.trans t2r).mono (by simp)
  have hlay : A.lay.val < 256 := by have := A.lay.isLt; omega
  obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3a, t3b, t3r, t3f⟩ := sub44_spec hsub t2 t2pc A.lay.val A.tree
    A.leaf (2 * p) hlay hpre.htree hpre.hleaf (by omega)
    (by rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x8])
    (by rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x9])
    (by rw [e12.get (by simp), g _ (by simp [leafRegs]), hpre.x18])
    (by rw [e12.get (by simp)]; exact ht.x19)
  rw [show 2 * p / 2 = p by omega] at t3a
  have f13 : Frame t t3 (fun X => X = PRIV + 16 ∨ X = PRIV + 24) :=
    ((t1f.trans t2f).trans t3f).mono (fun X _ h => by rcases h with (h | h) | h <;> simp_all)
  have r13 : RegsExcept t t3 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (e12.trans t3r).mono (by simp)
  have hLP : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → ¬ LeafW A X := by
    intro X hX hw
    have := hpre.hvs; have := hpre.hds; have := hpre.hdv
    unfold LeafW at hw
    sc_omega
  have fr : ∀ X, (X = PRIV ∨ X = PRIV + 8 ∨ X = PRIV + 32 ∨ X = PRIV + 40 ∨ X = PRIV + 48 ∨
      X = PRIV + 56) → t3.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX =>
    (f13.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide))
      (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide))).trans
      (ht.frame.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; decide)) (hLP X hX))
  have hq : hashInput t3 = toQ (privateInput sk (.inl (header 0 A.lay.val A.tree p A.leaf))) := by
    refine hashInput_toQ t3 _ 0 PRIV (privateInput_tweak_length _ _) t3x10 (by decide) (by decide) t3x11
      (by decide) ?_
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, fr PRIV (by simp),
      fr (PRIV + 8) (by simp), t3a, t3b, fr (PRIV + 32) (by simp), fr (PRIV + 40) (by simp),
      fr (PRIV + 48) (by simp), fr (PRIV + 56) (by simp), hpre.p0, hpre.p8, hpre.p32, hpre.p40,
      hpre.p48, hpre.p56]
    rfl
  have hv : hashArgumentsValid t3 = true :=
    hashArgs_const t3 PRIV 64 SEEDS t3x10 t3x11 t3x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t3.getReg .x5 = 0 := by rw [r13.get (by simp), g _ (by simp [leafRegs]), hpre.x5]
  refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.privatePair_bind (k := k) (c := c) (n := n) (b := bl)
    (fetch_sub59 hsub t3 t3pc) h5 hv hq (fun a => ?_))).of_eq rfl (by omega) (by omega) rfl rfl
  have hwf := Frame.writeHash t3 a SEEDS t3x12 (by decide)
  refine hk a (writeHash t3 a) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by rw [pc_writeHash, t3pc,
    pcOf_add4]) (DigAt.writeHash_lo t3 a SEEDS t3x12 (by decide))
    (DigAt.writeHash_hi t3 a SEEDS t3x12 (by decide))
  · rw [getReg_writeHash, r13.get (by simp)]; exact ht.x19
  · rw [getReg_writeHash, r13.get (by simp)]; exact ht.x23
  · rw [getReg_writeHash, r13.get (by simp)]; exact ht.x3
  · have hw0 : RegsExcept t3 (writeHash t3 a) [] := fun r _ => getReg_writeHash t3 a r
    exact ((ht.regs.trans r13).trans hw0).mono (by decide)
  · refine (ht.frame.trans (f13.trans hwf)).mono (fun X _ h => ?_)
    unfold LeafW at *
    rcases h with h | (h | h) | h
    · exact h
    · left; exact h
    · right; left; exact h
    · right; right; left; simp only [SEEDS] at h ⊢; omega
  · rw [(f13.trans hwf).get (by decide) (by simp only [CHAIN, PRIV, SEEDS]; omega), ht.w24]
  · rw [(f13.trans hwf).get (by decide) (by simp only [LEAFPK, PRIV, SEEDS]; omega), ht.lh16]
  · rw [(f13.trans hwf).get (by decide) (by simp only [LEAFPK, PRIV, SEEDS]; omega), ht.lh24]
  · exact ht.elen
  · exact ht.vlen
  · intro hso c hc
    have h1 := slot_ge c
    have h2 := slot_lt (show c < A.n by omega)
    exact (ht.ends hso c hc).frame (f13.trans hwf) (by sc_omega) (by sc_omega) (by sc_omega)
  · have hvs := hpre.hvs
    have hvb := hpre.hv
    exact ht.vals.frame (f13.trans hwf) (by rw [ht.vlen]; omega) (fun X h1 h2 => by
      rw [ht.vlen] at h2; sc_omega)

/-- The head of an odd chain `2p + 1 < N`: the loop test and the parity test (3 steps). -/
theorem leaf_oddS {j : Nat} (hj : j < A.n) (hodd : j % 2 = 1) {st : List Digest × List Digest}
    {t : MachineState} (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 41)) :
    ∃ u, Steps image t 3 3 u ∧ u.pc = pcOf (b + 60) ∧ LeafInv s0 A j st u ∧ Frame t u (fun _ => False) := by
  have hn : A.n = 58 ∨ A.n = 43 := chainCount_cases A.lay
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [ht.regs.get (by simp [leafRegs]), hpre.x26]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec hsub t hpc j A.n (by omega) (by omega) ht.x19 r26
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub42_spec hsub t1 t1pc j (by rw [t1r.get (by simp)]; exact ht.x19)
  rw [if_neg (by omega)] at t2pc
  have r12 : RegsExcept t t2 [.x6] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  refine ⟨t2, st1.trans st2, t2pc, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ht.elen, ht.vlen, ?_, ?_⟩, f12⟩
  · rw [r12.get (by simp)]; exact ht.x19
  · rw [r12.get (by simp)]; exact ht.x23
  · rw [r12.get (by simp)]; exact ht.x3
  · exact (ht.regs.trans r12).mono (by decide)
  · exact (ht.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  · rw [f12.get (by decide) (by simp)]; exact ht.w24
  · rw [f12.get (by decide) (by simp)]; exact ht.lh16
  · rw [f12.get (by decide) (by simp)]; exact ht.lh24
  · intro hso c hc
    have h1 := slot_ge c; have h2 := slot_lt (show c < A.n by omega)
    exact (ht.ends hso c hc).frame f12 (by sc_omega) (by simp) (by simp)
  · exact ht.vals.frame f12 (by rw [ht.vlen]; have := hpre.hv; omega) (fun X _ _ => by simp)

/-- One pair `p` (`2p < N`): the PRF query, chain `2p`, and chain `2p+1` if it exists. -/
theorem leaf_pairS {p : Nat} (hp : 2 * p < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A (2 * p) st t) (hpc : t.pc = pcOf (b + 41)) :
    TSim image sk t (A.pairK p) (A.pairC p) (A.pairN p) (A.pairN p)
      (privatePair 0 A.lay.val A.tree p A.leaf >>= fun seeds =>
        (List.range 2).foldlM (leafHalf A seeds p) st)
      (fun st' u => u.pc = pcOf (b + 41) ∧ LeafInv s0 A (min (2 * p + 2) A.n) st' u) := by
  have hn : A.n = 58 ∨ A.n = 43 := chainCount_cases A.lay
  have hfold : ∀ (seeds : Digest × Digest), (List.range 2).foldlM (leafHalf A seeds p) st =
      leafHalf A seeds p st 0 >>= fun st1 => leafHalf A seeds p st1 1 := by
    intro seeds; simp [List.range_succ, List.foldlM_append]
  have hd : ∀ i < A.n, A.so = false → A.d i ≤ 2 ^ width A.lay i - 1 := fun i hi => (hpre.hdigb i hi).2
  unfold LeafArgs.pairK LeafArgs.pairC LeafArgs.pairN
  refine (leaf_prfS hsub sk hpre hp ht hpc
    (k := A.iterK (2 * p) + (if 2 * p + 1 < A.n then 3 + A.iterK (2 * p + 1) else 0))
    (c := A.iterC (2 * p) + (if 2 * p + 1 < A.n then 3 + A.iterC (2 * p + 1) else 0))
    (n := A.e (2 * p) + (if 2 * p + 1 < A.n then A.e (2 * p + 1) else 0))
    (bl := A.e (2 * p) + (if 2 * p + 1 < A.n then A.e (2 * p + 1) else 0))
    (fun a u hu upc hlo hhi => ?_)).of_eq rfl (by omega) (by omega) (by omega) (by omega)
  rw [hfold, leafHalf_lt A _ p st 0 (by omega) (hd _ (by omega))]
  simp only [if_pos rfl]
  have h1 := leaf_iterS hsub sk hpre (j := 2 * p) (by omega) hu upc (a.extractLsb' 0 128)
    (by rw [show 2 * p % 2 = 0 by omega]; simpa using hlo)
  by_cases hq : 2 * p + 1 < A.n
  · simp only [if_pos hq]
    refine TSim.bind h1 (fun st1 w hw => ?_)
    obtain ⟨wpc, hw1, hwf⟩ := hw
    obtain ⟨x, stx, xpc, hx, xf⟩ := leaf_oddS hsub sk hpre hq (by omega) hw1 wpc
    rw [leafHalf_lt A _ p st1 1 hq (hd _ hq), if_neg (by omega)]
    have hhi' : DigAt x (SEEDS + 16 * ((2 * p + 1) % 2)) (a.extractLsb' 128 128) := by
      rw [show (2 * p + 1) % 2 = 1 by omega, Nat.mul_one]
      refine (hhi.frame hwf (by decide) ?_ ?_).frame xf (by decide) (by simp) (by simp)
      · have := slot_ge (2 * p); have := slot_lt hp; have := hpre.hvs
        simp only [CHAIN, SEEDS, LEAFPK, PRIV] at *; omega
      · have := slot_ge (2 * p); have := slot_lt hp; have := hpre.hvs
        simp only [CHAIN, SEEDS, LEAFPK, PRIV] at *; omega
    refine (TSim.steps stx ((leaf_iterS hsub sk hpre (j := 2 * p + 1) hq hx xpc _ hhi').mono
      (fun st2 y hy => ⟨hy.1, by rw [show min (2 * p + 2) A.n = 2 * p + 1 + 1 by omega]; exact hy.2.1⟩))).of_eq
      rfl (by omega) (by omega) (by omega) (by omega)
  · simp only [if_neg hq]
    rw [show (fun st1 => leafHalf A (a.extractLsb' 0 128, a.extractLsb' 128 128) p st1 1) =
      fun st1 => pure st1 from funext fun st1 => leafHalf_ge A _ p st1 1 (by omega), bind_pure]
    exact (h1.mono (fun st1 w hw => ⟨hw.1, by
      rw [show min (2 * p + 2) A.n = 2 * p + 1 by omega]; exact hw.2.1⟩)).of_eq rfl (by omega) (by omega)
      (by omega) (by omega)

omit hsub hpre in
/-- The leaf-pk input `end0 | T2 | end1 .. end(N-1)`, zero-padded. -/
theorem leafInput_wordsS (A : LeafArgs) (ends : List Digest) (hlen : ends.length = A.n) :
    wordsOf (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 A.lay.val A.tree 0 A.leaf) ++
        (ends.drop 1).flatMap (bytesLE 16))) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++
        [BitVec.ofNat 64 (hdr0 2 A.lay.val A.tree 0), BitVec.ofNat 64 (hdr1 A.tree A.leaf)] ++
        wordsOf ((ends.drop 1).flatMap (bytesLE 16)) ++ (if A.n = 58 then [0, 0] else []) := by
  have hn : A.n = 58 ∨ A.n = 43 := chainCount_cases A.lay
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (A.n - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  unfold pad64
  rw [List.length_append, List.length_append, bytesLE_length, bytesLE_length, hfl,
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length, hfl] <;> omega),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length] <;> omega),
    wordsOf_append _ _ (by simp only [bytesLE_length] <;> omega), wordsOf_header]
  rcases hn with h | h
  · rw [h, if_pos rfl]
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod]
    rw [show (List.replicate 16 0 : List UInt8) = List.replicate (8 * 2) 0 from rfl,
      wordsOf_replicate_zero]
    rfl
  · rw [h, if_neg (by decide)]
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, List.replicate_zero,
      wordsOf_nil, List.append_nil]
    simp [T3.packedNodeTag]

omit hsub hpre in
theorem leafInput_lengthS (A : LeafArgs) (ends : List Digest) (hlen : ends.length = A.n) :
    (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (header 2 A.lay.val A.tree 0 A.leaf) ++
        (ends.drop 1).flatMap (bytesLE 16))).length = 64 * leafBlocks A.lay := by
  have hn : A.n = 58 ∨ A.n = 43 := chainCount_cases A.lay
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (A.n - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  rw [pad64_length, List.length_append, List.length_append, bytesLE_length, bytesLE_length, hfl]
  unfold leafBlocks
  rcases hn with h | h <;> rw [show chainCount A.lay = A.n from rfl, h]

/-- The exit: the loop test, then (unless signature-only) the leaf-pk HASH and the copy to `DEST`,
then the return. -/
theorem leaf_exitS {st : List Digest × List Digest} {t : MachineState} (ht : LeafInv s0 A A.n st t)
    (hpc : t.pc = pcOf (b + 41)) :
    TSim image sk t (if A.so then 3 else 19) (if A.so then 3 else 18 + 8 * leafBlocks A.lay)
      (if A.so then 0 else 1) (if A.so then 0 else leafBlocks A.lay)
      (if A.so then pure (0, st.2) else (leafHash A.lay A.tree A.leaf st.1 >>= fun root => pure (root, st.2)))
      (fun r u => u.pc = pcOf A.ret ∧ (A.so = false → DigAt u A.dest r.1) ∧ DigsAt u A.valp r.2 ∧
        r.2.length = A.n ∧ u.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * A.n) ∧ RegsExcept s0 u leafRegs ∧
        Frame s0 u (LeafW A)) := by
  have hn : A.n = 58 ∨ A.n = 43 := chainCount_cases A.lay
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [g _ (by simp [leafRegs]), hpre.x26]
  have r31 : t.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [g _ (by simp [leafRegs]), hpre.x31]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec hsub t hpc A.n A.n (by omega) (by omega) ht.x19 r26
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub95_spec hsub t1 t1pc A.so (by rw [t1r.get (by simp)]; exact r31)
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  cases hso : A.so
  · -- the leaf hash
    rw [hso, if_neg (by simp)] at t2pc
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3r, t3f⟩ := sub96_spec hsub t2 t2pc A.n hn
      (by rw [e12.get (by simp)]; exact r26)
    have r13 : RegsExcept t t3 [.x6, .x10, .x11, .x12] := (e12.trans t3r).mono (by simp)
    have f13 : Frame t t3 (fun _ => False) := (f12.trans t3f).mono (fun X _ h => by simp_all)
    have hlen : st.1.length = A.n := by have := ht.elen; simpa [hso] using this
    have hends := ht.ends hso
    -- the leaf-pk block in memory
    have hw : t3.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks A.lay) =
        wordsOf (pad64 (bytesLE 16 (st.1.getD 0 0) ++ bytesLE 16 (header 2 A.lay.val A.tree 0 A.leaf) ++
          (st.1.drop 1).flatMap (bytesLE 16))) := by
      rw [leafInput_wordsS A st.1 hlen]
      have h0 : DigAt t3 LEAFPK (st.1.getD 0 0) :=
        (hends 0 (by omega)).frame f13 (by decide) (by simp) (by simp)
      have hrest : DigsAt t3 (LEAFPK + 32) (st.1.drop 1) := by
        intro c hc
        simp only [List.length_drop] at hc
        have hsl := slot_lt (show c + 1 < A.n by omega)
        simp only [LEAFPK] at hsl
        have := (hends (c + 1) (by omega)).frame f13 (by omega) (by simp) (by simp)
        simp only [slot, if_neg (show c + 1 ≠ 0 by omega)] at this
        rw [show LEAFPK + 32 + 16 * c = LEAFPK + 16 * (c + 1 + 1) by ring]
        simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
      have hhd : t3.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
          [BitVec.ofNat 64 (hdr0 2 A.lay.val A.tree 0), BitVec.ofNat 64 (hdr1 A.tree A.leaf)] := by
        rw [readWords_two, f13.get (by decide) (by simp), f13.get (by decide) (by simp), ht.lh16,
          show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, ht.lh24,
          hdr0_eq 2 A.lay.val A.tree 0 (by decide) (by have := A.lay.isLt; omega) hpre.htree (by decide)]
        first | rfl | (congr 2; omega)
      rcases hn with hn' | hn'
      · have ht0 := hpre.ztail hn'
        have hvs := hpre.hvs
        have hds := hpre.hds
        have hdv := hpre.hdv
        rw [hn'] at hvs hdv
        have hnw : ∀ X, (X = LEAFPK + 944 ∨ X = LEAFPK + 952) → ¬ LeafW A X := by
          intro X hX hw'
          unfold LeafW at hw'
          rw [hn'] at hw'
          sc_omega
        have hz : t3.readWords (BitVec.ofNat 64 (LEAFPK + 944)) 2 = [0, 0] := by
          rw [readWords_two, f13.get (by decide) (by simp), f13.get (by decide) (by simp),
            ht.frame.get (by decide) (hnw _ (Or.inl rfl)),
            ht.frame.get (by decide) (hnw _ (Or.inr rfl)), ht0.1, ht0.2]
        have hb : 8 * leafBlocks A.lay = 2 + (2 + (2 * (st.1.drop 1).length + 2)) := by
          simp only [List.length_drop, hlen, leafBlocks, show chainCount A.lay = A.n from rfl, hn']
        rw [hb, readWords_add, readWords_add, readWords_add, h0.words, hhd, hrest.words,
          show LEAFPK + 8 * 2 + 8 * 2 + 8 * (2 * (st.1.drop 1).length) = LEAFPK + 944 by
            simp only [List.length_drop, hlen, hn', LEAFPK], hz, if_pos hn']
        simp only [List.append_assoc]
      · have hb : 8 * leafBlocks A.lay = 2 + (2 + 2 * (st.1.drop 1).length) := by
          simp only [List.length_drop, hlen, leafBlocks, show chainCount A.lay = A.n from rfl, hn']
        rw [hb, readWords_add, readWords_add, h0.words, hhd, hrest.words, if_neg (by omega)]
        simp only [List.append_assoc, List.append_nil]
    have hl := leafInput_lengthS A st.1 hlen
    have hnb : leafBlocks A.lay = 15 ∨ leafBlocks A.lay = 11 := by
      unfold leafBlocks; rcases hn with h | h <;> rw [show chainCount A.lay = A.n from rfl, h] <;> simp
    have hq : hashInput t3 = toQ (pad64 (bytesLE 16 (st.1.getD 0 0) ++
        bytesLE 16 (header 2 A.lay.val A.tree 0 A.leaf) ++ (st.1.drop 1).flatMap (bytesLE 16))) := by
      refine hashInput_toQ t3 _ (leafBlocks A.lay - 1) LEAFPK (by rw [hl]; omega) t3x10 (by decide)
        (by decide) ?_ (by omega) (by rw [show 8 * (leafBlocks A.lay - 1 + 1) = 8 * leafBlocks A.lay by omega]; exact hw)
      rw [t3x11]; congr 1
      unfold leafBlocks; rcases hn with h | h <;> rw [show chainCount A.lay = A.n from rfl, h]
    have hblk : (toQ (pad64 (bytesLE 16 (st.1.getD 0 0) ++
        bytesLE 16 (header 2 A.lay.val A.tree 0 A.leaf) ++ (st.1.drop 1).flatMap (bytesLE 16)))).blocks =
        leafBlocks A.lay := by
      rw [blocks_toQ ⟨by rw [hl]; omega, by rw [hl]; omega⟩, hl]; omega
    have hv : hashArgumentsValid t3 = true := by
      refine hashArgs_const t3 LEAFPK (64 * leafBlocks A.lay) LOUT t3x10 ?_ t3x12 (by decide) (by omega)
        (by simp only [LEAFPK]; omega) (by decide) (by decide)
      rw [t3x11]; congr 1
      unfold leafBlocks; rcases hn with h | h <;> rw [show chainCount A.lay = A.n from rfl, h]
    have h5 : t3.getReg .x5 = 0 := by rw [r13.get (by simp), g _ (by simp [leafRegs]), hpre.x5]
    unfold leafHash
    refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.shortHash_bind (k := 7) (c := 7) (n := 0) (b := 0)
      (f := fun root => pure (root, st.2)) (fetch_sub105 hsub t3 t3pc) h5 hv hq (fun a => ?_))).of_eq rfl
      (by omega) (by rw [hblk]; omega) (by omega) (by rw [hblk]; omega)
    have hds := hpre.hds
    have hdv := hpre.hdv
    have hvs := hpre.hvs
    have hdb := hpre.hd
    have hd8 := hpre.hd8 hso
    have hwf := Frame.writeHash t3 a LOUT t3x12 (by decide)
    obtain ⟨u2, st5, u2pc, u2a, u2b, u2r, u2f⟩ := sub106_spec hsub (writeHash t3 a)
      (by rw [pc_writeHash, t3pc, pcOf_add4]) A.dest hd8 hdb (by sc_omega)
      (by rw [getReg_writeHash, r13.get (by simp), g _ (by simp [leafRegs]), hpre.x25])
    have hlo := DigAt.writeHash_lo t3 a LOUT t3x12 (by decide)
    obtain ⟨u3, st6, u3pc, u3r, u3f⟩ := sub112_spec hsub u2 u2pc A.ret
      (by rw [u2r.get (by simp), getReg_writeHash, r13.get (by simp)]; exact ht.x3)
    have fall : Frame t u3 (fun X => (LOUT ≤ X ∧ X < LOUT + 32) ∨ (X = A.dest ∨ X = A.dest + 8)) :=
      ((f13.trans hwf).trans (u2f.trans u3f)).mono (fun X _ h => by
        rcases h with (h | h) | (h | h)
        · exact h.elim
        · left; exact h
        · right; exact h
        · exact h.elim)
    refine TSim.pure_steps (st5.trans st6) ⟨u3pc, fun _ => ?_, ?_, ht.vlen, ?_, ?_, ?_⟩
    · have hd2 : DigAt u2 A.dest (a.extractLsb' 0 128) := ⟨u2a.trans hlo.1, by rw [u2b]; exact hlo.2⟩
      exact hd2.frame u3f (by omega) (by simp) (by simp)
    · have hvl := ht.vlen
      exact ht.vals.frame fall (by rw [hvl]; have := hpre.hv; omega) (fun X h1 h2 => by
        rw [hvl] at h2; sc_omega)
    · rw [u3r.get (by simp), u2r.get (by simp), getReg_writeHash, r13.get (by simp)]; exact ht.x23
    · have hw0 : RegsExcept t3 (writeHash t3 a) [] := fun r _ => getReg_writeHash t3 a r
      exact ((ht.regs.trans r13).trans ((hw0.trans u2r).trans u3r)).mono (by decide)
    · refine (ht.frame.trans fall).mono (fun X _ h => ?_)
      rcases h with h | h | h
      · exact h
      · unfold LeafW; right; right; right; right; right; right; right; left; exact h
      · unfold LeafW; right; right; right; right; right; right; right; right; right
        rcases h with h | h <;> omega
  · -- signature only: return
    rw [hso, if_pos rfl] at t2pc
    simp only [if_true]
    obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub112_spec hsub t2 t2pc A.ret (by rw [e12.get (by simp)]; exact ht.x3)
    refine TSim.pure_steps (st1.trans (st2.trans st3)) ⟨t3pc, fun h => by simp at h, ?_, ht.vlen, ?_, ?_, ?_⟩
    · have hvl := ht.vlen
      exact ht.vals.frame (f12.trans t3f) (by rw [hvl]; have := hpre.hv; omega) (fun X _ _ h => by simp_all)
    · rw [t3r.get (by simp), e12.get (by simp)]; exact ht.x23
    · exact (ht.regs.trans (e12.trans t3r)).mono (by decide)
    · exact (ht.frame.trans (f12.trans t3f)).mono (fun X _ h => by
        rcases h with h | h | h; exact h; exact h.elim; exact h.elim)

/-- **`build_leaf`** (any image holding the shared code at base `b`): from the entry (offset 27)
the machine refines Core's `buildLeaf A.lay A.tree A.leaf A.digits A.so` exactly and returns to
`A.ret` with the chain values at `A.valp` and (unless signature-only) the leaf root at `A.dest`. -/
theorem buildLeaf_tsimS (hpc : s0.pc = pcOf (b + 27)) :
    TSim image sk s0 A.leafK A.leafC A.leafN A.leafB (buildLeaf A.lay A.tree A.leaf A.digits A.so)
      (fun r t => t.pc = pcOf A.ret ∧ (A.so = false → DigAt t A.dest r.1) ∧ DigsAt t A.valp r.2 ∧
        r.2.length = A.n ∧ t.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * A.n) ∧ RegsExcept s0 t leafRegs ∧
        Frame s0 t (LeafW A)) := by
  have hn : A.n = 58 ∨ A.n = 43 := chainCount_cases A.lay
  have hlay : A.lay.val < 256 := by have := A.lay.isLt; omega
  obtain ⟨t1, st1, t1pc, t1x3, t1x19, t1c24, t1l24, t1l16, t1r, t1f⟩ :=
    sub27_spec hsub s0 hpc A.lay.val A.tree A.leaf hlay hpre.htree hpre.hleaf hpre.x8 hpre.x9 hpre.x18
  have h0 : LeafInv s0 A 0 ([], []) t1 := by
    refine ⟨t1x19, ?_, by rw [t1x3, hpre.x1], t1r.mono (by decide), t1f.mono (fun X _ h => ?_), t1c24, ?_,
      t1l24, by simp, rfl, fun _ c hc => absurd hc (by omega), DigsAt.nil _ _⟩
    · rw [t1r.get (by simp), hpre.x23]; simp
    · unfold LeafW; simp only [CHAIN, LEAFPK] at h ⊢; omega
    · rw [t1l16]
  rw [buildLeaf_unfold]
  refine (TSim.steps st1 (TSim.bind (k₂ := if A.so then 3 else 19)
    (c₂ := if A.so then 3 else 18 + 8 * leafBlocks A.lay) (n₂ := if A.so then 0 else 1)
    (b₂ := if A.so then 0 else leafBlocks A.lay) (TSim.foldlM_range ((A.n + 1) / 2) _ ([], [])
    (fun p st t => t.pc = pcOf (b + 41) ∧ LeafInv s0 A (min (2 * p) A.n) st t)
    A.pairK A.pairC A.pairN A.pairN (fun p hp st t ht => ?_) ⟨t1pc, by simpa using h0⟩)
    (fun st t ht => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · have h2p : 2 * p < A.n := by omega
    rw [show min (2 * p) A.n = 2 * p by omega] at ht
    exact (leaf_pairS hsub sk hpre h2p ht.2 ht.1).mono (fun st' u hu =>
      ⟨hu.1, by rw [show 2 * (p + 1) = 2 * p + 2 by ring]; exact hu.2⟩)
  · obtain ⟨tpc, hinv⟩ := ht
    rw [show min (2 * ((A.n + 1) / 2)) A.n = A.n by omega] at hinv
    exact leaf_exitS hsub sk hpre hinv tpc
  all_goals simp only [LeafArgs.leafK, LeafArgs.leafC, LeafArgs.leafN, LeafArgs.leafB]
  all_goals omega

end leaf

end SigGolfCandidate.T3M.Sign
