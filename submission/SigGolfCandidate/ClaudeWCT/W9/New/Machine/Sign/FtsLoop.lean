import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsChain

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
def pairBody (index c j : Nat) (word : WCT9.Rank) (p : Fin 4) (state : List Digest × List Digest) :
    M (List Digest × List Digest) := do
  let seeds ← privatePair 8 c index 0 (4 * j + p.val)
  (List.finRange 2).foldlM (WCT9.childHalf index c j word p seeds) state
theorem childRows_eq (index c j : Nat) (word : WCT9.Rank) :
    WCT9.childRows index c j word = (do
      let s1 ← pairBody index c j word 0 ([], [])
      let s2 ← pairBody index c j word 1 s1
      let s3 ← pairBody index c j word 2 s2
      pairBody index c j word 3 s3) := by
  simp only [WCT9.childRows, pairBody, show List.finRange 4 = [0, 1, 2, 3] from rfl, List.foldlM_cons,
    List.foldlM_nil, bind_assoc, bind_pure]
theorem childHalf_eq (index c j : Nat) (word : WCT9.Rank) (p : Fin 4) (seeds : Digest × Digest)
    (state : List Digest × List Digest) (h : Fin 2) (hh : 2 * p.val + h.val < 7) :
    WCT9.childHalf index c j word p seeds state h =
      (chainRest index c j (2 * p.val + h.val) (WCT9.digit word ⟨2 * p.val + h.val, hh⟩) 3
        [if h.val = 0 then seeds.1 else seeds.2] >>= fun r => pure (state.1 ++ [r.2], state.2 ++ [r.1])) := by
  have hd := WCT9.digit_le_three word ⟨2 * p.val + h.val, hh⟩
  rw [← chain3_eq _ _ _ _ _ hd]
  simp only [WCT9.childHalf, dif_pos hh, bind_assoc, pure_bind]
theorem childHalf_none (index c j : Nat) (word : WCT9.Rank) (p : Fin 4) (seeds : Digest × Digest)
    (state : List Digest × List Digest) (h : Fin 2) (hh : ¬ 2 * p.val + h.val < 7) :
    WCT9.childHalf index c j word p seeds state h = pure state := by
  simp only [WCT9.childHalf, dif_neg hh]
def bodyRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x26, .x28, .x29]
def bodyW (c : Nat) (A : Nat) : Prop :=
  (PRIVW + 16 ≤ A ∧ A < PRIVW + 32) ∨ (PAIRW ≤ A ∧ A < PAIRW + 32) ∨ (CHAINW + 16 ≤ A ∧ A < CHAINW + 32) ∨
    (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) ∨ (LEAFW ≤ A ∧ A < LEAFW + 128) ∨ (slotV c 0 ≤ A ∧ A < slotV c 7)
structure BodySt (sk : BitVec 256) (j index sel w : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIVW + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIVW + 56)) = 0
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
theorem BodySt.of {sk : BitVec 256} {j index sel w : Nat} {s t : MachineState} {W : Nat → Prop} {l : List Reg}
    (h : BodySt sk j index sel w s) (hr : RegsExcept s t l)
    (hl : .x5 ∉ l ∧ .x18 ∉ l ∧ .x22 ∉ l ∧ .x24 ∉ l ∧ .x25 ∉ l) (hf : Frame s t W)
    (hW : ¬ W PRIVW ∧ ¬ W (PRIVW + 8) ∧ ¬ W (PRIVW + 32) ∧ ¬ W (PRIVW + 40) ∧ ¬ W (PRIVW + 48) ∧
      ¬ W (PRIVW + 56) ∧ ¬ W CHAINW ∧ ¬ W (CHAINW + 8) ∧ ¬ W (CHAINW + 32) ∧ ¬ W (CHAINW + 40)) :
    BodySt sk j index sel w t := by
  obtain ⟨l5, l18, l22, l24, l25⟩ := hl
  obtain ⟨w0, w8, w32, w40, w48, w56, c0, c8, c32, c40⟩ := hW
  exact ⟨by rw [hr.get l5]; exact h.x5, by rw [hr.get l18]; exact h.x18, by rw [hr.get l22]; exact h.x22,
    by rw [hr.get l24]; exact h.x24, by rw [hr.get l25]; exact h.x25,
    by rw [hf.get (by ao) w0]; exact h.p0, by rw [hf.get (by ao) w8]; exact h.p8,
    by rw [hf.get (by ao) w32]; exact h.p32, by rw [hf.get (by ao) w40]; exact h.p40,
    by rw [hf.get (by ao) w48]; exact h.p48, by rw [hf.get (by ao) w56]; exact h.p56,
    by rw [hf.get (by ao) c0]; exact h.z0, by rw [hf.get (by ao) c8]; exact h.z8,
    by rw [hf.get (by ao) c32]; exact h.z32, by rw [hf.get (by ao) c40]; exact h.z40⟩
structure RowsAt (c j sel n : Nat) (rows : List Digest × List Digest) (t : MachineState) : Prop where
  len1 : rows.1.length = n
  len2 : rows.2.length = n
  leaf : ∀ i < n, DigAt t (LEAFW + leafOff i) (rows.1.getD i 0)
  sig : j = sel → ∀ i < n, DigAt t (slotV c i) (rows.2.getD i 0)
theorem leafOff_lt (i : Nat) (hi : i < 7) : leafOff i + 16 ≤ 128 := by unfold leafOff; split_ifs <;> omega
theorem leafOff_ne (i i' : Nat) (hi : i < 7) (hi' : i' < 7) (hne : i ≠ i') :
    leafOff i ≠ leafOff i' ∧ leafOff i ≠ leafOff i' + 8 ∧ leafOff i + 8 ≠ leafOff i' ∧ leafOff i + 8 ≠ leafOff i' + 8 := by
  unfold leafOff; split_ifs <;> omega
theorem hashInput_priv (t : MachineState) (sk : BitVec 256) {c index q : Nat} (hc : c < 9) (hidx : index < 2 ^ 32)
    (hq : q < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 PRIVW) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64)
    (p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64)
    (p16 : t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c))
    (p24 : t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * q))
    (p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64)
    (p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64)
    (p48 : t.getMem (BitVec.ofNat 64 (PRIVW + 48)) = 0) (p56 : t.getMem (BitVec.ofNat 64 (PRIVW + 56)) = 0) :
    hashInput t = toQ (privateInput sk (.inl (header 8 c index 0 q))) := by
  refine hashInput_of_words t _ 0 PRIVW (by rw [privateInput_tweak_length]) h10 (by ao) (by ao) h11 ?_
  rw [wordsOf_priv sk c index q (by omega) hidx hq]
  intro k hk
  interval_cases k
  · exact p0
  · exact p8
  · exact p16
  · exact p24
  · exact p32
  · exact p40
  · exact p48
  · exact p56
theorem slotV_lt (c i : Nat) (hi : i < 7) : slotV c i + 16 ≤ slotV c 7 := by unfold slotV; omega
theorem chainW_bodyW {c i A : Nat} (hi : i < 7) (h : chainW c i A) : bodyW c A := by
  have := leafOff_lt i hi
  have := slotV_lt c i hi
  unfold chainW at h; unfold bodyW
  rcases h with h | h | h | h | h | h
  · right; right; left; exact h
  · right; right; right; left; exact h
  · right; right; right; right; left; subst h; constructor <;> omega
  · right; right; right; right; left; subst h; constructor <;> omega
  · right; right; right; right; right; subst h; unfold slotV at *; constructor <;> omega
  · right; right; right; right; right; subst h; unfold slotV at *; constructor <;> omega
theorem BodySt.of_body {sk : BitVec 256} {j index sel w c : Nat} {s t : MachineState} {W : Nat → Prop} {l : List Reg}
    (hc : c < 9) (h : BodySt sk j index sel w s) (hr : RegsExcept s t l) (hl : ∀ r ∈ l, r ∈ bodyRegs) (hf : Frame s t W)
    (hW : ∀ A, W A → bodyW c A) : BodySt sk j index sel w t := by
  have nb : ∀ A, (A = PRIVW ∨ A = PRIVW + 8 ∨ A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ A = PRIVW + 48 ∨ A = PRIVW + 56 ∨
      A = CHAINW ∨ A = CHAINW + 8 ∨ A = CHAINW + 32 ∨ A = CHAINW + 40) → ¬ W A := by
    intro A hA hw
    have := hW A hw
    unfold bodyW slotV at this
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [PRIVW, PAIRW, CHAINW, LEAFW, SIG] at this <;> omega
  refine h.of hr ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩ hf
    ⟨nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp),
      nb _ (by simp), nb _ (by simp), nb _ (by simp), nb _ (by simp)⟩ <;>
    · have := hl _ m; simp [bodyRegs] at this
theorem RowsAt.frame {c j sel n : Nat} {rows : List Digest × List Digest} {s t : MachineState} {W : Nat → Prop}
    (h : RowsAt c j sel n rows s) (hc : c < 9) (hn : n ≤ 7) (hf : Frame s t W)
    (hW : ∀ i < n, ¬ W (LEAFW + leafOff i) ∧ ¬ W (LEAFW + leafOff i + 8) ∧ ¬ W (slotV c i) ∧ ¬ W (slotV c i + 8)) :
    RowsAt c j sel n rows t := by
  refine ⟨h.len1, h.len2, fun i hi => ?_, fun hjs i hi => ?_⟩
  · have := leafOff_lt i (by omega)
    exact (h.leaf i hi).frame hf (by ao) (hW i hi).1 (hW i hi).2.1
  · exact (h.sig hjs i hi).frame hf (by unfold slotV; ao) (hW i hi).2.2.1 (hW i hi).2.2.2
theorem RowsAt.snoc {c j sel n : Nat} {rows : List Digest × List Digest} {t : MachineState} {x y : Digest}
    (h : RowsAt c j sel n rows t) (hl : DigAt t (LEAFW + leafOff n) x) (hs : j = sel → DigAt t (slotV c n) y) :
    RowsAt c j sel (n + 1) (rows.1 ++ [x], rows.2 ++ [y]) t := by
  refine ⟨by simp [h.len1], by simp [h.len2], fun i hi => ?_, fun hjs i hi => ?_⟩
  · by_cases hin : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len1]; exact hin), ← List.getD_eq_getElem?_getD]
      exact h.leaf i hin
    · have : i = n := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len1]), h.len1, Nat.sub_self]; exact hl
  · by_cases hin : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len2]; exact hin), ← List.getD_eq_getElem?_getD]
      exact h.sig hjs i hin
    · have : i = n := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len2]), h.len2, Nat.sub_self]; exact hs hjs
theorem chainW_other {c i i' : Nat} (hc : c < 9) (hi : i < 7) (hi' : i' < 7) (hne : i' ≠ i) :
    ¬ chainW c i (LEAFW + leafOff i') ∧ ¬ chainW c i (LEAFW + leafOff i' + 8) ∧ ¬ chainW c i (slotV c i') ∧
      ¬ chainW c i (slotV c i' + 8) := by
  have h1 := leafOff_lt i hi
  have h2 := leafOff_lt i' hi'
  have h3 := leafOff_ne i' i hi' hi hne
  unfold chainW slotV
  refine ⟨?_, ?_, ?_, ?_⟩ <;> aoh
theorem preI_pI : ∀ c, c < 9 → ∀ p, p < 4 → preI c (2 * p) = pI c p + 20 := by decide +kernel
theorem pI_pos : ∀ c, c < 9 → ∀ p, p < 4 → 1 ≤ pI c p := by decide +kernel
def pairEnd (c p : Nat) : Nat := if p = 3 then lI c else pI c (p + 1)
def pairC : Nat := 19 + (8 + (chainC + chainC))
theorem childHalf_eq' (index c j : Nat) (word : WCT9.Rank) (p : Fin 4) (seeds : Digest × Digest)
    (state : List Digest × List Digest) (h : Fin 2) (i : Nat) (hi : 2 * p.val + h.val = i) (hi7 : i < 7) (d : Nat)
    (hd : WCT9.digit word ⟨i, hi7⟩ = d) (seed : Digest) (hseed : (if h.val = 0 then seeds.1 else seeds.2) = seed) :
    WCT9.childHalf index c j word p seeds state h =
      (chainRest index c j i d 3 [seed] >>= fun r => pure (state.1 ++ [r.2], state.2 ++ [r.1])) := by
  subst hi; subst hd; subst hseed
  exact childHalf_eq index c j word p seeds state h hi7
theorem halves_eq (index c j : Nat) (word : WCT9.Rank) (w : Nat)
    (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i) (p : Nat) (hp : p < 4) (seeds : Digest × Digest)
    (rows : List Digest × List Digest) :
    (List.finRange 2).foldlM (WCT9.childHalf index c j word ⟨p, hp⟩ seeds) rows =
      if p < 3 then
        (chainRest index c j (2 * p) (w / 4 ^ (2 * p) % 4) 3 [seeds.1] >>= fun r =>
          chainRest index c j (2 * p + 1) (w / 4 ^ (2 * p + 1) % 4) 3 [seeds.2] >>= fun r' =>
            pure (rows.1 ++ [r.2] ++ [r'.2], rows.2 ++ [r.1] ++ [r'.1]))
      else
        (chainRest index c j (2 * p) (w / 4 ^ (2 * p) % 4) 3 [seeds.1] >>= fun r =>
          pure (rows.1 ++ [r.2], rows.2 ++ [r.1])) := by
  rw [show List.finRange 2 = [0, 1] from rfl]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  rw [childHalf_eq' index c j word ⟨p, hp⟩ seeds rows 0 (2 * p) rfl (by omega) _ (hword ⟨2 * p, by omega⟩).symm
    seeds.1 rfl]
  simp only [bind_assoc, pure_bind]
  by_cases hp3 : p < 3
  · rw [if_pos hp3]
    refine bind_congr fun r => ?_
    rw [childHalf_eq' index c j word ⟨p, hp⟩ seeds _ 1 (2 * p + 1) rfl (by omega) _
      (hword ⟨2 * p + 1, by omega⟩).symm seeds.2 rfl]
  · rw [if_neg hp3]
    refine bind_congr fun r => ?_
    rw [childHalf_none index c j word ⟨p, hp⟩ seeds _ 1 (by simp; omega)]
section pair
variable {im : Image} {sk : BitVec 256}
theorem pair_unit (hcode : NewCodeAt im) {c p j index sel w : Nat} {word : WCT9.Rank} (hc : c < 9) (hp : p < 4)
    (hj : j < 128) (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i)
    {rows : List Digest × List Digest} {s : MachineState} (hpc : s.pc = pcOf (pI c p))
    (hb : BodySt sk j index sel w s) (hr : RowsAt c j sel (2 * p) rows s) :
    TBSim im sk s pairC (pairBody index c j word ⟨p, hp⟩ rows) (fun rows' t =>
      t.pc = pcOf (pairEnd c p) ∧ BodySt sk j index sel w t ∧ RowsAt c j sel (min (2 * p + 2) 7) rows' t ∧
        RegsExcept s t bodyRegs ∧ Frame s t (bodyW c) ∧
        (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
          t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A))) := by
  obtain ⟨t1, s1, e1, p1, x10, x11, x12, m16, m24, r1, f1⟩ :=
    step_P hcode hc hp s hpc hb.x18 hb.x22 (by omega)
  have hb1 : BodySt sk j index sel w t1 := hb.of_body hc r1 (by simp [bodyRegs]) f1 (fun A hA => by
    unfold bodyW; rcases hA with rfl | rfl <;> (left; constructor <;> ao))
  have hq := hashInput_priv t1 sk hc (by omega : index < 2 ^ 32) (by omega : 4 * j + p < 2 ^ 32) x10 x11 hb1.p0 hb1.p8
    m16 m24 hb1.p32 hb1.p40 hb1.p48 hb1.p56
  unfold pairBody
  refine (TBSim.steps s1 (TBSim.privatePair_bind' (W := chainC + chainC) e1 hb1.x5
    (hashArgs_const t1 PRIVW 64 PAIRW x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
    (fun a => ?_))).mono (by unfold pairC; omega) (fun _ _ h => h)
  set u := writeHash t1 a with hu
  have fu := Frame.writeHash t1 a PAIRW x12 (by ao)
  have sd0 : DigAt u PAIRW (a.extractLsb' 0 128) := DigAt.writeHash_lo t1 a PAIRW x12 (by ao)
  have sd1 : DigAt u (PAIRW + 16) (a.extractLsb' 128 128) := DigAt.writeHash_hi t1 a PAIRW x12 (by ao)
  have hbu : BodySt sk j index sel w u := hb1.of_body hc (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 u [])
    (by simp) fu (fun A hA => by unfold bodyW; right; left; exact hA)
  have hupc : u.pc = pcOf (preI c (2 * p)) := by
    rw [hu, pc_writeHash, p1, preI_pI c hc p hp, pcOf_add4]
  have fsu : Frame s u (bodyW c) := (f1.trans fu).mono (fun A _ hA => by
    unfold bodyW
    rcases hA with (rfl | rfl) | hA
    · left; constructor <;> ao
    · left; constructor <;> ao
    · right; left; exact hA)
  have rsu : RegsExcept s u bodyRegs := (r1.trans (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 u [])).mono
    (by simp [bodyRegs])
  have hru : RowsAt c j sel (2 * p) rows u := hr.frame hc (by omega) (f1.trans fu) (fun i hi => by
    have := leafOff_lt i (by omega)
    unfold slotV
    refine ⟨?_, ?_, ?_, ?_⟩ <;> aoh)
  have hpre1 : ChainPre c (2 * p) j index sel w (a.extractLsb' 0 128) u :=
    ⟨hupc, hbu.x5, hbu.x18, hbu.x22, hbu.x24, hbu.x25, by rw [show 2 * p % 2 = 0 by omega]; simpa using sd0,
      hbu.z0, hbu.z8, hbu.z32, hbu.z40⟩
  rw [halves_eq index c j word w hword p hp]
  split_ifs with hp3
  · refine (TBSim.bind (W₂ := chainC) (chain_unit hcode hc (by omega) hj hsel hidx hw hpre1)
      (fun r t ht => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨tpc, tleaf, tsig, tregs, tframe, tnos⟩ := ht
    have hnu : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
        u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun _ A hA h1 h2 =>
      (f1.trans fu).get hA (by unfold slotV at h1 h2; intro h'; rcases h' with (h' | h') | h' <;> aoh)
    have hbt : BodySt sk j index sel w t := hbu.of_body hc tregs (by simp [chainRegs, bodyRegs]) tframe
      (fun A hA => chainW_bodyW (by omega) hA)
    have sdt : DigAt t (PAIRW + 16 * ((2 * p + 1) % 2)) (a.extractLsb' 128 128) := by
      rw [show (2 * p + 1) % 2 = 1 by omega, Nat.mul_one]
      refine sd1.frame tframe (by ao) ?_ ?_ <;> (unfold chainW slotV; have := leafOff_lt (2 * p) (by omega); aoh)
    have hpre2 : ChainPre c (2 * p + 1) j index sel w (a.extractLsb' 128 128) t :=
      ⟨by rw [tpc]; unfold lcEnd; rw [if_neg (by omega), if_pos (by omega)], hbt.x5, hbt.x18, hbt.x22, hbt.x24,
        hbt.x25, sdt, hbt.z0, hbt.z8, hbt.z32, hbt.z40⟩
    have hrt : RowsAt c j sel (2 * p + 1) (rows.1 ++ [r.2], rows.2 ++ [r.1]) t :=
      (hru.frame hc (by omega) tframe (fun i hi => chainW_other hc (by omega) (by omega) (by omega))).snoc tleaf tsig
    refine (TBSim.bind (W₂ := 0) (chain_unit hcode hc (by omega) hj hsel hidx hw hpre2) (fun r' t' ht' => ?_)).mono
      (by omega) (fun _ _ h => h)
    obtain ⟨tpc', tleaf', tsig', tregs', tframe', tnos'⟩ := ht'
    refine TBSim.pure ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tpc']; unfold lcEnd pairEnd
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (2 * p + 1 + 1) / 2 = p + 1 by omega]
    · exact hbt.of_body hc tregs' (by simp [chainRegs, bodyRegs]) tframe' (fun A hA => chainW_bodyW (by omega) hA)
    · rw [show min (2 * p + 2) 7 = 2 * p + 1 + 1 by omega]
      exact (hrt.frame hc (by omega) tframe' (fun i hi => chainW_other hc (by omega) (by omega) (by omega))).snoc
        tleaf' tsig'
    · exact ((rsu.trans tregs).trans tregs').mono (by simp [chainRegs, bodyRegs])
    · exact ((fsu.trans tframe).trans tframe').mono (fun A _ hA => by
        rcases hA with (hA | hA) | hA
        · exact hA
        · exact chainW_bodyW (by omega) hA
        · exact chainW_bodyW (by omega) hA)
    · intro hjs A hA h1 h2; rw [tnos' hjs A hA h1 h2, tnos hjs A hA h1 h2, hnu hjs A hA h1 h2]
  · have hp3' : p = 3 := by omega
    subst hp3'
    refine (TBSim.bind (W₂ := 0) (chain_unit hcode hc (by omega) hj hsel hidx hw hpre1) (fun r t ht => ?_)).mono
      (by omega) (fun _ _ h => h)
    obtain ⟨tpc, tleaf, tsig, tregs, tframe, tnos⟩ := ht
    have hnu : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
        u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun _ A hA h1 h2 =>
      (f1.trans fu).get hA (by unfold slotV at h1 h2; intro h'; rcases h' with (h' | h') | h' <;> aoh)
    refine TBSim.pure ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tpc]; unfold lcEnd pairEnd; rw [if_pos (by omega), if_pos rfl]
    · exact hbu.of_body hc tregs (by simp [chainRegs, bodyRegs]) tframe (fun A hA => chainW_bodyW (by omega) hA)
    · exact (hru.frame hc (by omega) tframe (fun i hi => chainW_other hc (by omega) (by omega) (by omega))).snoc
        tleaf tsig
    · exact (rsu.trans tregs).mono (by simp [chainRegs, bodyRegs])
    · exact (fsu.trans tframe).mono (fun A _ hA => by
        rcases hA with hA | hA
        · exact hA
        · exact chainW_bodyW (by omega) hA)
    · intro hjs A hA h1 h2; rw [tnos hjs A hA h1 h2, hnu hjs A hA h1 h2]
end pair
end ClaudeWCT.W9.Machine.Sign
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
theorem hashInput_leaf (t : MachineState) {c j index : Nat} (ends : List Digest) (hlen : ends.length = 7) (hc : c < 9)
    (hidx : index < 2 ^ 32) (hj : j < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 LEAFW)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 128) (he : ∀ i < 7, DigAt t (LEAFW + leafOff i) (ends.getD i 0))
    (m16 : t.getMem (BitVec.ofNat 64 (LEAFW + 16)) = BitVec.ofNat 64 (hdr6 c))
    (m24 : t.getMem (BitVec.ofNat 64 (LEAFW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * j)) :
    hashInput t = toQ (pad64 (leafIn index c j ends)) := by
  refine hashInput_of_words t _ 1 LEAFW (by rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ hlen]),
    leafIn_len _ _ _ _ hlen]) h10 (by ao) (by ao) h11 ?_
  rw [wordsOf_leaf index c j ends hlen (by omega) hidx hj]
  match ends, hlen with
  | [e0, e1, e2, e3, e4, e5, e6], _ =>
    have d0 := he 0 (by norm_num); have d1 := he 1 (by norm_num); have d2 := he 2 (by norm_num)
    have d3 := he 3 (by norm_num); have d4 := he 4 (by norm_num); have d5 := he 5 (by norm_num)
    have d6 := he 6 (by norm_num)
    simp only [leafOff, List.getD_cons_zero, List.getD_cons_succ] at d0 d1 d2 d3 d4 d5 d6
    simp only [if_true, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide,
      show (4 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 0 by decide, if_false,
      Nat.add_zero] at d0 d1 d2 d3 d4 d5 d6
    intro k hk
    interval_cases k <;> simp only [List.getD_cons_zero, List.drop_succ_cons, List.drop_zero, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, wordsOf_bytesLE16, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    · exact d0.1
    · exact d0.2
    · exact m16
    · exact m24
    · exact d1.1
    · exact d1.2
    · exact d2.1
    · exact d2.2
    · exact d3.1
    · exact d3.2
    · exact d4.1
    · exact d4.2
    · exact d5.1
    · exact d5.2
    · exact d6.1
    · exact d6.2
theorem leafI_pI : ∀ c, c < 9 → leafI c = pI c 0 := by decide +kernel
theorem tI_pos : ∀ c, c < 9 → 1 ≤ tI c := by decide +kernel
def childW (c j : Nat) (A : Nat) : Prop :=
  bodyW c A ∨ (HEAPW + 16 * (128 + j) ≤ A ∧ A < HEAPW + 16 * (128 + j) + 32)
def childC : Nat := 4 * pairC + (16 + (16 + 0))
section child
variable {im : Image} {sk : BitVec 256}
theorem child_unit (hcode : NewCodeAt im) {c j index sel w : Nat} {word : WCT9.Rank} (hc : c < 9) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64)
    (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i) {s : MachineState}
    (hpc : s.pc = pcOf (leafI c)) (hb : BodySt sk j index sel w s) :
    TBSim im sk s childC (WCT9.buildChild index c j word) (fun rv t =>
      t.pc = pcOf (tI c) ∧ BodySt sk j index sel w t ∧ DigAt t (HEAPW + 16 * (128 + j)) rv.1 ∧
        (j = sel → rv.2.length = 7 ∧ ∀ i < 7, DigAt t (slotV c i) (rv.2.getD i 0)) ∧
        RegsExcept s t bodyRegs ∧ Frame s t (childW c j) ∧
        (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
          t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A))) := by
  rw [WCT9.buildChild_factor, childRows_eq]
  simp only [bind_assoc]
  have h0 : RowsAt c j sel (2 * 0) ([], []) s := ⟨rfl, rfl, fun i hi => absurd hi (by omega), fun _ i hi => absurd hi (by omega)⟩
  have fw : ∀ {t1 t2 : MachineState}, Frame s t1 (bodyW c) → Frame t1 t2 (bodyW c) → Frame s t2 (bodyW c) :=
    fun f1 f2 => (f1.trans f2).mono (fun A _ hA => by rcases hA with hA | hA <;> exact hA)
  have rw' : ∀ {t1 t2 : MachineState}, RegsExcept s t1 bodyRegs → RegsExcept t1 t2 bodyRegs →
      RegsExcept s t2 bodyRegs := fun r1 r2 => (r1.trans r2).mono (by simp)
  refine (TBSim.bind (W₂ := 3 * pairC + (16 + (16 + 0)))
    (pair_unit hcode hc (by norm_num : 0 < 4) hj hsel hidx hw hword (by rw [hpc, leafI_pI c hc]) hb h0)
    (fun r1 t1 ht1 => ?_)).mono (by unfold childC; omega) (fun _ _ h => h)
  obtain ⟨p1, b1, rr1, g1, f1, n1⟩ := ht1
  refine (TBSim.bind (W₂ := 2 * pairC + (16 + (16 + 0)))
    (pair_unit hcode hc (by norm_num : 1 < 4) hj hsel hidx hw hword (by rw [p1]; rfl) b1 rr1)
    (fun r2 t2 ht2 => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p2, b2, rr2, g2, f2, n2⟩ := ht2
  refine (TBSim.bind (W₂ := pairC + (16 + (16 + 0)))
    (pair_unit hcode hc (by norm_num : 2 < 4) hj hsel hidx hw hword (by rw [p2]; rfl) b2 rr2)
    (fun r3 t3 ht3 => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p3, b3, rr3, g3, f3, n3⟩ := ht3
  refine (TBSim.bind (W₂ := 16 + (16 + 0))
    (pair_unit hcode hc (by norm_num : 3 < 4) hj hsel hidx hw hword (by rw [p3]; rfl) b3 rr3)
    (fun rows t4 ht4 => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p4, b4, rr4, g4, f4, n4⟩ := ht4
  have f14 : Frame s t4 (bodyW c) := fw (fw (fw f1 f2) f3) f4
  have g14 : RegsExcept s t4 bodyRegs := rw' (rw' (rw' g1 g2) g3) g4
  obtain ⟨t5, s5, e5, p5, x10, x11, x12, m16, m24, r5, f5⟩ :=
    step_L hcode hc t4 (by rw [p4]; rfl) b4.x18 b4.x22 (by omega)
  have hrows : RowsAt c j sel 7 rows t5 := rr4.frame hc (by norm_num) f5 (fun i hi => by
    have := leafOff_lt i (by omega)
    have := leafOff_ne i 1 (by omega) (by norm_num)
    unfold slotV leafOff at *
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs at * <;> aoh)
  have hq := hashInput_leaf t5 rows.1 hrows.len1 hc (by omega) (by omega) x10 x11 hrows.leaf m16 m24
  have hb5 : BodySt sk j index sel w t5 := b4.of_body hc r5 (by simp [bodyRegs]) f5 (fun A hA => by
    unfold bodyW; rcases hA with rfl | rfl <;> (right; right; right; right; left; constructor <;> ao))
  have hbl : (toQ (pad64 (leafIn index c j rows.1))).blocks = 2 := by
    rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ hrows.len1]),
      blocks_toQ ⟨by rw [leafIn_len _ _ _ _ hrows.len1]; norm_num, by rw [leafIn_len _ _ _ _ hrows.len1]⟩,
      leafIn_len _ _ _ _ hrows.len1]
  rw [leafHash_eq]
  refine (TBSim.steps s5 (TBSim.shortHash_bind' (W := 0) (f := fun root => pure (root, rows.2)) e5 hb5.x5
    (hashArgs_const t5 LEAFW 128 (HEAPW + 16 * (j + 128)) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao))
    hq (fun a => TBSim.pure ?_))).mono (by rw [hbl]; split <;> omega) (fun _ _ h => h)
  have fh := Frame.writeHash t5 a (HEAPW + 16 * (j + 128)) x12 (by ao)
  refine ⟨?_, ?_, ?_, fun hjs => ⟨by rw [hrows.len2], fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · rw [pc_writeHash, p5, pcOf_pred4 _ (tI_pos c hc)]
  · exact hb5.of (fun x _ => getReg_writeHash t5 a x : RegsExcept t5 (writeHash t5 a) []) (by simp) fh
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ao)
  · rw [show 128 + j = j + 128 by omega]; exact DigAt.writeHash_lo t5 a _ x12 (by ao)
  · exact (hrows.sig hjs i hi).frame fh (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
  · exact (g14.trans (r5.trans (fun x _ => getReg_writeHash t5 a x : RegsExcept t5 (writeHash t5 a) []))).mono
      (by simp [bodyRegs])
  · refine ((f14.trans f5).trans fh).mono (fun A _ hA => ?_)
    unfold childW
    rcases hA with (hA | hA) | hA
    · left; exact hA
    · left; unfold bodyW; rcases hA with rfl | rfl <;> (right; right; right; right; left; constructor <;> ao)
    · right; constructor <;> omega
  · intro hjs A hA h1 h2
    rw [fh.get hA (by unfold slotV at h1 h2; intro h'; aoh), f5.get hA (by unfold slotV at h1 h2; intro h'; aoh),
      n4 hjs A hA h1 h2, n3 hjs A hA h1 h2, n2 hjs A hA h1 h2, n1 hjs A hA h1 h2]
end child
end ClaudeWCT.W9.Machine.Sign
end

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
def loopW (c : Nat) (A : Nat) : Prop := bodyW c A ∨ (HEAPW + 16 * 128 ≤ A ∧ A < SCREND)
structure LoopInv (sk : BitVec 256) (c index sel w : Nat) (s0 : MachineState) (j : Nat)
    (acc : List Digest × List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if j < 128 then leafI c else nodeI c)
  body : BodySt sk (if j < 128 then j else 127) index sel w t
  len : acc.1.length = j
  leaves : ∀ j' < j, DigAt t (HEAPW + 16 * (128 + j')) (acc.1.getD j' 0)
  vals : sel < j → acc.2.length = 7 ∧ ∀ i < 7, DigAt t (slotV c i) (acc.2.getD i 0)
  nosig : j ≤ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
    t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)
  regs : RegsExcept s0 t (.x18 :: bodyRegs)
  frame : Frame s0 t (loopW c)
def loopStepC : Nat := childC + 4
theorem BodySt.with18 {sk : BitVec 256} {j j' index sel w : Nat} {u v : MachineState} (h : BodySt sk j index sel w u)
    (hr : RegsExcept u v [.x6, .x18]) (hf : Frame u v (fun _ => False)) (h18 : v.getReg .x18 = BitVec.ofNat 64 j') :
    BodySt sk j' index sel w v := by
  have g : ∀ A, A < 2 ^ 64 → v.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := fun A hA => hf.get hA id
  exact ⟨by rw [hr.get (by simp)]; exact h.x5, h18, by rw [hr.get (by simp)]; exact h.x22,
    by rw [hr.get (by simp)]; exact h.x24, by rw [hr.get (by simp)]; exact h.x25,
    by rw [g _ (by ao)]; exact h.p0, by rw [g _ (by ao)]; exact h.p8, by rw [g _ (by ao)]; exact h.p32,
    by rw [g _ (by ao)]; exact h.p40, by rw [g _ (by ao)]; exact h.p48, by rw [g _ (by ao)]; exact h.p56,
    by rw [g _ (by ao)]; exact h.z0, by rw [g _ (by ao)]; exact h.z8, by rw [g _ (by ao)]; exact h.z32,
    by rw [g _ (by ao)]; exact h.z40⟩
section loop
variable {im : Image} {sk : BitVec 256}
theorem child_step (hcode : NewCodeAt im) {c index sel w : Nat} {word : WCT9.Rank} (hc : c < 9) (hsel : sel < 128)
    (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i)
    {s0 : MachineState} (j : Nat) (hj : j < 128) (acc : List Digest × List Digest) (t : MachineState)
    (h : LoopInv sk c index sel w s0 j acc t) :
    TBSim im sk t loopStepC (do
        let (root, values) ← WCT9.buildChild index c j word
        pure (acc.1 ++ [root], if j = sel then values else acc.2)) (LoopInv sk c index sel w s0 (j + 1)) := by
  have hpc : t.pc = pcOf (leafI c) := by rw [h.pc, if_pos hj]
  have hb : BodySt sk j index sel w t := by have := h.body; rwa [if_pos hj] at this
  refine (TBSim.bind (W₂ := 4) (child_unit hcode hc hj hsel hidx hw hword hpc hb) (fun rv u hu => ?_)).mono
    (by unfold loopStepC; omega) (fun _ _ h => h)
  obtain ⟨root, values⟩ := rv
  obtain ⟨upc, ub, uroot, usel, uregs, uframe, unos⟩ := hu
  obtain ⟨v, k, sv, hk, vp1, vp2, vregs, vframe⟩ := step_T hcode hc hj u upc ub.x18
  refine TBSim.pure_steps' sv ?_ |>.mono hk (fun _ _ h => h)
  have hheap : ∀ A, A < 2 ^ 64 → v.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
    fun A hA => vframe.get hA (fun h => h)
  have fuv : Frame t v (childW c j) := (uframe.trans vframe).mono (fun A _ hA => by
    rcases hA with hA | hA
    · exact hA
    · exact hA.elim)
  refine ⟨?_, ?_, ?_, fun j' hj' => ?_, fun hs => ?_, fun hs A hA h1 h2 => ?_, ?_, ?_⟩
  · by_cases h1 : j + 1 < 128
    · rw [if_pos h1]; exact (vp1 h1).1
    · rw [if_neg h1]; exact (vp2 (by omega)).1
  · by_cases h1 : j + 1 < 128
    · rw [if_pos h1]; exact ub.with18 vregs vframe (vp1 h1).2
    · rw [if_neg h1]; exact ub.with18 vregs vframe (vp2 (by omega)).2
  · simp [h.len]
  · by_cases hlt : j' < j
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len]; exact hlt),
        ← List.getD_eq_getElem?_getD]
      refine (h.leaves j' hlt).frame fuv (by ao) ?_ ?_ <;> (unfold childW bodyW slotV; aoh)
    · have : j' = j := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len]), h.len, Nat.sub_self]
      exact uroot.frame vframe (by ao) (fun h => h) (fun h => h)
  · by_cases hjs : j = sel
    · subst hjs
      rw [if_pos rfl]
      obtain ⟨hl, hd⟩ := usel rfl
      exact ⟨hl, fun i hi => (hd i hi).frame vframe (by unfold slotV; ao) (fun h => h) (fun h => h)⟩
    · rw [if_neg hjs]
      obtain ⟨hl, hd⟩ := h.vals (by omega)
      refine ⟨hl, fun i hi => ⟨?_, ?_⟩⟩
      · rw [hheap _ (by unfold slotV; ao), unos hjs _ (by unfold slotV; ao) (by unfold slotV; omega)
          (by unfold slotV; omega)]
        exact (hd i hi).1
      · rw [hheap _ (by unfold slotV; ao), unos hjs _ (by unfold slotV; ao) (by unfold slotV; omega)
          (by unfold slotV; omega)]
        exact (hd i hi).2
  · rw [hheap A hA, unos (by omega) A hA h1 h2]; exact h.nosig (by omega) A hA h1 h2
  · exact (h.regs.trans (uregs.trans vregs)).mono (by simp [bodyRegs])
  · refine (h.frame.trans fuv).mono (fun A _ hA => ?_)
    unfold loopW
    rcases hA with hA | hA
    · exact hA
    · unfold childW at hA
      rcases hA with hA | hA
      · left; exact hA
      · right; constructor <;> aoh
theorem LoopInv.init {c index sel w : Nat} {s0 : MachineState} (hpc : s0.pc = pcOf (leafI c))
    (hb : BodySt sk 0 index sel w s0) : LoopInv sk c index sel w s0 0 ([], []) s0 :=
  ⟨by rw [if_pos (by norm_num)]; exact hpc, by rw [if_pos (by norm_num)]; exact hb, rfl,
    fun j' hj' => absurd hj' (by omega), fun h => absurd h (by omega), fun _ _ _ _ _ => rfl,
    RegsExcept.refl _ _, Frame.refl _ _⟩
theorem child_loop (hcode : NewCodeAt im) {c index sel w : Nat} {word : WCT9.Rank} (hc : c < 9) (hsel : sel < 128)
    (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i)
    {s0 : MachineState} (h0 : LoopInv sk c index sel w s0 0 ([], []) s0) :
    TBSim im sk s0 (128 * loopStepC) (WCT9.coordRows index ⟨c, hc⟩ ⟨sel, hsel⟩ word)
      (LoopInv sk c index sel w s0 128) := by
  unfold WCT9.coordRows
  rw [List.range_eq_range']
  exact TBSim.foldlM_range' 0 128 _ _ (LoopInv sk c index sel w s0) loopStepC
    (fun j hj acc t ht => by
      simp only [Nat.zero_add]
      exact child_step hcode hc hsel hidx hw hword j hj acc t ht) h0
end loop
def treeStep (index c : Nat) (nodes : Array Digest) (heap : Nat) : M (Array Digest) := do
  let value ← WCT9.wctNodeHash c index heap (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
  pure (nodes.set! heap value)
theorem heap_order_list : (List.range' 2 126).reverse = (List.range' 0 126).map (fun k => 127 - k) := by
  decide +kernel
theorem heapBuild_eq (index c : Nat) (leaves : List Digest) :
    WCT9.heapBuild index c leaves =
      (List.range' 0 126).foldlM (fun nodes k => treeStep index c nodes (127 - k))
        ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
  unfold WCT9.heapBuild
  rw [heap_order_list, List.foldlM_map]
  rfl
def treeRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x28, .x29]
def treeW (A : Nat) : Prop :=
  (A = NODEW ∨ A = NODEW + 8 ∨ A = NODEW + 16 ∨ A = NODEW + 24 ∨ A = NODEW + 48 ∨ A = NODEW + 56) ∨
    (NOUTW ≤ A ∧ A < NOUTW + 32) ∨ (HEAPW + 16 ≤ A ∧ A < HEAPW + 2048)
structure TreeInv (c index : Nat) (s0 : MachineState) (k : Nat) (nodes : Array Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 126 then nodeI c else rI c)
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 (127 - k)
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  size : nodes.size = 256
  heap : ∀ m, 127 - k < m → m < 256 → DigAt t (HEAPW + 16 * m) (nodes.getD m 0)
  z32 : t.getMem (BitVec.ofNat 64 (NODEW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (NODEW + 40)) = 0
  regs : RegsExcept s0 t (.x18 :: treeRegs)
  frame : Frame s0 t treeW
def treeC : Nat := 25 + (8 + 13)
theorem hashInput_node (t : MachineState) {c index h : Nat} {L R : Digest} (hc : c < 9) (hidx : index < 2 ^ 32)
    (hh : h < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 NODEW) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hL : DigAt t NODEW L) (m16 : t.getMem (BitVec.ofNat 64 (NODEW + 16)) = BitVec.ofNat 64 (nodeK c + 2 ^ 32 * index))
    (m24 : t.getMem (BitVec.ofNat 64 (NODEW + 24)) = BitVec.ofNat 64 h)
    (z32 : t.getMem (BitVec.ofNat 64 (NODEW + 32)) = 0) (z40 : t.getMem (BitVec.ofNat 64 (NODEW + 40)) = 0)
    (hR : DigAt t (NODEW + 48) R) : hashInput t = toQ (pad64 (nodeIn c index h L R)) := by
  refine hashInput_of_words t _ 0 NODEW (by rw [pad64_of_aligned _ (by rw [nodeIn_len]), nodeIn_len]) h10 (by ao)
    (by ao) h11 ?_
  rw [wordsOf_node c index h L R hc hidx hh]
  intro k hk
  interval_cases k
  · exact hL.1
  · exact hL.2
  · exact m16
  · exact m24
  · exact z32
  · exact z40
  · exact hR.1
  · exact hR.2
section tree
variable {im : Image} {sk : BitVec 256}
theorem tree_step (hcode : NewCodeAt im) {c index : Nat} (hc : c < 9) (hidx : index < 2 ^ 31) {s0 : MachineState}
    (k : Nat) (hk : k < 126) (nodes : Array Digest) (t : MachineState) (h : TreeInv c index s0 k nodes t) :
    TBSim im sk t treeC (treeStep index c nodes (127 - k)) (TreeInv c index s0 (k + 1)) := by
  have hpc : t.pc = pcOf (nodeI c) := by rw [h.pc, if_pos hk]
  obtain ⟨t1, s1, e1, p1, x10, x11, x12, n0, n8, n48, n56, n16, n24, r1, f1⟩ :=
    step_N hcode hc (by omega : 1 ≤ 127 - k) (by omega) t hpc h.x18 h.x22 (by omega)
  have hL : DigAt t1 NODEW (nodes.getD (2 * (127 - k)) 0) := by
    have := h.heap (2 * (127 - k)) (by omega) (by omega)
    exact ⟨by rw [n0, show HEAPW + 32 * (127 - k) = HEAPW + 16 * (2 * (127 - k)) by ring]; exact this.1,
      by rw [n8, show HEAPW + 32 * (127 - k) + 8 = HEAPW + 16 * (2 * (127 - k)) + 8 by ring]; exact this.2⟩
  have hR : DigAt t1 (NODEW + 48) (nodes.getD (2 * (127 - k) + 1) 0) := by
    have := h.heap (2 * (127 - k) + 1) (by omega) (by omega)
    exact ⟨by rw [n48, show HEAPW + 32 * (127 - k) + 16 = HEAPW + 16 * (2 * (127 - k) + 1) by ring]; exact this.1,
      by rw [show NODEW + 48 + 8 = NODEW + 56 by ao, n56,
        show HEAPW + 32 * (127 - k) + 24 = HEAPW + 16 * (2 * (127 - k) + 1) + 8 by ring]; exact this.2⟩
  have hz32 : t1.getMem (BitVec.ofNat 64 (NODEW + 32)) = 0 := by rw [f1.get (by ao) (by intro h'; aoh)]; exact h.z32
  have hz40 : t1.getMem (BitVec.ofNat 64 (NODEW + 40)) = 0 := by rw [f1.get (by ao) (by intro h'; aoh)]; exact h.z40
  have hq := hashInput_node t1 hc (by omega : index < 2 ^ 32) (by omega : 127 - k < 2 ^ 32) x10 x11 hL n16 n24 hz32 hz40 hR
  have hx5 : t1.getReg .x5 = 0 := by rw [r1.get (by simp)]; exact h.x5
  unfold treeStep
  rw [nodeHash_eq]
  refine (TBSim.steps s1 (TBSim.shortHash_bind' (W := 13) (f := fun value => pure (nodes.set! (127 - k) value)) e1 hx5
    (hashArgs_const t1 NODEW 64 NOUTW x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
    (fun a => ?_))).mono (by rw [blocks64 _ (nodeIn_len _ _ _ _ _)]; unfold treeC; omega) (fun _ _ h => h)
  set u := writeHash t1 a with hu
  have fu := Frame.writeHash t1 a NOUTW x12 (by ao)
  have hntpc : u.pc = pcOf (ntI c) := by
    rw [hu, pc_writeHash, p1]
    have : 1 ≤ ntI c := by have : ∀ c, c < 9 → 1 ≤ ntI c := by decide +kernel
                           exact this c hc
    exact pcOf_pred4 _ this
  have u18 : u.getReg .x18 = BitVec.ofNat 64 (127 - k) := by rw [hu, getReg_writeHash, r1.get (by simp)]; exact h.x18
  obtain ⟨t2, s2, q1, q2, x18', w0, w8, r2, f2⟩ := step_NT hcode hc (by omega : 2 ≤ 127 - k) (by omega) u hntpc u18
  have hout := DigAt.writeHash_lo t1 a NOUTW x12 (by ao)
  refine TBSim.pure_steps' s2 ⟨?_, ?_, ?_, ?_, ?_, fun m hm1 hm2 => ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hk1 : k + 1 < 126
    · rw [if_pos hk1]; exact q1 (by omega)
    · rw [if_neg hk1]; exact q2 (by omega)
  · rw [r2.get (by simp), hu, getReg_writeHash, r1.get (by simp)]; exact h.x5
  · rw [x18', show 127 - k - 1 = 127 - (k + 1) by omega]
  · rw [r2.get (by simp), hu, getReg_writeHash, r1.get (by simp)]; exact h.x22
  · simp [h.size]
  · by_cases hmk : m = 127 - k
    · subst hmk
      rw [WCT9.getD_set_self _ _ _ (by rw [h.size]; omega)]
      exact ⟨by rw [w0]; exact hout.1, by rw [w8]; exact hout.2⟩
    · rw [WCT9.getD_set_other _ _ _ _ (fun he => hmk he.symm)]
      have hd := h.heap m (by omega) hm2
      have g : ∀ A, (A = HEAPW + 16 * m ∨ A = HEAPW + 16 * m + 8) →
          t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
        intro A hA
        rw [f2.get (by aoh) (by intro h'; aoh), fu.get (by aoh) (by intro h'; aoh), f1.get (by aoh) (by intro h'; aoh)]
      exact ⟨by rw [g _ (Or.inl rfl)]; exact hd.1, by rw [g _ (Or.inr rfl)]; exact hd.2⟩
  · rw [f2.get (by ao) (by intro h'; aoh), fu.get (by ao) (by intro h'; aoh)]; exact hz32
  · rw [f2.get (by ao) (by intro h'; aoh), fu.get (by ao) (by intro h'; aoh)]; exact hz40
  · exact (h.regs.trans ((r1.trans (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 u [])).trans r2)).mono
      (by simp [treeRegs])
  · refine (((h.frame.trans f1).trans fu).trans f2).mono (fun A _ hA => ?_)
    unfold treeW
    rcases hA with ((hA | hA) | hA) | hA
    · exact hA
    · left; rcases hA with h' | h' | h' | h' | h' | h' <;> simp [h']
    · right; left; exact hA
    · right; right; rcases hA with rfl | rfl <;> constructor <;> omega
theorem tree_loop (hcode : NewCodeAt im) {c index : Nat} (hc : c < 9) (hidx : index < 2 ^ 31) {s0 : MachineState}
    {leaves : List Digest} (h0 : TreeInv c index s0 0 ((List.replicate 128 (0 : Digest) ++ leaves).toArray) s0) :
    TBSim im sk s0 (126 * treeC) (WCT9.heapBuild index c leaves) (TreeInv c index s0 126) := by
  rw [heapBuild_eq]
  exact TBSim.foldlM_range' 0 126 _ _ (TreeInv c index s0) treeC
    (fun k hk nodes t ht => by
      simp only [Nat.zero_add]
      exact tree_step hcode hc hidx k hk nodes t ht) h0
end tree
end ClaudeWCT.W9.Machine.Sign
end
