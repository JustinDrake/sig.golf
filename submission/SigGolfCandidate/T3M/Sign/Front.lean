import SigGolfCandidate.T3M.FullCache.MacRun
import SigGolfCandidate.T3M.Sign.FrontBlocks
import SigGolfCandidate.T3M.Sign.Kernels
import SigGolfCandidate.T3M.Sign.Init
import SigGolfCandidate.T3M.Sign.BaseInv

/-!
# Sign: the front (MAC check, nonce, digest search)

`sign cache m` = MAC check; `signPayload` = nonce, digest search, then `payloadRest` (FTS trees,
forest, layers, the signature). `sign_front`: from the loaded state the machine refines
`sign (cacheDec cache) m` given a refinement of `payloadRest` from every state `AfterDs` (word 172:
`N` at `NBUF`, the selection rows, `rho` in the signature, the private prefix at `PRIV`, everything
outside `FrontW` as loaded). A tampered cache (any MAC doubleword differs) and an exhausted digest
search end in `Failed` (value `none`).
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Digest HashOutput Cache Region Signature Selection sign signPayload signLayers
  privateMac privateNonce privateInput header digestSearch selections admissible attemptLimit buildFts frontier
  forestPk piecesSignature zero16)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## Core: `signPayload` after the digest search -/

/-- The rest of `signPayload` after a successful digest search with output `output`. -/
def payloadRest (cache : Cache) (rho : Digest) (output : HashOutput) : M (Option Signature) := do
  let index := output.toNat % 2^31
  let chosen := selections output
  let state ← (List.range 7).foldlM
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let opened := selected.map (fun s => secrets.getD s 0)
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
        state.2.2 ++ [(levels.getD 11 []).getD 0 0])) ([],[],[])
  let root ← forestPk index state.2.2
  let some layers ← signLayers cache index 4 root | pure none
  pure (some ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
    fun lay => piecesSignature lay (layers.getD lay.val ([],[]))⟩)

theorem signPayload_eq (cache : Cache) (m : T3.Message) :
    signPayload cache m = privateNonce m >>= fun rho => digestSearch rho m 0 attemptLimit >>= fun r =>
      match r with
      | none => pure none
      | some (_, output) => payloadRest cache rho output := by
  unfold signPayload payloadRest
  congr 1; funext rho; congr 1; funext r
  rcases r with _ | ⟨_, output⟩ <;> rfl

theorem sign_eq (cache : Cache) (m : T3.Message) :
    sign cache m = privateMac cache.region >>= fun tag =>
      if tag ≠ cache.tag then pure none else signPayload cache m := by
  rfl

/-! ## The state after the digest search -/

/-- Doublewords written by the front: the saved tag, the MAC block, the MAC output, `PRIV`, the
nonce block and output, `rho` in the signature, the digest block and output, the selection rows. -/
def FrontW (X : Nat) : Prop :=
  (TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64) ∨ (MACOUT ≤ X ∧ X < MACOUT + 32) ∨
    (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (RHOOUT ≤ X ∧ X < RHOOUT + 32) ∨
    (SIG ≤ X ∧ X < SIG + 16) ∨ (DIG ≤ X ∧ X < DIG + 64) ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨
    (SEL ≤ X ∧ X < SEL + 168) ∨ (0x70000 ≤ X ∧ X < 0x70040)

/-- At `ds_done` (word 172) after a successful digest search with output `N`. -/
structure AfterDs (sk : SecretKey) (cache : Bytes 131072) (m : Message) (rho : Digest) (N : HashOutput)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 172
  x5 : t.getReg .x5 = 0
  adm : admissible (selections N) = true
  nbuf : OutAt t NBUF N
  sel : SelRows t N
  rho : DigAt t SIG rho
  p0 : t.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  frame : Frame (sinit sk cache m) t FrontW

/-- `Base` at `ds_done`: the private prefix, the loaded region, and the never-written zeros. -/
theorem AfterDs.base {sk : SecretKey} {cache : Bytes 131072} {m : Message} {rho : Digest} {N : HashOutput}
    {t : MachineState} (h : AfterDs sk cache m rho N t) : Base sk cache t := by
  refine ⟨h.x5, h.p0, h.p8, h.p32, h.p40, h.p48, h.p56, fun k hk => ?_, fun A hA hn => ?_, ?_⟩
  · rw [h.frame.get (by sg_omega) (by unfold FrontW; sg_omega), show REGION + 8 * k = CACHE + 8 * (k + 4) by sg_omega,
      sinit_cache sk cache m (k + 4) (by omega)]
  · unfold NeverW at hn
    rw [h.frame.get hA (by unfold FrontW; sg_omega)]
    exact sinit_zero sk cache m A (by unfold Search.TOP_DATA; sg_omega) (by sg_omega)

  · exact (sinit_table sk cache m).frame h.frame (by
      intro i hi; unfold FrontW Search.TOP_DATA; sg_omega)

/-! ## Doubleword helpers (as in `Keygen.Main`, which sign does not import) -/

/-- Unchanged doublewords read the same. -/
theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]

/-- The 4,104 doublewords of the MAC input `S0 | T14 | S1 | 0^16 | region | 0^32`. -/
theorem wordsOf_mac' (sk : BitVec 256) (region : Region) :
    wordsOf (privateInput sk (.inr (.inr region))) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, BitVec.ofNat 64 3585, 0, sk.extractLsb' 128 64,
        sk.extractLsb' 192 64, 0, 0] ++ wordsOf (List.ofFn region) ++ [0, 0, 0, 0] := by
  obtain ⟨h1, h2, h3, h4⟩ := sk_words sk
  have l1 : (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0) ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++ List.ofFn region).length % 8 = 0 := by
    simp only [List.length_append, bytesLE_length, List.length_ofFn, zero16, List.length_replicate]
  have l2 : (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0) ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16).length % 8 = 0 := by
    simp only [List.length_append, bytesLE_length, zero16, List.length_replicate]
  have l3 : (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0) ++
      bytesLE 16 (sk.extractLsb' 128 128)).length % 8 = 0 := by
    simp only [List.length_append, bytesLE_length]
  have l4 : (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 (header 14 0 0 0 0)).length % 8 = 0 := by
    simp only [List.length_append, bytesLE_length]
  have l5 : (bytesLE 16 (sk.extractLsb' 0 128)).length % 8 = 0 := by simp only [bytesLE_length]
  rw [privateInput_mac_eq, wordsOf_append _ _ l1, wordsOf_append _ _ l2, wordsOf_append _ _ l3,
    wordsOf_append _ _ l4, wordsOf_append _ _ l5, wordsOf_bytesLE16, wordsOf_header, wordsOf_bytesLE16,
    wordsOf_zero16, show List.replicate 32 (0 : UInt8) = List.replicate (8 * 4) 0 from rfl,
    wordsOf_replicate_zero, h1, h2, h3, h4]
  rfl

/-! ## The MAC compare chain (words 47..62) -/

/-- The compare chain: equal tags reach word 63 in 16 cycles, unequal ones reach `fail`. -/
theorem cmp_chain (t : MachineState) (hpc : t.pc = pcOf 47) (a tag : BitVec 256)
    (ha : OutAt t MACOUT a) (ht : OutAt t TAG tag) :
    (a = tag → ∃ u, Steps image t 16 16 u ∧ u.pc = pcOf 63 ∧ RegsExcept t u [.x6, .x7, .x28, .x29] ∧
      Frame t u (fun _ => False)) ∧
    (a ≠ tag → ∃ u k c, Steps image t k c u ∧ c ≤ 16 ∧ u.pc = pcOf 543) := by
  have e : ∀ k < 4, (t.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = t.getMem (BitVec.ofNat 64 (TAG + 8 * k))) ↔
      a.extractLsb' (64 * k) 64 = tag.extractLsb' (64 * k) 64 := fun k hk => by rw [ha k hk, ht k hk]
  have hiff := bv256_eq_iff a tag
  obtain ⟨t1, s1, p1, x28, x29, r1, f1⟩ := blk47_spec t hpc
  have g : ∀ u, RegsExcept t u [.x6, .x7, .x28, .x29] → Frame t u (fun _ => False) →
      ∀ k < 4, (u.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = u.getMem (BitVec.ofNat 64 (TAG + 8 * k)) ↔
        a.extractLsb' (64 * k) 64 = tag.extractLsb' (64 * k) 64) := fun u _ hf k hk => by
    rw [hf.get (by sg_omega) (fun h => h), hf.get (by sg_omega) (fun h => h)]; exact e k hk
  have e0 := e 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at e0
  constructor
  · intro hat
    have h0 : a.extractLsb' 0 64 = tag.extractLsb' 0 64 := (hiff.1 hat).1
    rw [if_pos (e0.2 h0)] at p1
    have r1' : RegsExcept t t1 [.x6, .x7, .x28, .x29] := r1
    obtain ⟨t2, s2, p2, r2, f2⟩ := blk54_spec t1 p1 x28 x29
    rw [if_pos ((g t1 r1' f1 1 (by decide)).2 (hiff.1 hat).2.1)] at p2
    have r12 : RegsExcept t t2 [.x6, .x7, .x28, .x29] := (r1'.trans r2).mono (by decide)
    have f12 : Frame t t2 (fun _ => False) := (f1.trans f2).mono (fun _ _ h => by simp_all)
    obtain ⟨t3, s3, p3, r3, f3⟩ := blk57_spec t2 p2 (by rw [r2.get (by decide), x28]) (by rw [r2.get (by decide), x29])
    rw [if_pos ((g t2 r12 f12 2 (by decide)).2 (hiff.1 hat).2.2.1)] at p3
    have r13 : RegsExcept t t3 [.x6, .x7, .x28, .x29] := (r12.trans r3).mono (by decide)
    have f13 : Frame t t3 (fun _ => False) := (f12.trans f3).mono (fun _ _ h => by simp_all)
    obtain ⟨t4, s4, p4, r4, f4⟩ := blk60_spec t3 p3 (by rw [r3.get (by decide), r2.get (by decide), x28])
      (by rw [r3.get (by decide), r2.get (by decide), x29])
    rw [if_pos ((g t3 r13 f13 3 (by decide)).2 (hiff.1 hat).2.2.2)] at p4
    exact ⟨t4, (s1.trans s2).trans (s3.trans s4), p4, (r13.trans r4).mono (by decide),
      (f13.trans f4).mono (fun _ _ h => by simp_all)⟩
  · intro hne
    have r1' : RegsExcept t t1 [.x6, .x7, .x28, .x29] := r1
    by_cases h0 : a.extractLsb' 0 64 = tag.extractLsb' 0 64
    · rw [if_pos (e0.2 h0)] at p1
      obtain ⟨t2, s2, p2, r2, f2⟩ := blk54_spec t1 p1 x28 x29
      have r12 : RegsExcept t t2 [.x6, .x7, .x28, .x29] := (r1'.trans r2).mono (by decide)
      have f12 : Frame t t2 (fun _ => False) := (f1.trans f2).mono (fun _ _ h => by simp_all)
      by_cases h1 : a.extractLsb' 64 64 = tag.extractLsb' 64 64
      · rw [if_pos ((g t1 r1' f1 1 (by decide)).2 h1)] at p2
        obtain ⟨t3, s3, p3, r3, f3⟩ := blk57_spec t2 p2 (by rw [r2.get (by decide), x28])
          (by rw [r2.get (by decide), x29])
        have r13 : RegsExcept t t3 [.x6, .x7, .x28, .x29] := (r12.trans r3).mono (by decide)
        have f13 : Frame t t3 (fun _ => False) := (f12.trans f3).mono (fun _ _ h => by simp_all)
        by_cases h2 : a.extractLsb' 128 64 = tag.extractLsb' 128 64
        · rw [if_pos ((g t2 r12 f12 2 (by decide)).2 h2)] at p3
          obtain ⟨t4, s4, p4, -, -⟩ := blk60_spec t3 p3 (by rw [r3.get (by decide), r2.get (by decide), x28])
            (by rw [r3.get (by decide), r2.get (by decide), x29])
          have h3 : ¬ a.extractLsb' 192 64 = tag.extractLsb' 192 64 := fun h3 => hne (hiff.2 ⟨h0, h1, h2, h3⟩)
          rw [if_neg (fun h => h3 ((g t3 r13 f13 3 (by decide)).1 h))] at p4
          exact ⟨t4, _, _, (s1.trans s2).trans (s3.trans s4), le_refl _, p4⟩
        · rw [if_neg (fun h => h2 ((g t2 r12 f12 2 (by decide)).1 h))] at p3
          exact ⟨t3, _, _, (s1.trans s2).trans s3, by norm_num, p3⟩
      · rw [if_neg (fun h => h1 ((g t1 r1' f1 1 (by decide)).1 h))] at p2
        exact ⟨t2, _, _, s1.trans s2, by norm_num, p2⟩
    · rw [if_neg (fun h => h0 (e0.1 h))] at p1
      exact ⟨t1, _, _, s1, by norm_num, p1⟩

/-! ## The front -/

/-- Cycles of the front up to the digest search (MAC block, MAC, compares, nonce block, nonce,
`rho` copies). -/
def frontC : Nat := 17 + 2489875 + 1 + 16 + 59 + 8 * 2 + 30

/-- The 16 doublewords of the nonce input `S0 | T7 | S1 | 0^16 | m | 0^32`. -/
theorem wordsOf_nonce (sk : BitVec 256) (m : T3.Message) :
    wordsOf (privateInput sk (.inr (.inl m))) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, BitVec.ofNat 64 1793, 0, sk.extractLsb' 128 64,
        sk.extractLsb' 192 64, 0, 0, m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64, 0, 0, 0, 0] := by
  obtain ⟨h1, h2, h3, h4⟩ := sk_words sk
  rw [privateInput_nonce_eq, wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_header, wordsOf_bytesLE16, wordsOf_zero16, wordsOf_bytesLE32,
    show List.replicate 32 (0 : UInt8) = List.replicate (8 * 4) 0 from rfl, wordsOf_replicate_zero, h1, h2, h3, h4]
  rfl

section front
variable {sk : SecretKey} {cache : Bytes 131072} {m : Message}

/-- **The front**: the MAC check, the nonce and the digest search, then `payloadRest`. -/
theorem sign_front (hK : DigestSearchSpec sk) {W : Nat} {Q : Option Signature → MachineState → Prop}
    (hfail : ∀ t, Failed t → Q none t)
    (hrest : ∀ rho N t, AfterDs sk cache m rho N t →
      TBSim image sk t W (payloadRest (cacheDec cache) rho N) Q) :
    TBSim image sk (sinit sk cache m) (frontC + dsCost + W) (sign (cacheDec cache) m) Q := by
  set s0 := sinit sk cache m with hs0
  obtain ⟨t1, st1, p1, x5, g0, g8, g16, g24, r1, f1⟩ := blk0_spec s0 (sinit_pc sk cache m)
  have e1 : ∀ X, X < 2 ^ 64 → ¬ ((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) →
      t1.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX h => f1.get hX h
  have hsk : FullCache.SkAt t1 sk := by
    intro j
    rw [e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_sk sk cache m j.val j.isLt
  have hregion : t1.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
    rw [frame_readWords f1 REGION 16380 (by decide) (fun i _ h => by sg_omega)]
    exact sinit_region sk cache m
  rw [sign_eq]
  refine TBSim.of_eq (W := 17 + (2489875 + (1 + (16 + (59 + (8 * 2 + (30 + (dsCost + W)))))))) ?_ rfl
    (by unfold frontC; ring)
  refine TBSim.steps st1 ?_
  refine TBSim.bind ((FullCache.mac_tsim true sk (cacheDec cache).region t1 p1 x5 hsk hregion).toTBSim (by decide))
    (fun a tm hm => ?_)
  obtain ⟨t2, stm, pcm, rm, fm⟩ := blk1432_spec tm hm.pc
  refine TBSim.steps stm ?_
  have t2x5 : t2.getReg .x5 = 0 := by rw [rm.get (by simp),hm.x5]
  have hwf : Frame t1 t2 (fun X => (PRIV ≤ X ∧ X < PRIV+64) ∨
      (0x70000 ≤ X ∧ X < 0x70040) ∨ (MACOUT ≤ X ∧ X < MACOUT+32)) :=
    (hm.frame.trans fm).mono (by
      intro X hX h; rcases h with h | h
      · exact h
      · exact h.elim)
  have ha : OutAt t2 MACOUT a := by
    have hw : t2.readWords (BitVec.ofNat 64 MACOUT) 4 = wordsOf (bytesLE 32 a) := by
      rw [frame_readWords fm MACOUT 4 (by decide) (by intro i hi h; exact h)]
      exact hm.words
    rw [show (4:Nat)=2+2 from rfl,readWords_add,readWords_two,readWords_two,wordsOf_bytesLE32] at hw
    simp only [List.cons_append,List.nil_append,List.cons.injEq] at hw
    intro k hk
    interval_cases k
    · exact hw.1
    · exact hw.2.1
    · exact hw.2.2.1
    · exact hw.2.2.2.1
  have ht : OutAt t2 TAG (cacheDec cache).tag := fun k hk => by
    rw [hwf.get (by sg_omega) (by sg_omega)]
    have := sinit_tag sk cache m k hk
    interval_cases k
    · rw [show TAG + 8 * 0 = TAG from rfl, g0]; exact this
    · rw [show TAG + 8 * 1 = TAG + 8 from rfl, g8]; exact this
    · rw [show TAG + 8 * 2 = TAG + 16 from rfl, g16]; exact this
    · rw [show TAG + 8 * 3 = TAG + 24 from rfl, g24]; exact this
  obtain ⟨heq, hne⟩ := cmp_chain t2 pcm a _ ha ht
  by_cases hat : a = (cacheDec cache).tag
  swap
  · -- tampered cache: `fail`
    rw [if_pos hat]
    obtain ⟨u, k, c, su, hc, upc⟩ := hne hat
    obtain ⟨v, sv, hfv, -, -⟩ := fail_spec u upc
    exact TBSim.mono (TBSim.pure_steps (su.trans sv) (hfail v hfv)) (by omega) (fun _ _ h => h)
  rw [if_neg (not_not.2 hat)]
  obtain ⟨t3, st3, p3, r3, f3⟩ := heq hat
  refine TBSim.steps st3 ?_
  -- the nonce
  obtain ⟨t4, st4, p4, y10, y11, y12, q0, q8, q32, q40, q48, q56, n0, n8, n16, n24, n32, n40, n48, n56, n64, n72,
    n80, n88, r4, f4⟩ := blk63_spec t3 p3
  have f04 : Frame s0 t4 (fun X => ((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) ∨
      (MACOUT ≤ X ∧ X < MACOUT + 32) ∨ (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (0x70000 ≤ X ∧ X < 0x70040)) :=
    (((f1.trans hwf).trans f3).trans f4).mono (fun X _ h => by
      rcases h with ((h | h) | h) | h
      · exact Or.inl h
      · sg_omega
      · exact h.elim
      · sg_omega)
  have k : ∀ j < 4, t3.getMem (BitVec.ofNat 64 (SK + 8 * j)) = sk.extractLsb' (64 * j) 64 := fun j hj => by
    rw [f3.get (by sg_omega) (fun h => h), hwf.get (by sg_omega) (by sg_omega), e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_sk sk cache m j hj
  have mm : ∀ j < 4, t3.getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := fun j hj => by
    rw [f3.get (by sg_omega) (fun h => h), hwf.get (by sg_omega) (by sg_omega), e1 _ (by sg_omega) (by sg_omega)]
    exact sinit_msg sk cache m j hj
  have x5' : t4.getReg .x5 = 0 := by
    rw [r4.get (by decide), r3.get (by decide), t2x5]
  have hv4 : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NONCE 128 RHOOUT y10 y11 y12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hq4 : hashInput t4 = toQ (privateInput sk (.inr (.inl m))) := by
    refine hashInput_toQ t4 _ 1 NONCE (by
      rw [privateInput_nonce_eq]; simp [bytesLE_length, SigGolfCandidate.T3.zero16]) y10 (by decide) (by decide)
      y11 (by decide) ?_
    rw [wordsOf_nonce, show 8 * (1 + 1) = 8 + 8 from rfl, readWords_add, readWords_eight, readWords_eight]
    have z : ∀ X, NONCE + 96 ≤ X → X < NONCE + 128 → t4.getMem (BitVec.ofNat 64 X) = 0 := fun X h1 h2 => by
      rw [f04.get (by sg_omega) (by sg_omega)]; exact sinit_zero sk cache m X (by unfold Search.TOP_DATA; sg_omega) (by sg_omega)
    rw [n0, n8, n16, n24, n32, n40, n48, n56, n64, n72, n80, n88, z _ (by sg_omega) (by sg_omega),
      z _ (by sg_omega) (by sg_omega), z _ (by sg_omega) (by sg_omega), z _ (by sg_omega) (by sg_omega),
      show SK = SK + 8 * 0 from rfl, k 0 (by decide), k 1 (by decide), k 2 (by decide), k 3 (by decide),
      show MSG = MSG + 8 * 0 from rfl, mm 0 (by decide), mm 1 (by decide), mm 2 (by decide), mm 3 (by decide)]
    rfl
  refine TBSim.steps st4 ?_
  rw [signPayload_eq]
  refine TBSim.privateNonce_bind (W := 30 + (dsCost + W)) (fetch_122 t4 p4) x5' hv4 hq4 (fun b => ?_)
  -- rho to the signature and the digest block
  set t5 := writeHash t4 b
  have hwf5 := Frame.writeHash t4 b RHOOUT y12 (by decide)
  have hrho : DigAt t5 RHOOUT (b.extractLsb' 0 128) := DigAt.writeHash_lo t4 b RHOOUT y12 (by decide)
  obtain ⟨t6, st6, p6, x19, s0', s8', d0, d8, d32, d40, d48, d56, r6, f6⟩ :=
    blk123_spec t5 (by rw [pc_writeHash, p4, pcOf_add4])
  have mm5 : ∀ j < 4, t5.getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := fun j hj => by
    rw [hwf5.get (by sg_omega) (by sg_omega), f4.get (by sg_omega) (by sg_omega)]; exact mm j hj
  have hpre : DsPre t6 (b.extractLsb' 0 128) m :=
    { pc := p6
      x5 := by rw [r6.get (by decide), getReg_writeHash, x5']
      x19 := x19
      rho := ⟨by rw [d0]; exact hrho.1, by rw [d8]; exact hrho.2⟩
      msg := fun k hk => by
        interval_cases k
        · rw [show DIG + 32 + 8 * 0 = DIG + 32 from rfl, d32]; exact mm5 0 (by decide)
        · rw [show DIG + 32 + 8 * 1 = DIG + 40 from rfl, d40]; exact mm5 1 (by decide)
        · rw [show DIG + 32 + 8 * 2 = DIG + 48 from rfl, d48]; exact mm5 2 (by decide)
        · rw [show DIG + 32 + 8 * 3 = DIG + 56 from rfl, d56]; exact mm5 3 (by decide) }
  refine TBSim.steps st6 (TBSim.bind (hK t6 _ m hpre) (fun r u hu => ?_))
  rcases r with _ | ⟨ctr, N⟩
  · exact TBSim.mono (TBSim.pure (hfail u hu)) (by omega) (fun _ _ h => h)
  obtain ⟨upc, ux5, uadm, unb, usel, ur, uf⟩ := hu
  refine hrest _ N u ?_
  have f06 : Frame s0 t6 (fun X => (((TAG ≤ X ∧ X < TAG + 32) ∨ (MACBLK ≤ X ∧ X < MACBLK + 64)) ∨
      (MACOUT ≤ X ∧ X < MACOUT + 32) ∨ (PRIV ≤ X ∧ X < PRIV + 64) ∨ (NONCE ≤ X ∧ X < NONCE + 96) ∨ (0x70000 ≤ X ∧ X < 0x70040)) ∨
      (RHOOUT ≤ X ∧ X < RHOOUT + 32) ∨ (SIG ≤ X ∧ X < SIG + 16) ∨ (DIG ≤ X ∧ X < DIG + 64)) :=
    ((f04.trans hwf5).trans f6).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · sg_omega)
  have g6 : ∀ X, X < 2 ^ 64 → ¬ DsW X → u.getMem (BitVec.ofNat 64 X) = t6.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => uf.get hX h
  have nDs : ∀ X, (X < DIG + 16 ∨ (DIG + 32 ≤ X ∧ X < NBUF)) → ¬ DsW X := fun X hX h => by
    unfold DsW at h; sg_omega
  have pv : ∀ X, X < 2 ^ 64 → (PRIV ≤ X ∧ X < PRIV + 64) → u.getMem (BitVec.ofNat 64 X) =
      t4.getMem (BitVec.ofNat 64 X) := fun X hX h => by
    rw [g6 X hX (nDs X (by sg_omega)), f6.get hX (by sg_omega), hwf5.get hX (by sg_omega)]
  exact
    { pc := upc
      x5 := ux5
      adm := uadm
      nbuf := unb
      sel := usel
      rho := ⟨by rw [g6 _ (by sg_omega) (nDs _ (by sg_omega)), s0']; exact hrho.1,
        by rw [g6 _ (by sg_omega) (nDs _ (by sg_omega)), s8']; exact hrho.2⟩
      p0 := by rw [pv _ (by sg_omega) (by sg_omega), q0, k 0 (by decide)]
      p8 := by rw [pv _ (by sg_omega) (by sg_omega), q8]; exact k 1 (by decide)
      p32 := by rw [pv _ (by sg_omega) (by sg_omega), q32]; exact k 2 (by decide)
      p40 := by rw [pv _ (by sg_omega) (by sg_omega), q40]; exact k 3 (by decide)
      p48 := by rw [pv _ (by sg_omega) (by sg_omega), q48]
      p56 := by rw [pv _ (by sg_omega) (by sg_omega), q56]
      frame := (f06.trans uf).mono (fun X _ h => by unfold FrontW; unfold DsW at h; sg_omega) }

end front

end SigGolfCandidate.T3M.Sign
