import SigGolfCandidate.T3M.Keygen.Mask
import SigGolfCandidate.T3M.Submission

/-!
# Keygen: the whole phase, exactly

`keygen_tsim` composes `start`, `buildTree_tsim`, the pk copy, `masks_tsim`, the MAC (one
513-block `privateMac` query over the 4,104 doublewords at `0x8FE0`) and `HALT`:
from the loaded state the machine refines Core's `keygen` in exactly 29,765,754 steps,
37,152,876 cycles (+1 for the final `ECALL`), 989,182 calls and 1,047,038 compressions.

* `keygen_run` : `submission.run .keygen sk` is Core's `keygen` (realized with `sk`) with the outputs
  `(pk, cacheB ⟨tag, region⟩)`, 37,152,877 cycles, 989,182 calls, 1,047,038 compressions;
* `keygen_run_counts` : the value / calls / compressions form (`countBoth`);
* `keygen_runWith` : the fixed-oracle form (finished, exactly 37,152,877 cycles `< 2^32`).
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest Cache Region keygen keygenPayload buildTree mask privateMac privateInput
  header zero16 cacheBytes readLE)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## Loading, regions, frames -/

theorem initialState_keygen (sk : SecretKey) : initialState submission .keygen sk = some (kinit sk) := by
  have hv := submission_keygen_valid
  unfold initialState
  rw [if_pos hv]
  simp only [submission_keygen, Images.keygenImage, Images.keygenData, MachineState.writeBytesAsWords_nil]
  rfl

/-- Core's region from its byte list. -/
theorem ofFn_getD_toArray (n : Nat) (l : List UInt8) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.toArray.getD i.val 0) = l := by
  subst h
  apply List.ext_getElem List.length_ofFn
  intro i h1 h2
  rw [List.getElem_ofFn]
  simp only [Array.getD, List.size_toArray, h2, dite_true]
  rfl

theorem length_flatMap16 (ds : List Digest) : (ds.flatMap (bytesLE 16)).length = 16 * ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring

/-- Unchanged doublewords read the same. -/
theorem Frame.readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, Frame.readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]

/-- The 4,104 doublewords of the MAC input `S0 | T14 | S1 | 0^16 | region | 0^32`. -/
theorem wordsOf_mac (sk : BitVec 256) (region : Region) :
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

/-! ## `keygenPayload` -/

/-- After `keygenPayload` (word 48, masks done): pk at `0xA0`, the region at `REGION`, the secret key
at `0x80`, zero at `0x11000 .. 0x11020`. -/
structure PayloadPost (sk : SecretKey) (r : Digest × Region) (t : MachineState) : Prop where
  pc : t.pc = pcOf 48
  x20 : t.getReg .x20 = BitVec.ofNat 64 1
  x5 : t.getReg .x5 = 0
  pk : DigAt t 0xA0 r.1
  region : t.readWords (BitVec.ofNat 64 REGION) 4092 = wordsOf (List.ofFn r.2)
  k0 : t.getMem (BitVec.ofNat 64 0x80) = sk.extractLsb' 0 64
  k8 : t.getMem (BitVec.ofNat 64 0x88) = sk.extractLsb' 64 64
  k16 : t.getMem (BitVec.ofNat 64 0x90) = sk.extractLsb' 128 64
  k24 : t.getMem (BitVec.ofNat 64 0x98) = sk.extractLsb' 192 64
  tail : t.readWords (BitVec.ofNat 64 0x11000) 4 = [0, 0, 0, 0]

section main
variable {sk : SecretKey} {s1 : MachineState} (hs : KStart sk s1)
include hs

/-- **`keygenPayload`** from `KStart`. -/
theorem payload_tsim :
    TSim image sk s1 29765694 37148713 989181 1046525 keygenPayload (PayloadPost sk) := by
  unfold keygenPayload
  refine (TSim.bind (k₂ := 61459) (c₂ := 75781) (n₂ := 2046) (b₂ := 2046) (buildTree_tsim hs)
    (fun r t ht => ?_)).of_eq rfl rfl rfl rfl rfl
  obtain ⟨levels, vals⟩ := r
  obtain ⟨tpc, theap, tregs, tframe⟩ := ht
  obtain ⟨t4, st4, t4pc, t4a, t4b, t4x24, t4x20, t4x13, t4r, t4f⟩ :=
    blk39_spec t tpc (by rw [tregs.get (by decide), hs.x2])
  have fr : ∀ X, X < 2 ^ 64 → ¬ (W1 X ∨ LevW kgLev X) → X ≠ 0xA0 → X ≠ 0xA8 →
      t4.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 =>
    (t4f.get hX (by rintro (h | h) <;> contradiction)).trans (tframe.get hX h1)
  have nW : ∀ X, (X < PRIV + 16 ∨ (PRIV + 32 ≤ X ∧ X < SEEDS) ∨ X = 0x11000 ∨ X = 0x11008 ∨ X = 0x11010 ∨
      X = 0x11018 ∨ X = NODE + 32 ∨ X = NODE + 40) → ¬ (W1 X ∨ LevW kgLev X) := by
    intro X hX h
    unfold W1 LevW kgLev at h
    kg_omega
  obtain ⟨hlev, hnodes⟩ := theap
  have hm : MaskPre sk t4 levels :=
    { pc := t4pc
      x2 := by rw [t4r.get (by decide), tregs.get (by decide), hs.x2]
      x5 := by rw [t4r.get (by decide), tregs.get (by decide), hs.x5]
      x13 := t4x13
      x20 := t4x20
      x24 := t4x24
      p0 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p0]
      p8 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p8]
      p32 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p32]
      p40 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p40]
      p48 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p48]
      p56 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p56]
      nodes := fun l h1 h2 => by
        obtain ⟨hl, hd⟩ := hnodes l (by omega)
        have hp : 2 ^ (12 - l) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
        refine ⟨hl, hd.frame t4f ?_ ?_⟩
        · change TOP + 16 * 2 ^ (12 - l) + 16 * (levels.getD l []).length < 2 ^ 64
          rw [show (levels.getD l []).length = 2 ^ (12 - l) from hl]; kg_omega
        · intro B hB _ h; change TOP + 16 * 2 ^ (12 - l) ≤ B at hB; kg_omega }
  refine TSim.steps st4 (TSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) (masks_tsim hm)
    (fun masked u hu => TSim.pure ?_))
  obtain ⟨hml, hu⟩ := hu
  have hfl := hu.flen
  rw [hml] at hfl
  have hfl' : masked.flatten.length = 2046 := by rw [show 2 ^ (11 - 10) = 2 from rfl] at hfl; omega
  have g : ∀ r, r ∉ maskRegs → u.getReg r = t4.getReg r := fun r hr => hu.regs.get hr
  have fu : ∀ X, X < 2 ^ 64 → ¬ (W1 X ∨ LevW kgLev X) → X ≠ 0xA0 → X ≠ 0xA8 → ¬ MW X →
      u.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 h4 =>
    (hu.frame.get hX h4).trans (fr X hX h1 h2 h3)
  have nM : ∀ X, (X < REGION ∨ X = 0x11000 ∨ X = 0x11008 ∨ X = 0x11010 ∨ X = 0x11018) → ¬ MW X := by
    intro X hX h; unfold MW at h; kg_omega
  refine ⟨hu.pc, by rw [hu.x20, hml]; rfl, by rw [g _ (by decide), t4r.get (by decide), tregs.get (by decide),
    hs.x5], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pk = node 1
    obtain ⟨hl12, hd12⟩ := hnodes 12 le_rfl
    have h0 := hd12.get (i := 0) (by rw [hl12]; decide)
    have hpk : DigAt t4 0xA0 ((levels.getD 12 []).getD 0 0) := ⟨by rw [t4a]; exact h0.1, by rw [t4b]; exact h0.2⟩
    exact hpk.frame hu.frame (by decide) (by unfold MW; kg_omega) (by unfold MW; kg_omega)
  · -- the region
    show u.readWords (BitVec.ofNat 64 REGION) 4092 =
      wordsOf (List.ofFn fun i : Fin 32736 => (masked.flatten.flatMap (bytesLE 16)).toArray.getD i.val 0)
    rw [ofFn_getD_toArray 32736 _ (by rw [length_flatMap16, hfl']), ← hu.out.words, hfl']
  · rw [fu 0x80 (by decide) (nW 0x80 (by kg_omega)) (by decide) (by decide) (nM 0x80 (by kg_omega)), hs.k0]
  · rw [fu 0x88 (by decide) (nW 0x88 (by kg_omega)) (by decide) (by decide) (nM 0x88 (by kg_omega)), hs.k8]
  · rw [fu 0x90 (by decide) (nW 0x90 (by kg_omega)) (by decide) (by decide) (nM 0x90 (by kg_omega)), hs.k16]
  · rw [fu 0x98 (by decide) (nW 0x98 (by kg_omega)) (by decide) (by decide) (nM 0x98 (by kg_omega)), hs.k24]
  · have z : ∀ X, (X = 0x11000 ∨ X = 0x11008 ∨ X = 0x11010 ∨ X = 0x11018) →
        u.getMem (BitVec.ofNat 64 X) = 0 := fun X hX =>
      (fu X (by kg_omega) (nW X (by kg_omega)) (by kg_omega) (by kg_omega) (nM X (by kg_omega))).trans
        (hs.zero X (by kg_omega) (by kg_omega) (by kg_omega))
    rw [show (4 : Nat) = 2 + 2 from rfl, readWords_add, readWords_two, readWords_two,
      z 0x11000 (by decide), z (0x11000 + 8) (by decide), z (0x11000 + 8 * 2) (by decide),
      z (0x11000 + 8 * 2 + 8) (by decide)]
    rfl

/-- At `HALT` (word 116): `t0 = 1`, `a0 = 0`, the outputs at `0xA0` and `0x9000`. -/
structure KDone (r : Digest × Cache) (t : MachineState) : Prop where
  pc : t.pc = pcOf 116
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 0
  pk : t.readWords (BitVec.ofNat 64 0xA0) 2 = wordsOf (bytesLE 16 r.1)
  cache : t.readWords (BitVec.ofNat 64 0x9000) 4096 = wordsOf (cacheBytes r.2)

/-- `keygen` from `KStart`: the payload, the MAC (513 blocks over `0x8FE0 .. 0x11020`), `HALT`. -/
theorem keygen_from_start : TSim image sk s1 29765728 37152850 989182 1047038 keygen KDone := by
  unfold keygen
  refine TSim.bind (k₂ := 34) (c₂ := 4137) (n₂ := 1) (b₂ := 513) (payload_tsim hs) (fun r t ht => ?_)
  obtain ⟨pk, region⟩ := r
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk48_spec t ht.pc 1 (by norm_num) ht.x20
  rw [if_pos rfl] at t1pc
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, m0, m8, m16, m24, m32, m40, m48, m56, t2r, t2f⟩ :=
    blk84_spec t1 t1pc
  have f02 : Frame t t2 (fun A => MACBLK ≤ A ∧ A < MACBLK + 64) :=
    (t1f.trans t2f).mono (fun X _ h => by rcases h with h | h; exact h.elim; exact h)
  have r02 : RegsExcept t t2 ([.x6] ++ [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30]) := t1r.trans t2r
  have e1 : ∀ X, X < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 X) = t.getMem (BitVec.ofNat 64 X) :=
    fun X hX => t1f.get hX (fun h => h)
  have h5 : t2.getReg .x5 = 0 := by rw [r02.get (by decide), ht.x5]
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 MACBLK 32832 0x9000 t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  obtain ⟨s0a, s0b, s1a, s1b⟩ := sk_words sk
  have hq : hashInput t2 = toQ (privateInput sk (.inr (.inr region))) := by
    refine hashInput_toQ t2 _ 512 MACBLK (privateInput_mac_length sk region) t2x10 (by decide) (by decide)
      t2x11 (by decide) ?_
    rw [wordsOf_mac]
    show t2.readWords (BitVec.ofNat 64 MACBLK) (8 + (4092 + 4)) = _
    rw [readWords_add, readWords_add, show MACBLK + 8 * 8 = REGION from rfl,
      show REGION + 8 * 4092 = 0x11000 from rfl, readWords_eight, m0, m8, m16, m24, m32, m40, m48, m56,
      e1 0x80 (by decide), e1 0x88 (by decide), e1 0x90 (by decide), e1 0x98 (by decide), ht.k0, ht.k8,
      ht.k16, ht.k24, Frame.readWords f02 REGION 4092 (by decide) (fun i _ h => by kg_omega),
      Frame.readWords f02 0x11000 4 (by decide) (fun i _ h => by kg_omega), ht.region, ht.tail,
      List.append_assoc]
  refine TSim.steps (st1.trans st2) (TSim.privateMac_bind (k := 2) (c := 2) (n := 0) (b := 0)
    (fetch_113 t2 t2pc) h5 hv hq (fun a => ?_))
  have hwf := Frame.writeHash t2 a 0x9000 t2x12 (by decide)
  obtain ⟨t3, st3, t3pc, t3x5, t3x10, t3r, t3f⟩ :=
    blk114_spec (writeHash t2 a) (by rw [pc_writeHash, t2pc, pcOf_add4])
  have f23 : Frame t2 t3 (fun A => 0x9000 ≤ A ∧ A < 0x9000 + 32) :=
    (hwf.trans t3f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
  refine TSim.pure_steps st3 ⟨t3pc, t3x5, t3x10, ?_, ?_⟩
  · have hpk : DigAt t3 0xA0 pk :=
      (ht.pk.frame f02 (by decide) (by kg_omega) (by kg_omega)).frame f23 (by decide) (by omega) (by omega)
    exact hpk.words
  · show t3.readWords (BitVec.ofNat 64 0x9000) (4 + 4092) = wordsOf (bytesLE 32 a ++ List.ofFn region)
    rw [readWords_add, wordsOf_append _ _ (by simp [bytesLE_length]),
      Frame.readWords t3f 0x9000 4 (by decide) (fun _ _ h => h), readWords_writeHash t2 a 0x9000 t2x12 (by decide),
      Frame.readWords f23 (0x9000 + 8 * 4) 4092 (by decide) (fun i _ h => by omega),
      Frame.readWords f02 (0x9000 + 8 * 4) 4092 (by decide) (fun i _ h => by kg_omega)]
    exact congrArg _ ht.region

end main

/-! ## The phase -/

/-- **Keygen on the machine**: from the loaded state, exactly Core's `keygen`. -/
theorem keygen_tsim (sk : SecretKey) :
    TSim image sk (kinit sk) 29765754 37152876 989182 1047038 keygen KDone := by
  obtain ⟨s1, st1, hs⟩ := kstart sk
  exact TSim.steps st1 (keygen_from_start hs)

/-- The outputs at `HALT`. -/
theorem kdone_output {r : Digest × Cache} {t : MachineState} (h : KDone r t) :
    readOutput submission.sizes submission.layout .keygen t = ((r.1 : PublicKey), cacheB r.2) := by
  show (readBuffer t 160 16, readBuffer t 0x9000 32768) = _
  have e1 : readBuffer t 160 (8 * 2) = BitVec.ofNat _ (readLE (bytesLE 16 r.1)) :=
    readBuffer_of_words t 160 2 (bytesLE 16 r.1) (by decide) (by decide) (bytesLE_length _ _) h.pk
  have e2 : readBuffer t 0x9000 (8 * 4096) = BitVec.ofNat _ (readLE (cacheBytes r.2)) :=
    readBuffer_of_words t 0x9000 4096 (cacheBytes r.2) (by decide) (by decide) (cacheBytes_length r.2) h.cache
  rw [readLE_bytesLE] at e1
  refine Prod.ext ?_ e2
  refine e1.trans (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt r.1.isLt]

/-- **`keygen_run`**: the keygen phase is Core's `keygen` realized with the secret key, with
outputs `(pk, cacheB ⟨tag, region⟩)`, exactly 37,152,877 cycles, 989,182 calls and 1,047,038
compressions. -/
theorem keygen_run (sk : SecretKey) :
    submission.run .keygen sk =
      (fun r => ⟨some ((r.1 : PublicKey), cacheB r.2), true, 37152877, 989182, 1047038⟩) <$>
        mrealize sk keygen :=
  XSim.run_eq submission .keygen sk (initialState_keygen sk) (keygen_tsim sk) (by decide)
    (fun r => ((r.1 : PublicKey), cacheB r.2))
    (fun _ t h => ⟨fetch_116 t h.pc, h.x5, h.x10, kdone_output h⟩)

/-- Core's `keygen` makes exactly 989,182 calls and 1,047,038 compressions. -/
theorem keygen_countBoth (sk : SecretKey) :
    countBoth (mrealize sk keygen) = (fun a => (a, 989182, 1047038)) <$> mrealize sk keygen :=
  XSim.countBoth_eq (keygen_tsim sk)

/-- Value, calls and compressions of the run = Core's value with its joint call / compression
count. -/
theorem keygen_run_counts (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2.1, p.2.2)) <$>
        countBoth (mrealize sk keygen) := by
  rw [keygen_run, keygen_countBoth, Functor.map_map, Functor.map_map]; rfl

/-- Fixed-oracle form: finished, exactly 37,152,877 cycles (`< 2^32`), for every oracle. -/
theorem keygen_runWith (hash : Hash) (sk : SecretKey) :
    submission.runWith hash .keygen sk =
      ⟨some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2), true, 37152877, 989182, 1047038⟩ := by
  unfold Submission.runWith
  rw [keygen_run, evalWithAnswerFn_map]

end SigGolfCandidate.T3M.Keygen
