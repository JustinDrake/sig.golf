import SigGolfCandidate.T3M.Keygen.Mask

/-! Full-cache key-generation payload refinement. -/
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest Cache Region keygen keygenPayload buildTree mask privateMac privateInput
  header zero16 cacheBytes readLE)
open SphincsSecurity (bytesLE bytesLE_length)

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

structure PayloadPost (sk : SecretKey) (r : Digest × Region) (t : MachineState) : Prop where
  pc : t.pc = pcOf 334
  x20 : t.getReg .x20 = BitVec.ofNat 64 1
  x5 : t.getReg .x5 = 0
  pk : DigAt t 0xA0 r.1
  region : t.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn r.2)
  k0 : t.getMem (BitVec.ofNat 64 0x80) = sk.extractLsb' 0 64
  k8 : t.getMem (BitVec.ofNat 64 0x88) = sk.extractLsb' 64 64
  k16 : t.getMem (BitVec.ofNat 64 0x90) = sk.extractLsb' 128 64
  k24 : t.getMem (BitVec.ofNat 64 0x98) = sk.extractLsb' 192 64

section main
variable {sk : SecretKey} {s1 : MachineState} (hs : KStart sk s1)
include hs

/-- **`keygenPayload`** from `KStart`. -/
theorem payload_tsim :
    TSim image sk s1 29847693 37245055 991230 1048574 keygenPayload (PayloadPost sk) := by
  unfold keygenPayload
  refine (TSim.bind (k₂ := 143458) (c₂ := 172123) (n₂ := 4095) (b₂ := 4095) (buildTree_tsim hs)
    (fun r t ht => ?_)).of_eq rfl rfl rfl rfl rfl
  obtain ⟨levels, vals⟩ := r
  obtain ⟨tpc, theap, tregs, tframe⟩ := ht
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := blk39_spec t tpc
  obtain ⟨t4, st4', t4pc, t4x2, t4x20, t4x22, t4x24, t4a', t4b', t4r', t4f'⟩ :=
    blk277_spec t3 t3pc
  have t4a : t4.getMem (BitVec.ofNat 64 0xA0)=t.getMem (BitVec.ofNat 64 (TOP+16)) :=
    t4a'.trans (t3f.get (by decide) (fun h => h))
  have t4b : t4.getMem (BitVec.ofNat 64 0xA8)=t.getMem (BitVec.ofNat 64 (TOP+24)) :=
    t4b'.trans (t3f.get (by decide) (fun h => h))
  have st4 := st3.trans st4'
  have t4r := t3r.trans t4r'
  have t4f : Frame t t4 (fun X => X=0xA0 ∨ X=0xA8) :=
    (t3f.trans t4f').mono (fun X _ h => by rcases h with h | h; exact h.elim; exact h)
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
      x2 := t4x2
      x5 := by rw [t4r.get (by decide), tregs.get (by decide), hs.x5]
      x22 := t4x22
      x20 := t4x20
      x24 := t4x24
      p0 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p0]
      p8 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p8]
      p32 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p32]
      p40 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p40]
      p48 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p48]
      p56 := by rw [fr _ (by decide) (nW _ (by kg_omega)) (by decide) (by decide), hs.p56]
      nodes := fun l h2 => by
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
  have hfl' : masked.flatten.length = 8190 := by rw [show 2 ^ (13 - 12) = 2 from rfl] at hfl; omega
  have g : ∀ r, r ∉ maskRegs → u.getReg r = t4.getReg r := fun r hr => hu.regs.get hr
  have fu : ∀ X, X < 2 ^ 64 → ¬ (W1 X ∨ LevW kgLev X) → X ≠ 0xA0 → X ≠ 0xA8 → ¬ MW X →
      u.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 h4 =>
    (hu.frame.get hX h4).trans (fr X hX h1 h2 h3)
  have nM : ∀ X, X < 0xA0 → ¬ MW X := by
    intro X hX h; unfold MW at h; kg_omega
  refine ⟨by simpa only [hml, Nat.lt_irrefl, ite_false] using hu.pc, by rw [hu.x20, hml]; rfl, by rw [g _ (by decide), t4r.get (by decide), tregs.get (by decide),
    hs.x5], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pk = node 1
    obtain ⟨hl12, hd12⟩ := hnodes 12 le_rfl
    have h0 := hd12.get (i := 0) (by rw [hl12]; decide)
    have hpk : DigAt t4 0xA0 ((levels.getD 12 []).getD 0 0) := ⟨by rw [t4a]; exact h0.1, by rw [t4b]; exact h0.2⟩
    exact hpk.frame hu.frame (by decide) (by unfold MW; kg_omega) (by unfold MW; kg_omega)
  · -- the region
    show u.readWords (BitVec.ofNat 64 REGION) 16380 =
      wordsOf (List.ofFn fun i : Fin 131040 => (masked.flatten.flatMap (bytesLE 16)).toArray.getD i.val 0)
    rw [ofFn_getD_toArray 131040 _ (by rw [length_flatMap16, hfl']), ← hu.out.words, hfl']
  · rw [fu 0x80 (by decide) (nW 0x80 (by kg_omega)) (by decide) (by decide) (nM 0x80 (by kg_omega)), hs.k0]
  · rw [fu 0x88 (by decide) (nW 0x88 (by kg_omega)) (by decide) (by decide) (nM 0x88 (by kg_omega)), hs.k8]
  · rw [fu 0x90 (by decide) (nW 0x90 (by kg_omega)) (by decide) (by decide) (nM 0x90 (by kg_omega)), hs.k16]
  · rw [fu 0x98 (by decide) (nW 0x98 (by kg_omega)) (by decide) (by decide) (nM 0x98 (by kg_omega)), hs.k24]

end main

end SigGolfCandidate.T3M.Keygen
