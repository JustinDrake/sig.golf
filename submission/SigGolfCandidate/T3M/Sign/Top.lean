import SigGolfCandidate.T3M.Sign.FtsBlocks
import SigGolfCandidate.T3M.Sign.TopMask
import SigGolfCandidate.T3M.Sign.TopLeaf
import SigGolfCandidate.T3M.Sign.Iface
import SigGolfCandidate.T3M.Sign.Kernels
import SigGolfCandidate.T3M.Sign.Digits

/-!
# Sign: layer 0 refines `signLayers cache index 1`

`l0Spec_of` composes the layer-0 counter search, the signature-only WOTS leaf,
and all twelve cached authentication siblings with the final halt setup. It
preserves the earlier signature fields and proves the complete layer-0 layout.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Pieces Cache signLayers signTop topPath counterSearch counterLimit buildLeaf
  nodeHash mask route height chainCount width maxDigit target decode header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP REGION
  LeafArgs LeafW leafRegs n4)
open SphincsSecurity (bytesLE bytesLE_length)

private theorem extractByte_zero_top (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]

/-! ## Core -/

theorem signLayers_one (cache : Cache) (index : Nat) (root : Digest) :
    signLayers cache index 1 root = (do
      let some (_, digits) ← counterSearch 0 (route index 0).2 (route index 0).1 root 0 counterLimit | pure none
      let part ← signTop cache (route index 0).1 digits
      pure (some [part])) := rfl

theorem route_0 {index : Nat} (h : index < 2 ^ 31) : route index 0 = (index / 2 ^ 19 % 4096, 0) := by
  show (index / 2 ^ 19 % 2 ^ 12, index / 2 ^ (19 + 12)) = _
  rw [Nat.div_eq_of_lt (by omega : index < 2 ^ (19 + 12))]
  rfl

private theorem sumTo_le_mul_top (f : Nat → Nat) (b : Nat) : ∀ n, (∀ j < n, f j ≤ b) → sumTo f n ≤ n * b
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
    have := sumTo_le_mul_top f b n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; rw [Nat.succ_mul]; omega

private theorem sumTo_le_sumTo_top (f g : Nat → Nat) : ∀ n, (∀ j < n, f j ≤ g j) → sumTo f n ≤ sumTo g n
  | 0, _ => le_rfl
  | n + 1, h => by
    have := sumTo_le_sumTo_top f g n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; omega

/-! ## The leaves of layer 0 -/

/-- The signature-only leaf (values to `SIG + 2240`; `dest` = the unused root slot left in `s9`). -/
def tl0 (leaf : Nat) (ds : List Nat) (dest : Nat) : LeafArgs :=
  ⟨0, 0, leaf, ds, true, DIGITS, SIG + 2240, dest, 447⟩
theorem tl0_costs (leaf dest : Nat) {ds : List Nat} (hd : ∀ i < 54, ds.getD i 0 ≤ 7) :
    (tl0 leaf ds dest).leafK ≤ (tl0 leaf ds dest).leafC ∧ (tl0 leaf ds dest).leafC ≤ 13328 := by
  have he : ∀ i < 54, (tl0 leaf ds dest).e i ≤ 7 := fun i hi => hd i hi
  have hiK : ∀ i, (tl0 leaf ds dest).iterK i ≤ (tl0 leaf ds dest).iterC i := fun i => by
    unfold LeafArgs.iterK LeafArgs.iterC; omega
  have hiC : ∀ i < 54, (tl0 leaf ds dest).iterC i ≤ 219 := fun i hi => by
    have := he i hi
    have e1 : (tl0 leaf ds dest).iterC i =
        21 + (if i < 51 then 5 else 3) + 1 + (26 * (tl0 leaf ds dest).e i + 10) + 0 := rfl
    rw [e1]; split_ifs <;> omega
  have hpK : ∀ p < 27, (tl0 leaf ds dest).pairK p ≤ (tl0 leaf ds dest).pairC p := fun p _ => by
    have e1 : (tl0 leaf ds dest).pairK p = 19 + (tl0 leaf ds dest).iterK (2 * p) +
        (if 2 * p + 1 < 54 then 3 + (tl0 leaf ds dest).iterK (2 * p + 1) else 0) := rfl
    have e2 : (tl0 leaf ds dest).pairC p = 26 + (tl0 leaf ds dest).iterC (2 * p) +
        (if 2 * p + 1 < 54 then 3 + (tl0 leaf ds dest).iterC (2 * p + 1) else 0) := rfl
    have := hiK (2 * p)
    have := hiK (2 * p + 1)
    rw [e1, e2]; split_ifs <;> omega
  have hpC : ∀ p < 27, (tl0 leaf ds dest).pairC p ≤ 467 := fun p hp => by
    have e2 : (tl0 leaf ds dest).pairC p = 26 + (tl0 leaf ds dest).iterC (2 * p) +
        (if 2 * p + 1 < 54 then 3 + (tl0 leaf ds dest).iterC (2 * p + 1) else 0) := rfl
    have := hiC (2 * p) (by omega)
    have := hiC (2 * p + 1) (by omega)
    rw [e2]; split_ifs <;> omega
  have hs1 := sumTo_le_sumTo_top _ _ 27 hpK
  have hs2 := sumTo_le_mul_top _ 467 27 hpC
  have hn : (tl0 leaf ds dest).n = 54 := rfl
  have hso : (tl0 leaf ds dest).so = true := rfl
  unfold LeafArgs.leafK LeafArgs.leafC
  simp only [hn, hso, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv]
  constructor <;> omega

section top
variable {sk : SecretKey} {cache : Bytes 131072}

/-- `build_leaf`'s entry conditions for a layer-0 leaf from `Base` and the registers. -/
theorem leafPreS_of {s : MachineState} {A : LeafArgs} (hb : Base sk cache s) (hlay : A.lay = 0)
    (h1 : s.getReg .x1 = pcOf A.ret) (h8 : s.getReg .x8 = BitVec.ofNat 64 0)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 A.tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 A.digp) (h23 : s.getReg .x23 = BitVec.ofNat 64 A.valp)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 A.dest) (h26 : s.getReg .x26 = BitVec.ofNat 64 54)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 51) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0))
    (htree : A.tree < 2 ^ 32) (hleaf : A.leaf < 2 ^ 32)
    (hdig : ∀ i < 54, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i))
    (hdigb : ∀ i < 54, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit 0 i))
    (hdigp : A.digp + 54 ≤ 2 ^ 24) (hdigW : ∀ i < 54, ¬ LeafW A ((A.digp + i) / 8 * 8))
    (hv8 : A.valp % 8 = 0) (hv : A.valp + 16 * 54 ≤ 2 ^ 24)
    (hvs : A.valp + 16 * 54 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hd8 : A.so = false → A.dest % 8 = 0)
    (hd : A.dest + 16 ≤ 2 ^ 24) (hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT))
    (hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * 54 ≤ A.dest) : LeafPreS sk s A := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  have h4 : n4 A.lay = 51 := by rw [hlay]; rfl
  exact
    { x1 := h1
      x5 := hb.x5
      x8 := by rw [h8, hlay]; rfl
      x9 := h9
      x18 := h18
      x22 := h22
      x23 := h23
      x25 := h25
      x26 := by rw [h26, hn]
      x27 := by rw [h27, h4]
      x31 := h31
      htree := htree
      hleaf := hleaf
      p0 := hb.p0
      p8 := hb.p8
      p32 := hb.p32
      p40 := hb.p40
      p48 := hb.p48
      p56 := hb.p56
      z0 := hb.zero _ (by sgo) (by unfold NeverW; simp)
      z8 := hb.zero _ (by sgo) (by unfold NeverW; simp)
      z32 := hb.zero _ (by sgo) (by unfold NeverW; simp)
      z40 := hb.zero _ (by sgo) (by unfold NeverW; simp)
      ztail := fun _ => ⟨hb.zero _ (by sgo) (by unfold NeverW; simp), hb.zero _ (by sgo) (by unfold NeverW; simp)⟩
      hdig := fun i hi => hdig i (by rw [hn] at hi; exact hi)
      hdigb := fun i hi => by rw [hlay]; exact hdigb i (by rw [hn] at hi; exact hi)
      hdigp := by rw [hn]; exact hdigp
      hdigW := fun i hi => hdigW i (by rw [hn] at hi; exact hi)
      hv8 := hv8
      hv := by rw [hn]; exact hv
      hvs := by rw [hn]; exact hvs
      hd8 := hd8
      hd := hd
      hds := hds
      hdv := by rw [hn]; exact hdv }

/-- `Base` survives a layer-0 leaf. -/
theorem base_leaf {s t : MachineState} {A : LeafArgs} (hb : Base sk cache s) (hlay : A.lay = 0)
    (hf : Frame s t (LeafW A)) (hr : RegsExcept s t leafRegs)
    (hvB : A.valp + 16 * 54 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hvR : A.valp + 16 * 54 ≤ REGION ∨ REGION + 131040 ≤ A.valp)
    (hdB : A.dest + 16 ≤ PRIV) (hdZ : A.dest + 16 ≤ ZDIG ∨ ZDIG + 64 ≤ A.dest)
    (hvZ : A.valp + 16 * 54 ≤ ZDIG ∨ ZDIG + 64 ≤ A.valp)
    (hvT : A.valp + 16 * 54 ≤ Search.TOP_DATA) : Base sk cache t := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  refine hb.frame hf hr (by decide) (fun X _ hB hW => ?_)
  unfold BaseA NeverW Search.TOP_DATA at hB
  unfold Search.TOP_DATA at hvT
  unfold LeafW at hW
  rw [hn] at hW
  sgo

/-- The layer-0 registers every leaf call keeps. -/
structure TopRegs (leaf : Nat) (s : MachineState) : Prop where
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 0
  x14 : s.getReg .x14 = BitVec.ofNat 64 leaf
  x26 : s.getReg .x26 = BitVec.ofNat 64 54
  x27 : s.getReg .x27 = BitVec.ofNat 64 51

theorem TopRegs.of {leaf : Nat} {s t : MachineState} {l : List Reg} (h : TopRegs leaf s) (hr : RegsExcept s t l)
    (hl : Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x14 ∉ l ∧ Reg.x26 ∉ l ∧ Reg.x27 ∉ l) : TopRegs leaf t :=
  ⟨by rw [hr.get hl.1, h.x8], by rw [hr.get hl.2.1, h.x9], by rw [hr.get hl.2.2.1, h.x14],
    by rw [hr.get hl.2.2.2.1, h.x26], by rw [hr.get hl.2.2.2.2, h.x27]⟩

/-- The zero digit row `ZDIG`. -/
theorem zdig_byte {s : MachineState} (hb : Base sk cache s) {i : Nat} (hi : i < 54) :
    s.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 0 := by
  rw [getByte_eq_word s _ (by sgo), hb.zero _ (by sgo) (by unfold NeverW; sgo), extractByte_zero_top]
  rfl

/-- Writes allowed to layer 0, closed under composition. -/
theorem frame_l0 {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (hW : ∀ A, W A → L0W A) :
    Frame s t L0W := h.mono (fun A _ hA => hW A hA)

theorem frame_l0_trans {s t u : MachineState} (h1 : Frame s t L0W) (h2 : Frame t u L0W) : Frame s u L0W :=
  (h1.trans h2).mono (fun A _ h => by rcases h with h | h <;> exact h)

theorem leafW_l0 {A : LeafArgs} (hlay : A.lay = 0)
    (hv : A.valp + 16 * 54 ≤ SIG ∨ (SIG + 2240 ≤ A.valp ∧ A.valp + 16 * 54 ≤ SIG + 3296) ∨ SIG + 5664 ≤ A.valp)
    (hd : A.dest + 16 ≤ SIG ∨ (SIG + 2240 ≤ A.dest ∧ A.dest + 16 ≤ SIG + 3296) ∨ SIG + 5664 ≤ A.dest) :
    ∀ X, LeafW A X → L0W X := by
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  intro X hX
  unfold LeafW at hX
  rw [hn] at hX
  unfold L0W
  constructor <;> sgo

/-- The doublewords `[lo, hi)` are unchanged from `s` to `t`. -/
def KeepI (s t : MachineState) (lo hi : Nat) : Prop :=
  ∀ A, A < 2 ^ 64 → lo ≤ A → A < hi → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)

theorem KeepI.of_frame {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {lo hi : Nat}
    (hW : ∀ A, lo ≤ A → A < hi → ¬ W A) : KeepI s t lo hi := fun A hA h1 h2 => h.get hA (hW A h1 h2)

theorem KeepI.trans {s t u : MachineState} {lo hi : Nat} (h1 : KeepI s t lo hi) (h2 : KeepI t u lo hi) :
    KeepI s u lo hi := fun A hA a b => (h2 A hA a b).trans (h1 A hA a b)

theorem KeepI.mono {s t : MachineState} {lo hi lo' hi' : Nat} (h : KeepI s t lo hi) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : KeepI s t lo' hi' := fun A hA a b => h A hA (by omega) (by omega)

theorem KeepI.digAt {s t : MachineState} {lo hi A : Nat} {d : Digest} (h : KeepI s t lo hi) (hd : DigAt s A d)
    (h1 : lo ≤ A) (h2 : A + 16 ≤ hi) (h3 : A + 16 ≤ 2 ^ 64) : DigAt t A d :=
  ⟨(h A (by omega) h1 (by omega)).trans hd.1, (h (A + 8) (by omega) (by omega) (by omega)).trans hd.2⟩

/-- **Layer 0** (given E's `counter_search`): `L0Spec`. -/
theorem l0Spec_of (hK : CounterSearchSpec sk) : L0Spec sk cache := by
  intro index root t h
  have hSIG : SIG = 28672 := rfl
  have hidx := h.hidx
  have hl : index / 2 ^ 19 % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  rw [signLayers_one, route_0 hidx]
  obtain ⟨t1, st1, t1pc, t1x1, t1x8, t1x9, t1x26, t1x27, t1x17, t1x18, t1x14, t1r, t1f⟩ :=
    blk427_spec t h.pc index hidx h.idx
  have hcs : CsPre t1 0 0 (index / 2 ^ 19 % 4096) root 441 :=
    { pc := t1pc
      x1 := t1x1
      x5 := by rw [t1r.get (by decide), h.base.x5]
      x8 := t1x8
      x9 := t1x9
      x18 := t1x18
      x17 := t1x17
      x26 := t1x26
      x27 := t1x27
      htree := by norm_num
      hleaf := by omega
      msg := h.enc.frame t1f (by sgo) (fun h => h) (fun h => h)
      c32 := by rw [t1f.get (by sgo) (fun h => h)]; exact h.c32
      z40 := by rw [t1f.get (by sgo) (fun h => h)]; exact h.base.zero _ (by sgo) (by unfold NeverW; simp)
      z48 := by rw [t1f.get (by sgo) (fun h => h)]; exact h.base.zero _ (by sgo) (by unfold NeverW; simp)
      z56 := by rw [t1f.get (by sgo) (fun h => h)]; exact h.base.zero _ (by sgo) (by unfold NeverW; simp)
      table := h.base.table.frame t1f (fun _ _ h => h) }
  have hc0 : csCost 0 = counterLimit * 205 + 2000 := by unfold csCost; rw [if_pos rfl]
  refine TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 50000) (hK t1 0 0 _ root 441 hcs) (fun r u hu => ?_)))
    (by rw [hc0]; unfold L0Cost; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, ds⟩
  · exact TBSim.mono (TBSim.pure hu) (by omega) (fun _ _ h => h)
  obtain ⟨upc, ux5, ⟨v0, hdec⟩, udig, -, ur, uf, ux25⟩ := hu
  obtain ⟨-, hdb⟩ := decode_digits hdec
  have hd7 : ∀ i < 54, ds.getD i 0 ≤ 7 := fun i hi => by
    have := hdb i hi
    have : maxDigit 0 i ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
    omega
  have hx25 : (u.getReg .x25).toNat ≤ 126 := ux25
  set leaf := index / 2 ^ 19 % 4096 with hleaf_def
  set dest0 := (u.getReg .x25).toNat with hdest0
  -- registers and memory up to the first leaf
  have gu : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x17, .x18, .x26, .x27, .x28] ++ csRegs →
      u.getReg r = t.getReg r := fun r hr => (t1r.trans ur).get hr
  have ftu : Frame t u CsW := (t1f.trans uf).mono (fun A _ h => by
    rcases h with h | h
    · exact h.elim
    · exact h)
  have hbu : Base sk cache u := h.base.frame ftu (t1r.trans ur) (by decide) (fun A _ hb hw => by
    unfold BaseA NeverW Search.TOP_DATA at hb; unfold CsW at hw; sgo)
  have u14 : u.getReg .x14 = BitVec.ofNat 64 leaf := by rw [ur.get (by decide)]; exact t1x14
  obtain ⟨u1, su1, u1pc, u1x1, u1x31, u1x22, u1x23, u1r, u1f⟩ := blk441_spec u upc
  have g1 : ∀ r, r ∉ [.x1, .x22, .x23, .x31] → u1.getReg r = u.getReg r := fun r hr => u1r.get hr
  have hbu1 : Base sk cache u1 := hbu.frame u1f u1r (by decide) (fun _ _ _ h => h)
  have tr1 : TopRegs leaf u1 :=
    ⟨by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x8, by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x9,
      by rw [g1 _ (by decide)]; exact u14, by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x26,
      by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x27⟩
  have hp0 : LeafPreS sk u1 (tl0 leaf ds dest0) :=
    leafPreS_of hbu1 rfl u1x1 tr1.x8 tr1.x9 (by rw [g1 _ (by decide), ur.get (by decide)]; exact t1x18) u1x22 u1x23
      (by rw [g1 _ (by decide)]; show u.getReg .x25 = BitVec.ofNat 64 (u.getReg .x25).toNat
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      tr1.x26 tr1.x27 u1x31 (by show 0 < 2 ^ 32; norm_num) (by show leaf < 2 ^ 32; omega)
      (fun i hi => by
        show u1.getByte (BitVec.ofNat 64 (DIGITS + i)) = _
        rw [u1f.getByte (by sgo) (fun h => h)]; exact udig i hi)
      (fun i hi => ⟨by show ds.getD i 0 < 256; have := hd7 i hi; omega, fun h => by simp [tl0] at h⟩)
      (by show DIGITS + 54 ≤ 2 ^ 24; sgo) (fun i hi => by unfold LeafW; simp only [tl0, LeafArgs.n, chainCount, Matrix.cons_val_zero]; sgo)
      (by show (SIG + 2240) % 8 = 0; sgo) (by show SIG + 2240 + 16 * 54 ≤ 2 ^ 24; sgo)
      (Or.inl (by show SIG + 2240 + 16 * 54 ≤ PRIV; sgo)) (fun h => by simp [tl0] at h)
      (by show dest0 + 16 ≤ 2 ^ 24; omega) (Or.inl (by show dest0 + 16 ≤ PRIV; sgo))
      (Or.inl (by show dest0 + 16 ≤ SIG + 2240; sgo))
  obtain ⟨k0le, c0le⟩ := tl0_costs leaf dest0 hd7
  have hL0 := buildLeaf_tsimS subAt_sign sk hp0 u1pc
  dsimp only
  rw [signTop, bind_assoc]
  refine TBSim.mono (TBSim.steps su1 (TBSim.bind (W₂ := 36000) (TSim.toTBSim hL0 k0le) (fun r0 v0 hv0 => ?_)))
    (by omega) (fun _ _ h => h)
  obtain ⟨root0, values⟩ := r0
  obtain ⟨v0pc, -, v0vals, v0len, -, v0r, v0f⟩ := hv0
  have hbv0 : Base sk cache v0 := base_leaf hbu1 rfl v0f v0r (Or.inl (by show SIG + 2240 + 16 * 54 ≤ PRIV; sgo))
    (Or.inl (by show SIG + 2240 + 16 * 54 ≤ REGION; sgo)) (by show dest0 + 16 ≤ PRIV; sgo)
    (Or.inl (by show dest0 + 16 ≤ ZDIG; sgo)) (Or.inl (by show SIG + 2240 + 16 * 54 ≤ ZDIG; sgo))
    (by show SIG + 2240 + 16 * 54 ≤ Search.TOP_DATA; unfold Search.TOP_DATA; sgo)
  have trv0 : TopRegs leaf v0 := tr1.of v0r (by decide)
  have fv0 : Frame t v0 L0W := frame_l0_trans (frame_l0_trans (frame_l0_trans (frame_l0 t1f (fun _ h => h.elim))
    (frame_l0 uf (fun A hA => by unfold CsW at hA; unfold L0W; constructor <;> sgo)))
    (frame_l0 u1f (fun _ h => h.elim)))
    (frame_l0 v0f (leafW_l0 rfl (by simp only [tl0]; sgo) (by simp only [tl0]; sgo)))
  show TBSim image sk v0 36000 ((topPath (cacheDec cache) leaf >>= fun path => pure (values, path)) >>=
    fun part => pure (some [part])) (L0Post t)
  simp only [topPath, bind_assoc, pure_bind]
  obtain ⟨v1,s447,v1pc,v1r,v1f⟩ := blk447_spec v0 v0pc
  obtain ⟨w,s1433,wpc,wx22,wx24,wx20,wr,wf⟩ := blk1433_spec v1 v1pc
  have hbw : Base sk cache w := (hbv0.frame v1f v1r (by decide) (fun _ _ _ h => h)).frame wf wr
    (by decide) (fun _ _ _ h => h)
  have w14 : w.getReg .x14=BitVec.ofNat 64 leaf := by
    rw [wr.get (by decide),v1r.get (by decide),trv0.x14]
  have hm := tp_masks hbw hl w14 (w:=w)
    ⟨wpc,wx22,by simpa using wx24,wx20,RegsExcept.refl _ _,Frame.refl _ _,DigsAt.nil _ _⟩
  refine TBSim.mono (TBSim.steps (s447.trans s1433)
    (TBSim.bind (W₂:=3) (TSim.toTBSim hm (by norm_num)) (fun path x hx => ?_)))
      (by omega) (fun _ _ h => h)
  obtain ⟨hlen,hx⟩ := hx
  obtain ⟨x1,s1482,x1pc,x1r,x1f⟩ := blk1482_spec x (by simpa [hlen] using hx.pc)
  obtain ⟨x2,s540,x2pc,x2x5,x2x10,x2r,x2f⟩ := blk540_spec x1 x1pc
  have fwx := hx.frame.trans (x1f.trans x2f)
  have keep : KeepI v0 x2 SIG (SIG+3104) :=
    ((KeepI.of_frame v1f (fun _ _ _ h => h)).trans (KeepI.of_frame wf (fun _ _ _ h => h))).trans
      (KeepI.of_frame fwx (fun A h1 h2 hA => by
        rcases hA with hA | hA | hA
        · unfold TMW at hA; sgo
        · exact hA
        · exact hA))
  refine TBSim.pure_steps (s1482.trans s540)
    ⟨values,path,rfl,⟨x2pc,x2x5,x2x10⟩,fun i hi => ?_,fun j hj => ?_,?_⟩
  · exact keep.digAt (v0vals i (by rw [v0len]; exact hi)) (by omega) (by omega) (by sgo)
  · have hd := hx.out j (by rw [hlen]; exact hj)
    exact hd.frame (x1f.trans x2f) (by sgo)
      (fun h => by rcases h with h | h <;> exact h) (fun h => by rcases h with h | h <;> exact h)
  · exact frame_l0_trans (frame_l0_trans (frame_l0_trans fv0 (frame_l0 v1f (fun _ h => h.elim)))
      (frame_l0 wf (fun _ h => h.elim))) (frame_l0 fwx (fun A hA => by
        rcases hA with hA | hA | hA
        · unfold TMW at hA; unfold L0W; constructor <;> sgo
        · exact hA.elim
        · exact hA.elim))

end top
end SigGolfCandidate.T3M.Sign
