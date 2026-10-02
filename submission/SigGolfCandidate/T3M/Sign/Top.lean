import SigGolfCandidate.T3M.Sign.TopMask
import SigGolfCandidate.T3M.Sign.TopLeaf
import SigGolfCandidate.T3M.Sign.Iface
import SigGolfCandidate.T3M.Sign.Kernels
import SigGolfCandidate.T3M.Sign.Digits
import SigGolfCandidate.T3M.Sign.LowTree

/-!
# Sign: layer 0 (words 427..542) refines `signLayers cache index 1`

`layer_0` (427): the layer-0 `counter_search` (E's kernel), then Core's `signTop`: the signature-only leaf
(values to `SIG + 2256`), the sibling leaf (root to the path slot `SIG + 3184`), the two leaves of the sibling
pair (roots to `NODE`, `NODE + 48`), their node hash (to `SIG + 3200`), the ten masked cache nodes (`tp_masks`,
to `SIG + 3216 ..`), `HALT(0)`. `l0Spec_of : CounterSearchSpec sk → L0Spec sk cache`.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Pieces Cache signLayers signTop topPath counterSearch counterLimit buildLeaf
  nodeHash mask route height chainCount width target decode header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION
  LeafArgs LeafW leafRegs n4 wordsOf_nodeInput nodeInput_length)
open SphincsSecurity (bytesLE bytesLE_length)

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

/-! ## The leaves of layer 0 -/

/-- The signature-only leaf (values to `SIG + 2256`; `dest` = the unused root slot left in `s9`). -/
def tl0 (leaf : Nat) (ds : List Nat) (dest : Nat) : LeafArgs :=
  ⟨0, 0, leaf, ds, true, DIGITS, SIG + 2256, dest, 447⟩
/-- The sibling leaf (root to the path slot `SIG + 3184`). -/
def tl1 (leaf : Nat) : LeafArgs := ⟨0, 0, leaf ^^^ 1, [], false, ZDIG, DUMMY, SIG + 3184, 456⟩
/-- The left leaf of the sibling pair (root to `NODE`). -/
def tl2 (leaf : Nat) : LeafArgs := ⟨0, 0, (leaf / 2 ^^^ 1) * 2, [], false, ZDIG, DUMMY, NODE, 464⟩
/-- The right leaf of the sibling pair (root to `NODE + 48`). -/
def tl3 (leaf : Nat) : LeafArgs := ⟨0, 0, (leaf / 2 ^^^ 1) * 2 + 1, [], false, ZDIG, DUMMY, NODE + 48, 470⟩

/-- A layer-0 leaf with no digits (its costs do not depend on the other fields). -/
def tlz : LeafArgs := ⟨0, 0, 0, [], false, 0, 0, 0, 0⟩

theorem tlz_costs : tlz.leafK = 7203 ∧ tlz.leafC = 8995 := by decide

theorem tl_costs (leaf : Nat) :
    (tl1 leaf).leafK = 7203 ∧ (tl1 leaf).leafC = 8995 ∧ (tl2 leaf).leafK = 7203 ∧ (tl2 leaf).leafC = 8995 ∧
      (tl3 leaf).leafK = 7203 ∧ (tl3 leaf).leafC = 8995 := by
  have e1 : (tl1 leaf).leafK = tlz.leafK ∧ (tl1 leaf).leafC = tlz.leafC := ⟨rfl, rfl⟩
  have e2 : (tl2 leaf).leafK = tlz.leafK ∧ (tl2 leaf).leafC = tlz.leafC := ⟨rfl, rfl⟩
  have e3 : (tl3 leaf).leafK = tlz.leafK ∧ (tl3 leaf).leafC = tlz.leafC := ⟨rfl, rfl⟩
  rw [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, tlz_costs.1, tlz_costs.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tl0_costs (leaf dest : Nat) {ds : List Nat} (hd : ∀ i < 58, ds.getD i 0 ≤ 7) :
    (tl0 leaf ds dest).leafK ≤ (tl0 leaf ds dest).leafC ∧ (tl0 leaf ds dest).leafC ≤ 13328 := by
  have he : ∀ i < 58, (tl0 leaf ds dest).e i ≤ 7 := fun i hi => hd i hi
  have hiK : ∀ i, (tl0 leaf ds dest).iterK i ≤ (tl0 leaf ds dest).iterC i := fun i => by
    unfold LeafArgs.iterK LeafArgs.iterC; omega
  have hiC : ∀ i < 58, (tl0 leaf ds dest).iterC i ≤ 215 := fun i hi => by
    have := he i hi
    have e1 : (tl0 leaf ds dest).iterC i =
        21 + (if i < 49 then 1 else 0) + 1 + (26 * (tl0 leaf ds dest).e i + 10) + 0 := rfl
    rw [e1]; split_ifs <;> omega
  have hpK : ∀ p < 29, (tl0 leaf ds dest).pairK p ≤ (tl0 leaf ds dest).pairC p := fun p _ => by
    have e1 : (tl0 leaf ds dest).pairK p = 19 + (tl0 leaf ds dest).iterK (2 * p) +
        (if 2 * p + 1 < 58 then 3 + (tl0 leaf ds dest).iterK (2 * p + 1) else 0) := rfl
    have e2 : (tl0 leaf ds dest).pairC p = 26 + (tl0 leaf ds dest).iterC (2 * p) +
        (if 2 * p + 1 < 58 then 3 + (tl0 leaf ds dest).iterC (2 * p + 1) else 0) := rfl
    have := hiK (2 * p)
    have := hiK (2 * p + 1)
    rw [e1, e2]; split_ifs <;> omega
  have hpC : ∀ p < 29, (tl0 leaf ds dest).pairC p ≤ 459 := fun p hp => by
    have e2 : (tl0 leaf ds dest).pairC p = 26 + (tl0 leaf ds dest).iterC (2 * p) +
        (if 2 * p + 1 < 58 then 3 + (tl0 leaf ds dest).iterC (2 * p + 1) else 0) := rfl
    have := hiC (2 * p) (by omega)
    have := hiC (2 * p + 1) (by omega)
    rw [e2]; split_ifs <;> omega
  have hs1 := sumTo_le_sumTo _ _ 29 hpK
  have hs2 := sumTo_le_mul _ 459 29 hpC
  have hn : (tl0 leaf ds dest).n = 58 := rfl
  have hso : (tl0 leaf ds dest).so = true := rfl
  unfold LeafArgs.leafK LeafArgs.leafC
  simp only [hn, hso, ↓reduceIte, Nat.reduceAdd, Nat.reduceDiv]
  constructor <;> omega

section top
variable {sk : SecretKey} {cache : Bytes 32768}

/-- `build_leaf`'s entry conditions for a layer-0 leaf from `Base` and the registers. -/
theorem leafPreS_of {s : MachineState} {A : LeafArgs} (hb : Base sk cache s) (hlay : A.lay = 0)
    (h1 : s.getReg .x1 = pcOf A.ret) (h8 : s.getReg .x8 = BitVec.ofNat 64 0)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 A.tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 A.digp) (h23 : s.getReg .x23 = BitVec.ofNat 64 A.valp)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 A.dest) (h26 : s.getReg .x26 = BitVec.ofNat 64 58)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 49) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0))
    (htree : A.tree < 2 ^ 32) (hleaf : A.leaf < 2 ^ 32)
    (hdig : ∀ i < 58, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i))
    (hdigb : ∀ i < 58, A.d i < 256 ∧ (A.so = false → A.d i ≤ 2 ^ width 0 i - 1))
    (hdigp : A.digp + 58 ≤ 2 ^ 24) (hdigW : ∀ i < 58, ¬ LeafW A ((A.digp + i) / 8 * 8))
    (hv8 : A.valp % 8 = 0) (hv : A.valp + 16 * 58 ≤ 2 ^ 24)
    (hvs : A.valp + 16 * 58 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hd8 : A.so = false → A.dest % 8 = 0)
    (hd : A.dest + 16 ≤ 2 ^ 24) (hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT))
    (hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * 58 ≤ A.dest) : LeafPreS sk s A := by
  have hn : A.n = 58 := by show chainCount A.lay = 58; rw [hlay]; rfl
  have h4 : n4 A.lay = 49 := by rw [hlay]; rfl
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
    (hvB : A.valp + 16 * 58 ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hvR : A.valp + 16 * 58 ≤ REGION ∨ REGION + 32736 ≤ A.valp)
    (hdB : A.dest + 16 ≤ REGION ∨ (REGION + 32736 ≤ A.dest ∧ A.dest + 16 ≤ PRIV) ∨ A.dest = NODE ∨ A.dest = NODE + 48 ∨
      LEAFPK + 960 ≤ A.dest) (hdZ : A.dest + 16 ≤ ZDIG ∨ ZDIG + 64 ≤ A.dest)
    (hvZ : A.valp + 16 * 58 ≤ ZDIG ∨ ZDIG + 64 ≤ A.valp) : Base sk cache t := by
  have hn : A.n = 58 := by show chainCount A.lay = 58; rw [hlay]; rfl
  refine hb.frame hf hr (by decide) (fun X _ hB hW => ?_)
  unfold BaseA NeverW at hB
  unfold LeafW at hW
  rw [hn] at hW
  sgo

/-- The layer-0 registers every leaf call keeps. -/
structure TopRegs (leaf : Nat) (s : MachineState) : Prop where
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 0
  x14 : s.getReg .x14 = BitVec.ofNat 64 leaf
  x26 : s.getReg .x26 = BitVec.ofNat 64 58
  x27 : s.getReg .x27 = BitVec.ofNat 64 49

theorem TopRegs.of {leaf : Nat} {s t : MachineState} {l : List Reg} (h : TopRegs leaf s) (hr : RegsExcept s t l)
    (hl : Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x14 ∉ l ∧ Reg.x26 ∉ l ∧ Reg.x27 ∉ l) : TopRegs leaf t :=
  ⟨by rw [hr.get hl.1, h.x8], by rw [hr.get hl.2.1, h.x9], by rw [hr.get hl.2.2.1, h.x14],
    by rw [hr.get hl.2.2.2.1, h.x26], by rw [hr.get hl.2.2.2.2, h.x27]⟩

/-- The zero digit row `ZDIG`. -/
theorem zdig_byte {s : MachineState} (hb : Base sk cache s) {i : Nat} (hi : i < 58) :
    s.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 0 := by
  rw [getByte_eq_word s _ (by sgo), hb.zero _ (by sgo) (by unfold NeverW; sgo), extractByte_zero']
  rfl

/-- Writes allowed to layer 0, closed under composition. -/
theorem frame_l0 {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (hW : ∀ A, W A → L0W A) :
    Frame s t L0W := h.mono (fun A _ hA => hW A hA)

theorem frame_l0_trans {s t u : MachineState} (h1 : Frame s t L0W) (h2 : Frame t u L0W) : Frame s u L0W :=
  (h1.trans h2).mono (fun A _ h => by rcases h with h | h <;> exact h)

theorem leafW_l0 {A : LeafArgs} (hlay : A.lay = 0)
    (hv : A.valp + 16 * 58 ≤ SIG ∨ (SIG + 2256 ≤ A.valp ∧ A.valp + 16 * 58 ≤ SIG + 3376) ∨ SIG + 5744 ≤ A.valp)
    (hd : A.dest + 16 ≤ SIG ∨ (SIG + 2256 ≤ A.dest ∧ A.dest + 16 ≤ SIG + 3376) ∨ SIG + 5744 ≤ A.dest) :
    ∀ X, LeafW A X → L0W X := by
  have hn : A.n = 58 := by show chainCount A.lay = 58; rw [hlay]; rfl
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
      z56 := by rw [t1f.get (by sgo) (fun h => h)]; exact h.base.zero _ (by sgo) (by unfold NeverW; simp) }
  have hc0 : csCost 0 = counterLimit * 205 + 2000 := by unfold csCost; rw [if_pos rfl]
  refine TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 50000) (hK t1 0 0 _ root 441 hcs) (fun r u hu => ?_)))
    (by rw [hc0]; unfold L0Cost; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, ds⟩
  · exact TBSim.mono (TBSim.pure hu) (by omega) (fun _ _ h => h)
  obtain ⟨upc, ux5, ⟨v0, hdec⟩, udig, -, ur, uf, ux25⟩ := hu
  obtain ⟨-, hdb⟩ := decode_digits hdec
  have hd7 : ∀ i < 58, ds.getD i 0 ≤ 7 := fun i hi => by
    have := hdb i hi
    have : 2 ^ width 0 i - 1 ≤ 7 := by unfold width; split_ifs <;> norm_num
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
    unfold BaseA NeverW at hb; unfold CsW at hw; sgo)
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
      (by show DIGITS + 58 ≤ 2 ^ 24; sgo) (fun i hi => by unfold LeafW; simp only [tl0, LeafArgs.n, chainCount_0]; sgo)
      (by show (SIG + 2256) % 8 = 0; sgo) (by show SIG + 2256 + 16 * 58 ≤ 2 ^ 24; sgo)
      (Or.inl (by show SIG + 2256 + 16 * 58 ≤ PRIV; sgo)) (fun h => by simp [tl0] at h)
      (by show dest0 + 16 ≤ 2 ^ 24; omega) (Or.inl (by show dest0 + 16 ≤ PRIV; sgo))
      (Or.inl (by show dest0 + 16 ≤ SIG + 2256; sgo))
  obtain ⟨k0le, c0le⟩ := tl0_costs leaf dest0 hd7
  obtain ⟨k1, c1, k2, c2, k3, c3⟩ := tl_costs leaf
  have hL0 := buildLeaf_tsimS subAt_sign sk hp0 u1pc
  dsimp only
  rw [signTop, bind_assoc]
  refine TBSim.mono (TBSim.steps su1 (TBSim.bind (W₂ := 36000) (TSim.toTBSim hL0 k0le) (fun r0 v0 hv0 => ?_)))
    (by omega) (fun _ _ h => h)
  obtain ⟨root0, values⟩ := r0
  obtain ⟨v0pc, -, v0vals, v0len, -, v0r, v0f⟩ := hv0
  have hbv0 : Base sk cache v0 := base_leaf hbu1 rfl v0f v0r (Or.inl (by show SIG + 2256 + 16 * 58 ≤ PRIV; sgo))
    (Or.inl (by show SIG + 2256 + 16 * 58 ≤ REGION; sgo)) (Or.inl (by show dest0 + 16 ≤ REGION; sgo))
    (Or.inl (by show dest0 + 16 ≤ ZDIG; sgo)) (Or.inl (by show SIG + 2256 + 16 * 58 ≤ ZDIG; sgo))
  have trv0 : TopRegs leaf v0 := tr1.of v0r (by decide)
  have fv0 : Frame t v0 L0W := frame_l0_trans (frame_l0_trans (frame_l0_trans (frame_l0 t1f (fun _ h => h.elim))
    (frame_l0 uf (fun A hA => by unfold CsW at hA; unfold L0W; constructor <;> sgo)))
    (frame_l0 u1f (fun _ h => h.elim)))
    (frame_l0 v0f (leafW_l0 rfl (by simp only [tl0]; sgo) (by simp only [tl0]; sgo)))
  show TBSim image sk v0 36000 ((topPath (cacheDec cache) leaf >>= fun path => pure (values, path)) >>=
    fun part => pure (some [part])) (L0Post t)
  simp only [topPath, bind_assoc, pure_bind]
  -- the sibling leaf (root to the path slot `SIG + 3184`)
  obtain ⟨v0a, s447, v0apc, v0ax1, v0ax31, v0ax22, v0ax23, v0ax25, v0ax18, v0ar, v0af⟩ :=
    blk447_spec v0 v0pc leaf hl trv0.x14
  have hbv0a : Base sk cache v0a := hbv0.frame v0af v0ar (by decide) (fun _ _ _ h => h)
  have trv0a : TopRegs leaf v0a := trv0.of v0ar (by decide)
  have hp1 : LeafPreS sk v0a (tl1 leaf) :=
    leafPreS_of hbv0a rfl v0ax1 trv0a.x8 trv0a.x9 v0ax18 v0ax22 v0ax23 v0ax25 trv0a.x26 trv0a.x27 v0ax31
      (by show 0 < 2 ^ 32; norm_num) (by show leaf ^^^ 1 < 2 ^ 32; exact Nat.xor_lt_two_pow (by omega) (by norm_num))
      (fun i hi => by show v0a.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 (([] : List Nat).getD i 0)
                      rw [zdig_byte hbv0a hi]; rfl)
      (fun i hi => ⟨by show ([] : List Nat).getD i 0 < 256; simp, fun _ => by
        show ([] : List Nat).getD i 0 ≤ _; simp⟩)
      (by show ZDIG + 58 ≤ 2 ^ 24; sgo) (fun i hi => by unfold LeafW; simp only [tl1, LeafArgs.n, chainCount_0]; sgo)
      (by show DUMMY % 8 = 0; sgo) (by show DUMMY + 16 * 58 ≤ 2 ^ 24; sgo) (Or.inr (by show LEAFPK + 960 ≤ DUMMY; sgo))
      (fun _ => by show (SIG + 3184) % 8 = 0; sgo) (by show SIG + 3184 + 16 ≤ 2 ^ 24; sgo)
      (Or.inl (by show SIG + 3184 + 16 ≤ PRIV; sgo)) (Or.inl (by show SIG + 3184 + 16 ≤ DUMMY; sgo))
  have hL1 := buildLeaf_tsimS subAt_sign sk hp1 v0apc
  rw [k1, c1] at hL1
  refine TBSim.mono (TBSim.steps s447 (TBSim.bind (W₂ := 18600) (TSim.toTBSim hL1 (by norm_num))
    (fun r1 v1 hv1 => ?_))) (by omega) (fun _ _ h => h)
  obtain ⟨v1pc, v1root, -, -, -, v1r, v1f⟩ := hv1
  have v1root' : DigAt v1 (SIG + 3184) r1.1 := v1root rfl
  have hbv1 : Base sk cache v1 := base_leaf hbv0a rfl v1f v1r (Or.inr (by show LEAFPK + 960 ≤ DUMMY; sgo))
    (Or.inr (by show REGION + 32736 ≤ DUMMY; sgo)) (Or.inl (by show SIG + 3184 + 16 ≤ REGION; sgo))
    (Or.inl (by show SIG + 3184 + 16 ≤ ZDIG; sgo)) (Or.inr (by show ZDIG + 64 ≤ DUMMY; sgo))
  have trv1 : TopRegs leaf v1 := trv0a.of v1r (by decide)
  have fv1 : Frame t v1 L0W := frame_l0_trans (frame_l0_trans fv0 (frame_l0 v0af (fun _ h => h.elim)))
    (frame_l0 v1f (leafW_l0 rfl (by simp only [tl1]; sgo) (by simp only [tl1]; sgo)))
  -- the left leaf of the sibling pair (root to `NODE`)
  obtain ⟨v1a, s456, v1apc, v1ax1, v1ax23, v1ax25, v1ax18, v1ar, v1af⟩ := blk456_spec v1 v1pc leaf hl trv1.x14
  have hbv1a : Base sk cache v1a := hbv1.frame v1af v1ar (by decide) (fun _ _ _ h => h)
  have trv1a : TopRegs leaf v1a := trv1.of v1ar (by decide)
  have v1a22 : v1a.getReg .x22 = BitVec.ofNat 64 ZDIG := by
    rw [v1ar.get (by decide), v1r.get (by decide)]; exact v0ax22
  have v1a31 : v1a.getReg .x31 = BitVec.ofNat 64 0 := by
    rw [v1ar.get (by decide), v1r.get (by decide)]; exact v0ax31
  have hpb : (leaf / 2 ^^^ 1) * 2 < 4096 := by
    have : leaf / 2 ^^^ 1 < 2048 := Nat.xor_lt_two_pow (n := 11) (by omega) (by norm_num)
    omega
  have hp2 : LeafPreS sk v1a (tl2 leaf) :=
    leafPreS_of hbv1a rfl v1ax1 trv1a.x8 trv1a.x9 v1ax18 v1a22 v1ax23 v1ax25 trv1a.x26 trv1a.x27 v1a31
      (by show 0 < 2 ^ 32; norm_num) (by show (leaf / 2 ^^^ 1) * 2 < 2 ^ 32; omega)
      (fun i hi => by show v1a.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 (([] : List Nat).getD i 0)
                      rw [zdig_byte hbv1a hi]; rfl)
      (fun i hi => ⟨by show ([] : List Nat).getD i 0 < 256; simp, fun _ => by
        show ([] : List Nat).getD i 0 ≤ _; simp⟩)
      (by show ZDIG + 58 ≤ 2 ^ 24; sgo) (fun i hi => by unfold LeafW; simp only [tl2, LeafArgs.n, chainCount_0]; sgo)
      (by show DUMMY % 8 = 0; sgo) (by show DUMMY + 16 * 58 ≤ 2 ^ 24; sgo) (Or.inr (by show LEAFPK + 960 ≤ DUMMY; sgo))
      (fun _ => by show NODE % 8 = 0; sgo) (by show NODE + 16 ≤ 2 ^ 24; sgo)
      (Or.inr (Or.inr ⟨by show CHAIN + 80 ≤ NODE; sgo, by show NODE + 16 ≤ LOUT; sgo⟩))
      (Or.inl (by show NODE + 16 ≤ DUMMY; sgo))
  have hL2 := buildLeaf_tsimS subAt_sign sk hp2 v1apc
  rw [k2, c2] at hL2
  refine TBSim.mono (TBSim.steps s456 (TBSim.bind (W₂ := 9550) (TSim.toTBSim hL2 (by norm_num))
    (fun r2 v2 hv2 => ?_))) (by omega) (fun _ _ h => h)
  obtain ⟨v2pc, v2root, -, -, -, v2r, v2f⟩ := hv2
  have v2root' : DigAt v2 NODE r2.1 := v2root rfl
  have hbv2 : Base sk cache v2 := base_leaf hbv1a rfl v2f v2r (Or.inr (by show LEAFPK + 960 ≤ DUMMY; sgo))
    (Or.inr (by show REGION + 32736 ≤ DUMMY; sgo)) (Or.inr (Or.inr (Or.inl rfl)))
    (Or.inl (by show NODE + 16 ≤ ZDIG; sgo)) (Or.inr (by show ZDIG + 64 ≤ DUMMY; sgo))
  have trv2 : TopRegs leaf v2 := trv1a.of v2r (by decide)
  have fv2 : Frame t v2 L0W := frame_l0_trans (frame_l0_trans fv1 (frame_l0 v1af (fun _ h => h.elim)))
    (frame_l0 v2f (leafW_l0 rfl (by simp only [tl2]; sgo) (by simp only [tl2]; sgo)))
  -- the right leaf of the sibling pair (root to `NODE + 48`)
  obtain ⟨v2a, s464, v2apc, v2ax1, v2ax23, v2ax25, v2ax18, v2ar, v2af⟩ :=
    blk464_spec v2 v2pc ((leaf / 2 ^^^ 1) * 2) (by omega) (by rw [v2r.get (by decide)]; exact v1ax18)
  have hbv2a : Base sk cache v2a := hbv2.frame v2af v2ar (by decide) (fun _ _ _ h => h)
  have trv2a : TopRegs leaf v2a := trv2.of v2ar (by decide)
  have v2a22 : v2a.getReg .x22 = BitVec.ofNat 64 ZDIG := by
    rw [v2ar.get (by decide), v2r.get (by decide)]; exact v1a22
  have v2a31 : v2a.getReg .x31 = BitVec.ofNat 64 0 := by
    rw [v2ar.get (by decide), v2r.get (by decide)]; exact v1a31
  have hp3 : LeafPreS sk v2a (tl3 leaf) :=
    leafPreS_of hbv2a rfl v2ax1 trv2a.x8 trv2a.x9 v2ax18 v2a22 v2ax23 v2ax25 trv2a.x26 trv2a.x27 v2a31
      (by show 0 < 2 ^ 32; norm_num) (by show (leaf / 2 ^^^ 1) * 2 + 1 < 2 ^ 32; omega)
      (fun i hi => by show v2a.getByte (BitVec.ofNat 64 (ZDIG + i)) = BitVec.ofNat 8 (([] : List Nat).getD i 0)
                      rw [zdig_byte hbv2a hi]; rfl)
      (fun i hi => ⟨by show ([] : List Nat).getD i 0 < 256; simp, fun _ => by
        show ([] : List Nat).getD i 0 ≤ _; simp⟩)
      (by show ZDIG + 58 ≤ 2 ^ 24; sgo) (fun i hi => by unfold LeafW; simp only [tl3, LeafArgs.n, chainCount_0]; sgo)
      (by show DUMMY % 8 = 0; sgo) (by show DUMMY + 16 * 58 ≤ 2 ^ 24; sgo) (Or.inr (by show LEAFPK + 960 ≤ DUMMY; sgo))
      (fun _ => by show (NODE + 48) % 8 = 0; sgo) (by show NODE + 48 + 16 ≤ 2 ^ 24; sgo)
      (Or.inr (Or.inr ⟨by show CHAIN + 80 ≤ NODE + 48; sgo, by show NODE + 48 + 16 ≤ LOUT; sgo⟩))
      (Or.inl (by show NODE + 48 + 16 ≤ DUMMY; sgo))
  have hL3 := buildLeaf_tsimS subAt_sign sk hp3 v2apc
  rw [k3, c3] at hL3
  refine TBSim.mono (TBSim.steps s464 (TBSim.bind (W₂ := 540) (TSim.toTBSim hL3 (by norm_num))
    (fun r3 v3 hv3 => ?_))) (by omega) (fun _ _ h => h)
  obtain ⟨v3pc, v3root, -, -, -, v3r, v3f⟩ := hv3
  have v3root' : DigAt v3 (NODE + 48) r3.1 := v3root rfl
  have hbv3 : Base sk cache v3 := base_leaf hbv2a rfl v3f v3r (Or.inr (by show LEAFPK + 960 ≤ DUMMY; sgo))
    (Or.inr (by show REGION + 32736 ≤ DUMMY; sgo)) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (Or.inl (by show NODE + 48 + 16 ≤ ZDIG; sgo)) (Or.inr (by show ZDIG + 64 ≤ DUMMY; sgo))
  have trv3 : TopRegs leaf v3 := trv2a.of v3r (by decide)
  have fv3 : Frame t v3 L0W := frame_l0_trans (frame_l0_trans fv2 (frame_l0 v2af (fun _ h => h.elim)))
    (frame_l0 v3f (leafW_l0 rfl (by simp only [tl3]; sgo) (by simp only [tl3]; sgo)))
  -- the sibling pair node
  have v3x18 : v3.getReg .x18 = BitVec.ofNat 64 ((leaf / 2 ^^^ 1) * 2 + 1) := by
    rw [v3r.get (by decide)]; exact v2ax18
  obtain ⟨v3a, s470, v3apc, v3ax10, v3ax11, v3ax12, v3am16, v3am24, v3ar, v3af⟩ :=
    blk470_spec v3 v3pc _ (by omega) v3x18
  have hnode : ∀ X, (X = NODE ∨ X = NODE + 8 ∨ X = NODE + 48 ∨ X = NODE + 56 ∨ X = NODE + 32 ∨ X = NODE + 40) →
      v3a.getMem (BitVec.ofNat 64 X) = v3.getMem (BitVec.ofNat 64 X) := fun X hX =>
    v3af.get (by rcases hX with h | h | h | h | h | h <;> (rw [h]; sgo)) (by sgo)
  have hl2 : DigAt v3 NODE r2.1 := v2root'.frame (v2af.trans v3f) (by sgo) (fun h => by
    rcases h with h | h
    · exact h
    · unfold LeafW at h; simp only [tl3] at h; sgo) (fun h => by
    rcases h with h | h
    · exact h
    · unfold LeafW at h; simp only [tl3] at h; sgo)
  have hpair : (leaf / 2 ^^^ 1) * 2 + 1 = (leaf / 2 ^^^ 1) * 2 + 1 := rfl
  have hq : hashInput v3a = toQ (pad64 (bytesLE 16 r2.1 ++ bytesLE 16 (header 3 0 0 0 (2048 + (leaf / 2 ^^^ 1) * 2 / 2)) ++
      zero16 ++ bytesLE 16 r3.1)) := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length])]
    refine hashInput_toQ v3a _ 0 NODE (nodeInput_length _ _ _ _ _ _) v3ax10 (by decide) (by decide) v3ax11
      (by decide) ?_
    have hdiv : ((leaf / 2 ^^^ 1) * 2 + 1) / 2 = (leaf / 2 ^^^ 1) * 2 / 2 := by omega
    rw [wordsOf_nodeInput 3 _ _ _ _ _ (by decide), readWords_eight, hnode NODE (by simp), hnode (NODE + 8) (by simp),
      show NODE + 8 + 8 = NODE + 16 from rfl, v3am16, show NODE + 16 + 8 = NODE + 24 from rfl, v3am24, hdiv,
      show NODE + 24 + 8 = NODE + 32 from rfl, hnode (NODE + 32) (by simp), show NODE + 32 + 8 = NODE + 40 from rfl,
      hnode (NODE + 40) (by simp), show NODE + 40 + 8 = NODE + 48 from rfl, hnode (NODE + 48) (by simp),
      show NODE + 48 + 8 = NODE + 56 from rfl, hnode (NODE + 56) (by simp),
      hbv3.zero (NODE + 32) (by sgo) (by unfold NeverW; simp), hbv3.zero (NODE + 40) (by sgo) (by unfold NeverW; simp),
      hl2.1, hl2.2, v3root'.1, v3root'.2]
  have hv : hashArgumentsValid v3a = true :=
    hashArgs_const v3a NODE 64 NOUT v3ax10 v3ax11 v3ax12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : v3a.getReg .x5 = 0 := by rw [v3ar.get (by decide), hbv3.x5]
  have hblk : (toQ (pad64 (bytesLE 16 r2.1 ++ bytesLE 16 (header 3 0 0 0 (2048 + (leaf / 2 ^^^ 1) * 2 / 2)) ++
      zero16 ++ bytesLE 16 r3.1))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length]),
      blocks_toQ ⟨by rw [nodeInput_length]; omega, by rw [nodeInput_length]⟩, nodeInput_length]
  unfold nodeHash
  refine TBSim.mono (TBSim.steps s470 (TBSim.of_eq (TBSim.shortHash_bind (W := 516) (fetch_485 v3a v3apc) h5 hv hq
    (fun a => ?_)) rfl (by rw [hblk]))) (by omega) (fun _ _ h => h)
  -- the node to the path slot `SIG + 3200`, the masked cache nodes
  have hwf := Frame.writeHash v3a a NOUT v3ax12 (by decide)
  have hlo := DigAt.writeHash_lo v3a a NOUT v3ax12 (by decide)
  obtain ⟨w, s486, wpc, wm0, wm8, wx22, wx24, wx20, wr, wf⟩ :=
    blk486_spec (writeHash v3a a) (by rw [pc_writeHash, v3apc, pcOf_add4])
  have hwr : RegsExcept v3a (writeHash v3a a) [] := fun r _ => getReg_writeHash v3a a r
  have hbw : Base sk cache w := ((hbv3.frame v3af v3ar (by decide) (fun A _ hB hW => by
      unfold BaseA NeverW at hB; sgo)).frame hwf hwr (by decide)
      (fun A _ hB hW => by unfold BaseA NeverW at hB; sgo)).frame wf wr (by decide)
      (fun A _ hB hW => by unfold BaseA NeverW at hB; sgo)
  have trw : TopRegs leaf w := (trv3.of v3ar (by decide)).of (hwr.trans wr) (by decide)
  have fw : Frame t w L0W := frame_l0_trans (frame_l0_trans (frame_l0_trans fv3
    (frame_l0 v3af (fun A hA => by unfold L0W; constructor <;> sgo)))
    (frame_l0 hwf (fun A hA => by unfold L0W; constructor <;> sgo)))
    (frame_l0 wf (fun A hA => by unfold L0W; constructor <;> sgo))
  have hm := tp_masks hbw hl trw.x14 (w := w) ⟨wpc, by rw [wx22]; rfl, by rw [wx24]; rfl, by rw [wx20]; rfl,
    RegsExcept.refl _ _, Frame.refl _ _, DigsAt.nil _ _⟩
  refine TBSim.mono (TBSim.steps s486 (TBSim.bind (W₂ := 4) (TSim.toTBSim hm (by norm_num))
    (fun rest x hx => ?_))) (by omega) (fun _ _ h => h)
  obtain ⟨hlen, hx⟩ := hx
  -- `HALT(0)`
  obtain ⟨x1, s498, x1pc, x1r, x1f⟩ := blk498_spec x hx.pc 12 (by norm_num) (by rw [hx.x22, hlen])
  rw [if_neg (by norm_num)] at x1pc
  obtain ⟨x2, s540, x2pc, x2x5, x2x10, -, x2f⟩ := blk540_spec x1 x1pc
  have fwx : Frame w x2 (fun A => TMW A ∨ False ∨ False) := hx.frame.trans (x1f.trans x2f)
  have K3296 : KeepI w x2 SIG (SIG + 3216) := KeepI.of_frame fwx (fun A h1 h2 hA => by
    rcases hA with hA | hA | hA
    · unfold TMW at hA; sgo
    · exact hA
    · exact hA)
  have K3280 : KeepI v1 x2 SIG (SIG + 3200) :=
    ((((((KeepI.of_frame v1af (fun _ _ _ h => h)).trans (KeepI.of_frame v2f (fun A h1 h2 hA => by
      unfold LeafW at hA; simp only [tl2, LeafArgs.n, chainCount_0] at hA; sgo))).trans
      (KeepI.of_frame v2af (fun _ _ _ h => h))).trans (KeepI.of_frame v3f (fun A h1 h2 hA => by
      unfold LeafW at hA; simp only [tl3, LeafArgs.n, chainCount_0] at hA; sgo))).trans
      (KeepI.of_frame v3af (fun A h1 h2 hA => by sgo))).trans
      ((KeepI.of_frame hwf (fun A h1 h2 hA => by sgo)).trans (KeepI.of_frame wf (fun A h1 h2 hA => by sgo)))).trans
      (K3296.mono le_rfl (by omega))
  have K3264 : KeepI v0 x2 SIG (SIG + 3184) :=
    ((KeepI.of_frame v0af (fun _ _ _ h => h)).trans (KeepI.of_frame v1f (fun A h1 h2 hA => by
      unfold LeafW at hA; simp only [tl1, LeafArgs.n, chainCount_0] at hA; sgo))).trans (K3280.mono le_rfl (by omega))
  refine TBSim.pure_steps (s498.trans s540) ⟨values, _, rfl, ⟨x2pc, x2x5, x2x10⟩, fun i hi => ?_, fun j hj => ?_, ?_⟩
  · -- the values (from the signature-only leaf)
    refine K3264.digAt (v0vals i (by rw [v0len]; exact hi)) (by omega) (by omega) (by sgo)
  · -- the path: the sibling leaf, the pair node, the masked cache nodes
    rcases j with _ | _ | j
    · exact K3280.digAt v1root' (by omega) (by omega) (by sgo)
    · show DigAt x2 (SIG + 3184 + 16 * 1) (a.extractLsb' 0 128)
      rw [show SIG + 3184 + 16 * 1 = SIG + 3200 by omega]
      exact K3296.digAt ⟨wm0.trans hlo.1, wm8.trans hlo.2⟩ (by omega) (by omega) (by sgo)
    · show DigAt x2 (SIG + 3184 + 16 * (j + 2)) (rest.getD j 0)
      have := hx.out j (by rw [hlen]; omega)
      rw [show SIG + 3184 + 16 * (j + 2) = SIG + 3216 + 16 * j by omega]
      exact this.frame (x1f.trans x2f) (by sgo) (fun h => by rcases h with h | h <;> exact h)
        (fun h => by rcases h with h | h <;> exact h)
  · exact frame_l0_trans fw (frame_l0 fwx (fun A hA => by
      rcases hA with hA | hA | hA
      · unfold TMW at hA; unfold L0W; constructor <;> sgo
      · exact hA.elim
      · exact hA.elim))

end top

end SigGolfCandidate.T3M.Sign
