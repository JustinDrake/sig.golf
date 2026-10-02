import SigGolfCandidate.T3M.Sign.LowTree
import SigGolfCandidate.T3M.Sign.Kernels
import SigGolfCandidate.T3M.Sign.Iface
import SigGolfCandidate.T3M.Sign.Digits

/-!
# Sign: the hypertree layers 3, 2, 1 and the link to layer 0

Core's `signLayers cache index 4 root` signs layer 3 (message: the forest pk), then layer 2 (message: layer 3's
root), layer 1, layer 0. The machine (words 370..427) does the same: per lower layer `lay` the setup block, the
`counter_search` call (E's kernel, `CounterSearchSpec`), the `build_tree` call (`buildTree_tbsim`), then the next
layer's setup block; layer 0 is entered at 427 (`L0Spec`).

* `PieceAt u lay p` : the piece `p = (values, path)` of layer `lay` in the signature (from digest `layIdx lay`);
* `SLPost t n` : the exit of `signLayers cache index n`: `fail`, or `HALT(0)` with the pieces of layers `0 .. n-1`,
  everything outside them and the FTS part of the signature possibly changed (`LayW n`);
* `lower_layer` : one lower layer, given the refinement of the layers below it;
* `layers_tbsim` : from the layer-3 entry, `signLayers cache index 4 root` within `layersC` cycles.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Pieces signLayers counterSearch counterLimit buildTree height chainCount
  target route decode width Cache)
open SigGolfCandidate.T3M.Keygen (LevW n4)

/-! ## Layout of the layer pieces -/

/-- First digest index of the piece of layer `n` (`n = 4`: the end of the signature). -/
def lstart : Nat → Nat
  | 0 => 140
  | 1 => 210
  | 2 => 260
  | 3 => 309
  | _ => 358

theorem lstart_mono (n : Nat) : lstart n ≤ lstart (n + 1) := by
  rcases n with _ | _ | _ | _ | n <;> simp [lstart]

/-- The layers below `n` may write anything but the FTS part of the signature and the pieces of the layers
`≥ n`. -/
def LayW (n : Nat) (A : Nat) : Prop :=
  ¬ (SIG ≤ A ∧ A < SIG + 2240) ∧ ¬ (SIG + 16 * lstart n ≤ A ∧ A < SIG + 5728)

/-- The piece `p = (values, path)` of layer `lay` in the signature. -/
def PieceAt (u : MachineState) (lay : Layer) (p : Pieces) : Prop :=
  (∀ i < chainCount lay, DigAt u (SIG + 16 * (layIdx lay + i)) (p.1.getD i 0)) ∧
    ∀ j < height lay, DigAt u (SIG + 16 * (layIdx lay + chainCount lay + j)) (p.2.getD j 0)

/-- The exit of `signLayers cache index n` (entered at `t`). -/
def SLPost (t : MachineState) (n : Nat) : Option (List Pieces) → MachineState → Prop
  | none, u => Failed u
  | some ps, u => Halted0 u ∧ ps.length = n ∧ (∀ lay : Layer, lay.val < n → PieceAt u lay (ps.getD lay.val ([], []))) ∧
      Frame t u (LayW n)

/-- `SLPost` from an earlier state (unchanged memory in between). -/
theorem SLPost.pre {s t : MachineState} {n : Nat} (hf : Frame s t (fun _ => False)) :
    ∀ r u, SLPost t n r u → SLPost s n r u
  | none, _, h => h
  | some _, _, ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, (hf.trans h4).mono (fun _ _ h => by
      rcases h with h | h
      · exact h.elim
      · exact h)⟩

/-- The three lower layers. -/
theorem lay_cases {lay : Layer} (hlay : lay ≠ 0) :
    (lay.val = 1 ∧ layIdx lay = 210 ∧ height lay = 7) ∨ (lay.val = 2 ∧ layIdx lay = 260 ∧ height lay = 6) ∨
      (lay.val = 3 ∧ layIdx lay = 309 ∧ height lay = 6) := by
  fin_cases lay
  · exact absurd rfl hlay
  · left; exact ⟨rfl, rfl, rfl⟩
  · right; left; exact ⟨rfl, rfl, rfl⟩
  · right; right; exact ⟨rfl, rfl, rfl⟩

theorem lay_facts {lay : Layer} (hlay : lay ≠ 0) :
    lstart lay.val = layIdx lay ∧ lstart (lay.val + 1) = layIdx lay + 43 + height lay ∧ 210 ≤ layIdx lay ∧
      layIdx lay + 43 + height lay ≤ 358 := by
  rcases lay_cases hlay with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;> simp [lstart]

theorem csW_layW {n A : Nat} (h : CsW A) : LayW n A := by
  have := lstart_mono n
  unfold CsW at h
  unfold LayW
  constructor <;> sgo

theorem btAllW_layW {lay : Layer} (hlay : lay ≠ 0) {tree A : Nat} (h : BtAllW lay tree (SIG + 16 * layIdx lay) A) :
    LayW (lay.val + 1) A := by
  unfold BtAllW BtW LevW at h
  simp only [btLev] at h
  unfold LayW
  obtain ⟨-, hls, -, -⟩ := lay_facts hlay
  rw [hls]
  rcases lay_cases hlay with ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ <;> rw [h2, h3] at h <;> rw [h2, h3] <;>
    simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] at h ⊢ <;> constructor <;> sgo

theorem layW_succ {n A : Nat} (h : LayW n A) : LayW (n + 1) A := by
  have := lstart_mono n
  exact ⟨h.1, fun h2 => h.2 ⟨by omega, h2.2⟩⟩

/-! ## The routes and the per-layer `build_tree` calls -/

theorem route_lt {index : Nat} (h : index < 2 ^ 31) (lay : Layer) :
    (route index lay).1 < 2 ^ height lay ∧ (route index lay).2 < 2 ^ 32 := by
  simp only [route]
  exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩

theorem route_3 (index : Nat) : route index 3 = (index % 64, index / 64) := by
  show (index / 2 ^ 0 % 2 ^ 6, index / 2 ^ (0 + 6)) = _
  simp

theorem route_2 (index : Nat) : route index 2 = (index / 64 % 64, index / 4096) := by
  show (index / 2 ^ 6 % 2 ^ 6, index / 2 ^ (6 + 6)) = _
  simp

theorem route_1 (index : Nat) : route index 1 = (index / 4096 % 128, index / 2 ^ 19) := by
  show (index / 2 ^ 12 % 2 ^ 7, index / 2 ^ (12 + 7)) = _
  simp

/-- The `jal build_tree` word of lower layer `lay` (`build_tree` returns to the next word). -/
def jalBT (lay : Layer) : Nat := (![0, 426, 411, 396] : Layer → Nat) lay

theorem blkJal_spec {lay : Layer} (hlay : lay ≠ 0) (s : MachineState) (hpc : s.pc = pcOf (jalBT lay)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf (jalBT lay + 1) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  fin_cases lay
  · exact absurd rfl hlay
  · exact blk426_spec s hpc
  · exact blk411_spec s hpc
  · exact blk396_spec s hpc

/-! ## One lower layer -/

/-- The `counter_search` entry (646) of lower layer `lay` with the message `msg` at `ENC`. -/
structure LayEntry (sk : SecretKey) (cache : Bytes 32768) (lay : Layer) (index : Nat) (msg : Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf 646
  x1 : t.getReg .x1 = pcOf (jalBT lay)
  x2 : t.getReg .x2 = BitVec.ofNat 64 LOW
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : t.getReg .x9 = BitVec.ofNat 64 (route index lay).2
  x14 : t.getReg .x14 = BitVec.ofNat 64 (route index lay).1
  x15 : t.getReg .x15 = BitVec.ofNat 64 (height lay)
  x16 : t.getReg .x16 = BitVec.ofNat 64 (SIG + 16 * layIdx lay)
  x17 : t.getReg .x17 = BitVec.ofNat 64 (target lay)
  x18 : t.getReg .x18 = BitVec.ofNat 64 (route index lay).1
  x26 : t.getReg .x26 = BitVec.ofNat 64 43
  x27 : t.getReg .x27 = BitVec.ofNat 64 0
  x31 : t.getReg .x31 = BitVec.ofNat 64 0
  base : Base sk cache t
  hlay : lay ≠ 0
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC msg
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32

/-- Back from `build_tree` at `ret` with the layer's root (the next message) at `ENC`. -/
structure LayNext (sk : SecretKey) (cache : Bytes 32768) (ret index : Nat) (root : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf ret
  x2 : t.getReg .x2 = BitVec.ofNat 64 LOW
  x26 : t.getReg .x26 = BitVec.ofNat 64 43
  x27 : t.getReg .x27 = BitVec.ofNat 64 0
  x31 : t.getReg .x31 = BitVec.ofNat 64 0
  base : Base sk cache t
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  enc : DigAt t ENC root
  c32 : (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32

/-- Core's `signLayers` at a lower layer. -/
theorem signLayers_low (cache : Cache) (index : Nat) {lay : Layer} (hlay : lay ≠ 0) (msg : Digest) :
    signLayers cache index (lay.val + 1) msg = (do
      let some (_, digits) ← counterSearch lay (route index lay).2 (route index lay).1 msg 0 counterLimit
        | pure none
      let (levels, values) ← buildTree lay (route index lay).2 (route index lay).1 digits
      let some previous ← signLayers cache index lay.val ((levels.getD (height lay) []).getD 0 0) | pure none
      pure (some (previous ++ [(values, (List.range (height lay)).map fun j =>
        (levels.getD j []).getD ((route index lay).1 / 2 ^ j ^^^ 1) 0)]))) := by
  fin_cases lay
  · exact absurd rfl hlay
  all_goals rfl

section layer
variable {sk : SecretKey} {cache : Bytes 32768}

/-- **One lower layer**: from the `counter_search` entry of layer `lay ≠ 0`, the machine refines
`signLayers cache index (lay + 1) msg`, given the refinement of `signLayers cache index lay` from the return of
`build_tree`. -/
theorem lower_layer (hK : CounterSearchSpec sk) {lay : Layer} {index : Nat} {msg : Digest} {t : MachineState}
    (h : LayEntry sk cache lay index msg t) {W : Nat}
    (hnext : ∀ root v, LayNext sk cache (jalBT lay + 1) index root v →
      TBSim image sk v W (signLayers (cacheDec cache) index lay.val root) (SLPost v lay.val)) :
    TBSim image sk t (csCost lay + (1 + (btCost + W))) (signLayers (cacheDec cache) index (lay.val + 1) msg)
      (SLPost t (lay.val + 1)) := by
  have hlay := h.hlay
  obtain ⟨hli, hls, hl0, hl1⟩ := lay_facts hlay
  have hH := height_low hlay
  have hSIG : SIG = 28672 := rfl
  obtain ⟨hleaf, htree⟩ := route_lt h.hidx lay
  have hcs : CsPre t lay (route index lay).2 (route index lay).1 msg (jalBT lay) :=
    { pc := h.pc
      x1 := h.x1
      x5 := h.base.x5
      x8 := h.x8
      x9 := h.x9
      x18 := h.x18
      x17 := h.x17
      x26 := by rw [h.x26, chainCount_low hlay]
      x27 := by rw [h.x27, n4_low hlay]
      htree := htree
      hleaf := by have : 2 ^ height lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega
      msg := h.enc
      c32 := h.c32
      z40 := h.base.zero _ (by sgo) (by unfold NeverW; simp)
      z48 := h.base.zero _ (by sgo) (by unfold NeverW; simp)
      z56 := h.base.zero _ (by sgo) (by unfold NeverW; simp) }
  rw [signLayers_low _ _ hlay]
  refine TBSim.bind (hK t lay _ _ msg (jalBT lay) hcs) (fun r u hu => ?_)
  rcases r with _ | ⟨c, ds⟩
  · exact TBSim.mono (TBSim.pure hu) (by omega) (fun _ _ h => h)
  obtain ⟨upc, -, ⟨v0, hdec⟩, udig, uc32, ur, uf, -⟩ := hu
  obtain ⟨-, hdb⟩ := decode_digits hdec
  obtain ⟨u1, st1, u1pc, u1x1, u1r, u1f⟩ := blkJal_spec hlay u upc
  have g1 : ∀ r, r ∉ csRegs ++ [.x1] → u1.getReg r = t.getReg r := fun r hr => (ur.trans u1r).get hr
  have fu1 : Frame t u1 CsW := (uf.trans u1f).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · exact h.elim)
  have hbt : BtPre sk cache lay (route index lay).2 (route index lay).1 ds (SIG + 16 * layIdx lay) u1 :=
    { x2 := by rw [g1 _ (by decide), h.x2]
      x8 := by rw [g1 _ (by decide), h.x8]
      x9 := by rw [g1 _ (by decide), h.x9]
      x14 := by rw [g1 _ (by decide), h.x14]
      x15 := by rw [g1 _ (by decide), h.x15]
      x16 := by rw [g1 _ (by decide), h.x16]
      x26 := by rw [g1 _ (by decide), h.x26]
      x27 := by rw [g1 _ (by decide), h.x27]
      x31 := by rw [g1 _ (by decide), h.x31]
      base := h.base.frame fu1 (ur.trans u1r) (by decide) (fun A _ hb hw => by
        unfold BaseA NeverW at hb
        unfold CsW at hw
        sgo)
      hlay := hlay
      htree := htree
      hsel := hleaf
      hdb := fun i hi => by
        have := hdb i (by rw [chainCount_low hlay]; exact hi)
        simpa [width, hlay] using this
      digits := fun i hi => by
        rw [u1f.getByte (by sgo) (fun h => h)]
        exact udig i (by rw [chainCount_low hlay]; exact hi)
      hsb := ⟨by omega, by omega⟩
      hsb8 := by omega }
  refine TBSim.steps st1 (TBSim.bind (buildTree_tbsim hbt u1pc u1x1) (fun lv v hv => ?_))
  obtain ⟨levels, values⟩ := lv
  obtain ⟨vpc, vlen, vvals, vpath, vroot, vbase, vr, vf⟩ := hv
  have gv : ∀ r, r ∉ csRegs ++ [.x1] ++ btAllRegs → v.getReg r = t.getReg r := fun r hr =>
    ((ur.trans u1r).trans vr).get hr
  have fuv : Frame u v (fun A => BtAllW lay (route index lay).2 (SIG + 16 * layIdx lay) A) :=
    (u1f.trans vf).mono (fun A _ h => by
      rcases h with h | h
      · exact h.elim
      · exact h)
  have ftv : Frame t v (fun A => CsW A ∨ BtAllW lay (route index lay).2 (SIG + 16 * layIdx lay) A) :=
    fu1.trans vf
  have nB : ∀ A, (A = IDXV ∨ A = ENC + 32) → ¬ BtAllW lay (route index lay).2 (SIG + 16 * layIdx lay) A := by
    intro A hA hw
    have := btAllW_layW hlay hw
    unfold BtAllW BtW LevW at hw
    simp only [btLev] at hw
    rcases hH with h6 | h6 <;> rw [h6] at hw <;> simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] at hw <;>
      sgo
  have hnx : LayNext sk cache (jalBT lay + 1) index ((levels.getD (height lay) []).getD 0 0) v :=
    { pc := vpc
      x2 := by rw [gv _ (by decide), h.x2]
      x26 := by rw [gv _ (by decide), h.x26]
      x27 := by rw [gv _ (by decide), h.x27]
      x31 := by rw [gv _ (by decide), h.x31]
      base := vbase
      hidx := h.hidx
      idx := by
        rw [ftv.get (by sgo) (fun hw => by
          rcases hw with hw | hw
          · unfold CsW at hw; sgo
          · exact nB _ (Or.inl rfl) hw)]
        exact h.idx
      enc := vroot
      c32 := by rw [fuv.get (by sgo) (nB _ (Or.inr rfl))]; exact uc32 }
  refine TBSim.bind (W₂ := 0) (hnext _ v hnx) (fun r w hw => ?_)
  rcases r with _ | previous
  · exact TBSim.pure hw
  obtain ⟨wh, wlen, wpieces, wf⟩ := hw
  refine TBSim.pure ⟨wh, by simp [wlen], fun lay' hlay' => ?_, ?_⟩
  · by_cases hlt : lay'.val < lay.val
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [wlen]; exact hlt),
        ← List.getD_eq_getElem?_getD]
      exact wpieces lay' hlt
    · have heq : lay' = lay := Fin.ext (by omega)
      subst heq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), wlen, Nat.sub_self]
      have nW : ∀ A, SIG + 16 * layIdx lay' ≤ A → A < SIG + 16 * (layIdx lay' + 43 + height lay') →
          ¬ LayW lay'.val A := fun A h1 h2 hw => hw.2 ⟨by omega, by omega⟩
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · rw [chainCount_low hlay] at hi
        have := vvals i (by rw [vlen]; exact hi)
        rw [show SIG + 16 * layIdx lay' + 16 * i = SIG + 16 * (layIdx lay' + i) by ring] at this
        exact this.frame wf (by omega) (nW _ (by omega) (by omega)) (nW _ (by omega) (by omega))
      · rw [chainCount_low hlay]
        have := vpath j (by simp [hj])
        rw [show SIG + 16 * layIdx lay' + 16 * 43 + 16 * j = SIG + 16 * (layIdx lay' + 43 + j) by ring] at this
        exact this.frame wf (by omega) (nW _ (by omega) (by omega)) (nW _ (by omega) (by omega))
  · exact (ftv.trans wf).mono (fun A _ hA => by
      rcases hA with (hA | hA) | hA
      · exact csW_layW hA
      · exact btAllW_layW hlay hA
      · exact layW_succ hA)

/-! ## The setup blocks of layers 2 and 1, the link to layer 0 -/

/-- Layer 2's setup (397..410) from layer 3's `build_tree` return. -/
theorem entry2 {index : Nat} {root : Digest} {v : MachineState} (h : LayNext sk cache 397 index root v) :
    ∃ t, Steps image v 14 14 t ∧ LayEntry sk cache 2 index root t ∧ Frame v t (fun _ => False) := by
  obtain ⟨t, st, tpc, tx1, tx8, tx15, tx16, tx17, tx18, tx14, tx9, tr, tf⟩ := blk397_spec v h.pc index h.hidx h.idx
  have g : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] → t.getReg r = v.getReg r :=
    fun r hr => tr.get hr
  refine ⟨t, st, ?_, tf⟩
  exact
    { pc := tpc
      x1 := tx1
      x2 := by rw [g _ (by decide), h.x2]
      x8 := tx8
      x9 := by rw [tx9, route_2]
      x14 := by rw [tx14, route_2]
      x15 := tx15
      x16 := tx16
      x17 := tx17
      x18 := by rw [tx18, route_2]
      x26 := by rw [g _ (by decide), h.x26]
      x27 := by rw [g _ (by decide), h.x27]
      x31 := by rw [g _ (by decide), h.x31]
      base := h.base.frame tf tr (by decide) (fun _ _ _ h => h)
      hlay := by decide
      hidx := h.hidx
      idx := by rw [tf.get (by sgo) (fun h => h)]; exact h.idx
      enc := h.enc.frame tf (by sgo) (fun h => h) (fun h => h)
      c32 := by rw [tf.get (by sgo) (fun h => h)]; exact h.c32 }

/-- Layer 1's setup (412..425) from layer 2's `build_tree` return. -/
theorem entry1 {index : Nat} {root : Digest} {v : MachineState} (h : LayNext sk cache 412 index root v) :
    ∃ t, Steps image v 14 14 t ∧ LayEntry sk cache 1 index root t ∧ Frame v t (fun _ => False) := by
  obtain ⟨t, st, tpc, tx1, tx8, tx15, tx16, tx17, tx18, tx14, tx9, tr, tf⟩ := blk412_spec v h.pc index h.hidx h.idx
  have g : ∀ r, r ∉ [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] → t.getReg r = v.getReg r :=
    fun r hr => tr.get hr
  refine ⟨t, st, ?_, tf⟩
  exact
    { pc := tpc
      x1 := tx1
      x2 := by rw [g _ (by decide), h.x2]
      x8 := tx8
      x9 := by rw [tx9, route_1]
      x14 := by rw [tx14, route_1]
      x15 := tx15
      x16 := tx16
      x17 := tx17
      x18 := by rw [tx18, route_1]
      x26 := by rw [g _ (by decide), h.x26]
      x27 := by rw [g _ (by decide), h.x27]
      x31 := by rw [g _ (by decide), h.x31]
      base := h.base.frame tf tr (by decide) (fun _ _ _ h => h)
      hlay := by decide
      hidx := h.hidx
      idx := by rw [tf.get (by sgo) (fun h => h)]; exact h.idx
      enc := h.enc.frame tf (by sgo) (fun h => h) (fun h => h)
      c32 := by rw [tf.get (by sgo) (fun h => h)]; exact h.c32 }

/-- Layer 0 from layer 1's `build_tree` return (427): `L0Spec`, as `SLPost`. -/
theorem layer0_link (hL0 : L0Spec sk cache) {index : Nat} {root : Digest} {v : MachineState}
    (h : LayNext sk cache 427 index root v) :
    TBSim image sk v L0Cost (signLayers (cacheDec cache) index 1 root) (SLPost v 1) := by
  refine TBSim.mono (hL0 index root v ⟨h.pc, h.base, h.hidx, h.idx, h.enc, h.c32⟩) le_rfl (fun r u hu => ?_)
  rcases r with _ | ps
  · exact hu
  obtain ⟨vals, path, rfl, uh, uv, up, uf⟩ := hu
  refine ⟨uh, rfl, fun lay hlay => ?_, uf.mono (fun A _ hA => hA)⟩
  have h0 : lay = 0 := Fin.ext (by omega)
  subst h0
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · have := uv i hi
    rw [show SIG + 2240 + 16 * i = SIG + 16 * (layIdx 0 + i) by simp [layIdx]; ring] at this
    exact this
  · have := up j hj
    rw [show SIG + 3168 + 16 * j = SIG + 16 * (layIdx 0 + chainCount 0 + j) by simp [layIdx, chainCount]; ring]
      at this
    exact this

/-! ## The layers -/

/-- Cycles of the layers below layer 1 (layer 0). -/
def layW1 : Nat := L0Cost
/-- Cycles from layer 2's `build_tree` return. -/
def layW2 : Nat := 14 + (csCost 1 + (1 + (btCost + layW1)))
/-- Cycles from layer 3's `build_tree` return. -/
def layW3 : Nat := 14 + (csCost 2 + (1 + (btCost + layW2)))
/-- Cycles of the layers from layer 3's `counter_search` entry. -/
def layersC : Nat := csCost 3 + (1 + (btCost + layW3))

/-- **The layers**: from layer 3's `counter_search` entry with the forest pk at `ENC`, the machine refines
`signLayers cache index 4 root`. -/
theorem layers_tbsim (hK : CounterSearchSpec sk) (hL0 : L0Spec sk cache) {index : Nat} {root : Digest}
    {t : MachineState} (h : LayEntry sk cache 3 index root t) :
    TBSim image sk t layersC (signLayers (cacheDec cache) index 4 root) (SLPost t 4) := by
  have L1 : ∀ root v, LayNext sk cache (jalBT 1 + 1) index root v →
      TBSim image sk v layW1 (signLayers (cacheDec cache) index (1 : Layer).val root) (SLPost v (1 : Layer).val) :=
    fun root v hv => layer0_link hL0 hv
  have L2 : ∀ root v, LayNext sk cache (jalBT 2 + 1) index root v →
      TBSim image sk v layW2 (signLayers (cacheDec cache) index (2 : Layer).val root) (SLPost v (2 : Layer).val) :=
    fun root v hv => by
      obtain ⟨t1, st, ht1, hf⟩ := entry1 hv
      exact TBSim.steps st (TBSim.mono (lower_layer hK ht1 L1) le_rfl (SLPost.pre hf))
  have L3 : ∀ root v, LayNext sk cache (jalBT 3 + 1) index root v →
      TBSim image sk v layW3 (signLayers (cacheDec cache) index (3 : Layer).val root) (SLPost v (3 : Layer).val) :=
    fun root v hv => by
      obtain ⟨t1, st, ht1, hf⟩ := entry2 hv
      exact TBSim.steps st (TBSim.mono (lower_layer hK ht1 L2) le_rfl (SLPost.pre hf))
  exact lower_layer hK h L3

end layer

end SigGolfCandidate.T3M.Sign
