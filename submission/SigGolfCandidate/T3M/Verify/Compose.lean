import SigGolfCandidate.T3M.Verify.LayerGood
import SigGolfCandidate.T3M.Verify.Compare
import SigGolfCandidate.T3M.Verify.MerkleSem
import SigGolfCandidate.T3M.Verify.FtsGood

/-! # The complete verifier: forest, signature layers, Merkle paths and root comparison

The accepting forest bound is 2675 cycles (n3-99 relabel 2676, digest header cut −1) at the 115-fold cap. The four
layers and final comparison cost 6014 cycles; the six-cycle load block gives 6020 after the forest. Thus the
accepting bound is 8695 cycles. Fuel 15418 and every-path cycle bound 15425 (`6 + lFuel 4 = 8050` after the
forest). The paired decoder lowers the top accepting transition by 46 cycles;
the last lower layer target 194 adds 9 cycles. The lower checksum register, leaf dispatch and
layer-3 index copy cuts and the top Merkle chunk-0 dispatch cut save 8 cycles. T3X: the lower layers read their WOTS
chain headers from a read-only image table (23 cycles per layer); T3Y: the 4096-aligned bank midpoints make each
lower layer's entry stub one `lui` (one more cycle per layer); BIG2: the Merkle levels store the header word 0 once
each from a register merged at level 0 (23 cycles); cryptogakusei's complemented top decoder tail (15e2fb43, 2 cycles);
BIG3 (T3Z): the top layer's chain heads read their header words from the same table (54 cycles) (layers
1338 + 1321 + 1321 + 1236, Merkle
168 + 168 + 181 + 273, compare 8). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height pad64 shortHash leafHash)

/-! ## The final continuation -/

/-- `afterFts`'s continuation for the result of the four layers: compare with `pk`. -/
def kFin (pk : Digest) : Option Digest → OracleComp HashSpec Obs := fun x =>
  ccM (match x with
    | some r => pure (r == pk)
    | _ => pure false) Kb

theorem kFin_none (pk : Digest) : kFin pk none = pure (false, 0) := by simp [kFin, Kb]

theorem kFin_some (pk r : Digest) : kFin pk (some r) = pure (r == pk, 0) := by simp [kFin, Kb]

/-! ## Layout facts -/

theorem trPc_vals : (∀ c, c < 64 → trPc 2 c = 5525 + 101 * c) ∧ (∀ c, c < 64 → trPc 1 c = 11989 + 101 * c) ∧
    (∀ c, c < 128 → trPc 0 c = 18460 + 134 * c) := by decide

theorem mkOff_vals : mkOff 3 0 6 = 36 ∧ mkOff 2 0 6 = 36 ∧ mkOff 1 0 7 = 42 ∧ mkOff 0 1 6 = 33 := by decide

theorem mkFin_succ (lay leaf : Nat) (hlay : lay < 4) :
    mkFin lay leaf + 1 = (if lay = 3 then 5525 + 101 * mkSh 3 0 leaf else if lay = 2 then 11989 + 101 * mkSh 2 0 leaf
      else if lay = 1 then 18460 + 134 * mkSh 1 0 leaf else 38675 + 53 * mkSh 0 1 leaf) := by
  obtain ⟨o3, o2, o1, o0⟩ := mkOff_vals
  interval_cases lay
  · simp only [mkFin, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl, o0, mkShp]; norm_num; omega
  · simp only [mkFin, show mkNch 1 - 1 = 0 from rfl, show mkBits 1 0 = 7 from rfl, o1, mkShp]; norm_num; omega
  · simp only [mkFin, show mkNch 2 - 1 = 0 from rfl, show mkBits 2 0 = 6 from rfl, o2, mkShp]; norm_num; omega
  · simp only [mkFin, show mkNch 3 - 1 = 0 from rfl, show mkBits 3 0 = 6 from rfl, o3, mkShp]; norm_num; omega

theorem ofNat4_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := by
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn]

/-! ## After a layer's root HASH -/

/-- The state before layer `n - 1` (its transition copy, `n ≥ 1`) or the compare (`n = 0`). -/
def RestIn (w : WBytes) (pk : Digest) (index n : Nat) (M : Digest) (s : MachineState) : Prop :=
  if n = 0 then CmpIn pk M s else LayerIn w pk index (n - 1) M s

/-- **After the root HASH of layer `n`**: the next layer's `LayerIn` or the compare's `CmpIn`. -/
theorem mkEnd_next (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (n : Nat) (hn : n < 4)
    (ends : List Digest) (u : MachineState) (hu : LeafOut w pk index (Fin.ofNat 4 n) ends u) (root : Digest)
    (t : MachineState) (ht : MkEnd w pk n (route index (Fin.ofNat 4 n)).1 u root t) :
    RestIn w pk index n root t := by
  have hv := ofNat4_val n hn
  have hleaf := leaf_lt index (Fin.ofNat 4 n)
  rw [hv] at hleaf
  have hpc := ht.pc
  rw [mkFin_succ n _ hn] at hpc
  by_cases h0 : n = 0
  · subst h0
    simp only [RestIn, if_true]
    refine ⟨⟨mkSh 0 1 (route index (Fin.ofNat 4 0)).1, mkSh_lt _ _ _, ?_, ?_, ?_⟩, ht.glob.2.2.1⟩
    · rw [hpc]; rfl
    · intro p hp
      simp only [cmpK,List.mem_append,List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact ht.glob.1 p hp
      · rw [ht.dstReg]
        congr 1
        exact (mkDst_chunk _).symm
    · change DigAt t (13336+48*(mkSh 0 1 (route index (Fin.ofNat 4 0)).1/32%2)) root
      rw [mkDst_chunk]
      exact ht.root
  · simp only [RestIn, if_neg h0]
    have hL0 : (Fin.ofNat 4 n : Layer) ≠ 0 := fun h => h0 (by have := congrArg Fin.val h; rw [hv] at this; exact this)
    have hkU : KnownOK (lfK n) u := by have := hu.glob.1; rwa [hv] at this
    have hsh : mkSh n 0 (route index (Fin.ofNat 4 n)).1 = (route index (Fin.ofNat 4 n)).1 := by
      simp only [mkSh, show mkLo n 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.div_one,
        show mkBits n 0 = hL n by simp [mkBits, h0]]
      exact Nat.mod_eq_of_lt hleaf
    have hn3 : n - 1 ≠ 3 := by omega
    obtain ⟨t2, t1, t0⟩ := trPc_vals
    refine ⟨by omega, hidx, ?_, ⟨?_, ht.glob.2⟩, ?_, ?_, ?_⟩
    · -- the transition copy
      refine ⟨(route index (Fin.ofNat 4 n)).1, ?_, ?_⟩
      · have hc : 2 ^ hL n ≤ nCopy (n - 1) := by
          obtain ⟨-, n2, n1, n0⟩ := nCopy_eq
          have hn' : n = 1 ∨ n = 2 ∨ n = 3 := by omega
          rcases hn' with rfl | rfl | rfl
          · rw [show 1 - 1 = 0 from rfl, n0]; decide
          · rw [show 2 - 1 = 1 from rfl, n1]; decide
          · rw [show 3 - 1 = 2 from rfl, n2]; decide
        omega
      · rw [hpc]
        have hn' : n = 1 ∨ n = 2 ∨ n = 3 := by omega
        rcases hn' with rfl | rfl | rfl
        · rw [if_neg (by decide), if_neg (by decide), if_pos rfl, hsh, t0 _ (by simpa [hL] using hleaf)]
        · rw [if_neg (by decide), if_pos rfl, hsh, t1 _ (by simpa [hL] using hleaf)]
        · rw [if_pos rfl, hsh, t2 _ (by simpa [hL] using hleaf)]
    · -- the registers of the next transition
      intro p hp
      simp only [preK, if_neg hn3, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, baseK] at hp
      have hkt := ht.known
      have hkp := ht.keep
      rcases hp with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ht.glob.1 _ (by simp [baseK])
      · exact ht.glob.1 _ (by simp [baseK])
      · rw [hkp .x27 (by simp [mkKeep]), hkU (.x27, BitVec.ofNat 64 (hw 1 n)) (by simp [lfK, postLf, leafK]),
          show n - 1 + 1 = n by omega]
      · rw [hkp .x24 (by simp [mkKeep]), hkU (.x24, 0x10000) (by simp [lfK, lfKeepK, h0])]
      · rw [hkp .x2 (by simp [mkKeep]), hkU (.x2, 0x3fe00) (by simp [lfK, lfKeepK])]
      · rw [hkp .x20 (by simp [mkKeep]), hkU (.x20, BitVec.ofNat 64 M1c) (by simp [lfK, lfKeepK, h0])]
      · rw [hkp .x21 (by simp [mkKeep]), hkU (.x21, BitVec.ofNat 64 M2c) (by simp [lfK, lfKeepK, h0])]
      · exact hkt _ (by simp)
      · rw [hkp .x28 (by simp [mkKeep]), hkU (.x28, BitVec.ofNat 64 (headerBank 0 0)) (by simp [lfK, lfKeepK])]
      all_goals exact hkt _ (by simp [mkKc])
    · -- the remaining index bits
      rw [show rReg (n - 1) = .x30 by simp [rReg, hn3], ht.keep .x30 (by simp [mkKeep]), hu.t5,
        tree_next index _ hL0, hv]
    · have := ht.root
      simpa [mkDst, h0] using this
    · have := ht.orig
      rw [show layerEnd (n - 1) = mkBase n by rw [← hv, layerEnd_prev _ hL0, ← mkBase_eq]]
      exact this

/-! ## The layers -/

/-- Cycles of layers `n - 1 .. 0` (V1's `layerCost` at `Z = 0` and V3's `mkCyc`) and the compare (8). -/
def lCyc : Nat → Nat
  | 0 => 8
  | n + 1 => layerCost n 0 + mkCyc n + lCyc n

/-- Steps of the same. -/
def lFuel : Nat → Nat
  | 0 => 9
  | n + 1 => layerFuel n + mkFuel n + lFuel n

theorem lCyc_4 : lCyc 4 = 6014 := by decide
theorem lFuel_4 : lFuel 4 = 8021 := by decide

/-- **The layers and the compare**: from `RestIn … n M s`, `layersP w index n M` continued by `kFin pk`. -/
theorem layers_good (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ M s, RestIn w pk index n M s →
      GoodQ s (lFuel n) (lCyc n) Q (lCyc n) (ccM (layersP w index n M) (kFin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ M s hs
    simp only [RestIn, if_true] at hs
    rw [show layersP w index 0 M = pure (some M) from rfl, ccM_pure, kFin_some]
    exact cmp_good pk M s hs Q hQ
  | succ n ih =>
    intro hn M s hs
    have hs' : LayerIn w pk index n M s := by simpa [RestIn] using hs
    have hv := ofNat4_val n (by omega)
    have hg := layersP_good w pk index n (by omega) M s hs' (kFin pk) (kFin_none pk) (lFuel n + mkFuel n)
      (lCyc n + mkCyc n) (lCyc n + mkCyc n) Q (fun ends u hu => by
        rw [ccM_bind]
        have hm := merkle_good w pk index (Fin.ofNat 4 n) ends u hidx hu
          (fun r => ccM (layersP w index n r) (kFin pk)) (lFuel n) (lCyc n) (lCyc n) Q
          (fun root t ht => ih (by omega) root t (mkEnd_next w pk index hidx n (by omega) ends u hu root t
            (by rw [hv] at ht; exact ht)))
        rw [hv] at hm
        exact hm)
    exact hg.mono (by simp only [lFuel]; omega) (by simp only [lCyc]; omega) (fun q => ⟨q, by simp only [lCyc]; omega⟩)

/-! ## From V2's `FtsOut` and from the initial state -/

/-- **After the FTS** (V2's `verifyP_good_fts` interface): from `FtsOut`, `afterFts` — the four layers and the
compare — with fuel and every-path bound 8050 (`6 + lFuel 4 = 8050`) and accepting cycles 6020 (`6 + lCyc 4`; T3K: the
6-cycle load block at 656 before layer 3's copy at 662). -/
theorem after_good (pk : Digest) (w : WBytes) (Q : Prop) (hQ : Q) (a : HashOutput) (root : Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ root u) :
    GoodQ u 8050 8050 Q 6020 (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb) := by
  have hidx : a.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ root u hidx h.glob h.idx h.pc h.root h.wit
  have hg := layers_good w pk _ hidx Q hQ 4 le_rfl root t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb =
      ccM (layersP w (a.toNat % 2 ^ 31) 4 root) (kFin pk) := by
    unfold afterFts; rw [ccM_bind]; rfl
  rw [e]
  rw [lFuel_4, lCyc_4] at hg
  exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)

/-- **The whole verify run**: from the initial state, every run finishes within 15425 cycles with fuel 15418, and
accepting runs take at most `8695 = 2675 + 6020` cycles; the observation is `countCalls (mrealize 0 (verifyP m pk w))`. -/
theorem verifyP_good (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitOK m pk w s) :
    GoodQ s 15418 15425 True 8695 (ccM (verifyP m pk w) Kb) :=
  verifyP_good_fts m pk w s hs 8050 6020 True (fun a root u h => after_good pk w True trivial a root u h)

end SigGolfCandidate.T3M
