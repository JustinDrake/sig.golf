import SigGolfCandidate.T3M.Verify.LayerGood
import SigGolfCandidate.T3M.Verify.Compare
import SigGolfCandidate.T3M.Verify.MerkleSem
import SigGolfCandidate.T3M.Verify.FtsGood

/-! # The complete verifier: forest, signature layers, Merkle paths and root comparison

The reversed-label forest with three checked side bits costs at most2644 cycles
from the initial state. The four layers and final comparison cost5938 cycles;
the five-cycle loader gives5903 after the forest. The accepting bound is8547.
Fuel15477 and the all-input cycle bound15484 retain conservative rejection margins.
-/

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

theorem trPc_vals : (∀ c, c < 64 → trPc 2 c = 5516 + 101 * c) ∧ (∀ c, c < 64 → trPc 1 c = 11980 + 101 * c) ∧
    (∀ c, c < 128 → trPc 0 c = 18450 + 134 * c) := by decide

theorem mkOff_vals : mkOff 3 0 6 = 34 ∧ mkOff 2 0 6 = 34 ∧ mkOff 1 0 7 = 40 ∧ mkOff 0 1 6 = 33 := by decide

theorem mkFin_succ (lay leaf : Nat) (hlay : lay < 4) :
    mkFin lay leaf + 1 = (if lay = 3 then 5521 + 101 * mkSh 3 0 leaf else if lay = 2 then 11985 + 101 * mkSh 2 0 leaf
      else if lay = 1 then 18455 + 134 * mkSh 1 0 leaf else 38669 + 53 * mkSh 0 1 leaf) := by
  obtain ⟨o3, o2, o1, o0⟩ := mkOff_vals
  interval_cases lay
  · simp only [mkFin, mkPack, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl, o0, mkShp]; norm_num; omega
  · simp only [mkFin, mkPack, show mkNch 1 - 1 = 0 from rfl, show mkBits 1 0 = 7 from rfl, o1, mkShp]; norm_num; omega
  · simp only [mkFin, mkPack, show mkNch 2 - 1 = 0 from rfl, show mkBits 2 0 = 6 from rfl, o2, mkShp]; norm_num; omega
  · simp only [mkFin, mkPack, show mkNch 3 - 1 = 0 from rfl, show mkBits 3 0 = 6 from rfl, o3, mkShp]; norm_num; omega

theorem ofNat4_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := by
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn]

/-- E8: the copy of layer `n - 1` follows HASH `h - 1` of layer `n`'s shape block (`n = 1, 2, 3`). -/
theorem mkEc_last_vals : (∀ leaf, leaf < 128 → mkEc 1 leaf (hL 1 - 1) + 1 = trPc 0 leaf) ∧
    (∀ leaf, leaf < 64 → mkEc 2 leaf (hL 2 - 1) + 1 = trPc 1 leaf) ∧
    (∀ leaf, leaf < 64 → mkEc 3 leaf (hL 3 - 1) + 1 = trPc 2 leaf) := by decide +kernel

theorem mkEc_last (n leaf : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 3) (hleaf : leaf < 2 ^ hL n) :
    mkEc n leaf (hL n - 1) + 1 = trPc (n - 1) leaf := by
  obtain ⟨e1, e2, e3⟩ := mkEc_last_vals
  rcases hn with rfl | rfl | rfl
  · exact e1 leaf (by simpa [hL] using hleaf)
  · exact e2 leaf (by simpa [hL] using hleaf)
  · exact e3 leaf (by simpa [hL] using hleaf)

theorem pad_lo32 (x : Digest) : (dlo x).toNat / 2 ^ 32 = (x.extractLsb' 32 96).toNat % 2 ^ 32 := by
  simp only [dlo, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  norm_num
  omega

theorem pad_hi (x : Digest) : dhi x = BitVec.ofNat 64 ((x.extractLsb' 32 96).toNat / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [dhi, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  norm_num
  omega

/-! ## After a layer's Merkle phase -/

/-- The state before layer `n - 1` (its transition copy, `n ≥ 1`) or the compare (`n = 0`). -/
def RestIn (w : WBytes) (pk : Digest) (index n : Nat) (M : T3.LayerMessage) (s : MachineState) : Prop :=
  if n = 0 then CmpIn pk M.1 s else LayerIn w pk index (n - 1) M s

/-- **After the root HASH of the top layer**: the compare's `CmpIn`. -/
theorem mkEnd_cmp (w : WBytes) (pk : Digest) (index : Nat) (ends : List Digest) (u : MachineState)
    (hu : LeafOut w pk index (Fin.ofNat 4 0) ends u) (root : Digest)
    (t : MachineState) (ht : MkEnd w pk 0 (route index (Fin.ofNat 4 0)).1 u root t) :
    CmpIn pk root t := by
  have hleaf := leaf_lt index (Fin.ofNat 4 0)
  have hpc := ht.pc
  rw [mkFin_succ 0 _ (by decide)] at hpc
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

/-- **After HASH `h - 1` of a lower layer `n`** (E8): the next layer's `LayerIn`, its message the root's children
(node and sibling of block `h - 1`) with the block's pad bytes, in place. -/
theorem mkAfter_next (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (n : Nat) (hn : n < 4)
    (h0 : n ≠ 0) (ends : List Digest) (u : MachineState) (hu : LeafOut w pk index (Fin.ofNat 4 n) ends u)
    (v : Digest) (t : MachineState) (ht : MAfter w pk n (route index (Fin.ofNat 4 n)).1 u (hL n - 1) v t) :
    LayerIn w pk index (n - 1) (T3.pairOf (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n))
      (wpath w (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n) - 1))
      ((wmerklePad w (Fin.ofNat 4 n) (height (Fin.ofNat 4 n) - 1)).extractLsb' 32 96) v) t := by
  have hv := ofNat4_val n hn
  have hleaf := leaf_lt index (Fin.ofNat 4 n)
  rw [hv] at hleaf
  have hL0 : (Fin.ofNat 4 n : Layer) ≠ 0 := fun h => h0 (by have := congrArg Fin.val h; rw [hv] at this; exact this)
  have hkU : KnownOK (lfK n) u := by have := hu.glob.1; rwa [hv] at this
  have hh : height (Fin.ofNat 4 n) = hL n := by rw [← hL_eq, hv]
  have hn' : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  have hB : encB (n - 1) = mkBlk n (hL n - 1) ∧ mkBo n (hL n - 1) = mkBase n ∧ mkBase n = layerEnd (n - 1) ∧
      6 ≤ hL n := by
    rcases hn' with rfl | rfl | rfl <;> decide
  obtain ⟨hB8, hBlo, hBhi, hBase, -, -, -⟩ := mkBo_facts n (hL n - 1) hn (by omega)
  have hn3 : n - 1 ≠ 3 := by omega
  have hmb : merkleBlock (Fin.ofNat 4 n) (height (Fin.ofNat 4 n) - 1) = mkBo n (hL n - 1) := by
    rw [hh, ← mkBo_eq, hv]
  have hkt : KnownOK (mkK n ++ [(.x11, 64)]) t := by
    have := ht.known
    simpa [mkLvlK, show hL n - 1 ≠ 0 by omega] using this
  refine ⟨by omega, hidx, ?_, ⟨?_, ht.glob.2⟩, ?_, ?_, ?_, Or.inr ⟨mkCur n (hL n - 1)
    ((route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2), ?_, ht.dstReg⟩⟩
  · -- the transition copy
    refine ⟨(route index (Fin.ofNat 4 n)).1, ?_, ?_⟩
    · have hc : 2 ^ hL n ≤ nCopy (n - 1) := by
        obtain ⟨-, n2, n1, n0⟩ := nCopy_eq
        rcases hn' with rfl | rfl | rfl
        · rw [show 1 - 1 = 0 from rfl, n0]; decide
        · rw [show 2 - 1 = 1 from rfl, n1]; decide
        · rw [show 3 - 1 = 2 from rfl, n2]; decide
      omega
    · rw [ht.pc]
      exact congrArg pcOf (mkEc_last n _ hn' hleaf)
  · -- the registers of the next transition
    intro p hp
    simp only [preK, if_neg hn3, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, baseK] at hp
    rw [show n - 1 + 1 = n by omega] at hp
    have hkp := ht.keep
    rcases hp with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ht.glob.1 _ (by simp [baseK])
    · exact ht.glob.1 _ (by simp [baseK])
    · rw [hkp .x27 (by simp [mkKeep]), hkU (.x27, BitVec.ofNat 64 (hw 1 n)) (by simp [lfK, postLf, leafK])]
    · rw [hkp .x24 (by simp [mkKeep]), hkU (.x24, 0x10000) (by simp [lfK, lfKeepK, h0])]
    · rw [hkp .x2 (by simp [mkKeep]), hkU (.x2, 0x3fe00) (by simp [lfK, lfKeepK])]
    · rw [hkp .x20 (by simp [mkKeep]), hkU (.x20, BitVec.ofNat 64 M1c) (by simp [lfK, lfKeepK, h0])]
    · rw [hkp .x21 (by simp [mkKeep]), hkU (.x21, BitVec.ofNat 64 M2c) (by simp [lfK, lfKeepK, h0])]
    · exact hkt _ (by simp)
    · rw [hkp .x28 (by simp [mkKeep]), hkU (.x28, BitVec.ofNat 64 (leaf28 n)) (by simp [lfK, lfKeepK])]
      rcases hn' with rfl | rfl | rfl <;> rfl
    all_goals first
      | solve | refine hkt _ ?_; simp [mkK]
      | rw [hkp .x19 (by simp [mkKeep]), hkU (.x19, BitVec.ofNat 64 (2^62)) (by simp [lfK, lfKeepK, h0])]
  · -- the remaining index bits
    rw [show rReg (n - 1) = .x30 by simp [rReg, hn3], ht.keep .x30 (by simp [mkKeep]), hu.t5,
      tree_next index _ hL0, hv]
  · -- the message: the node and the sibling of block `h - 1`, its pad
    have hO := ht.orig
    have hnode := ht.node
    have hbl := mkBit_lt (route index (Fin.ofNat 4 n)).1 (hL n - 1)
    have hpad := hO.dig (mkBo n (hL n - 1) + 32) (by omega) (by unfold WX; omega)
      ⟨by omega, by omega, by unfold mkCur mkBlk; interval_cases (route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2 <;> omega⟩
      ⟨by omega, by omega, by unfold mkCur mkBlk; interval_cases (route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2 <;> omega⟩
    have e32 : WIT + (mkBo n (hL n - 1) + 32) = mkBlk n (hL n - 1) + 32 := by unfold WIT mkBlk; omega
    rw [e32, show mkBlk n (hL n - 1) + 32 + 8 = mkBlk n (hL n - 1) + 40 by omega] at hpad
    rw [hB.1]
    unfold T3.pairOf wpath wmerklePad
    rw [hmb, hh]
    rcases (show (route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2 = 0 ∨
        (route index (Fin.ofNat 4 n)).1 / 2 ^ (hL n - 1) % 2 = 1 by omega) with hb | hb
    · rw [hb] at hnode hO
      simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide, if_false]
      have hsib := hO.dig (mkBo n (hL n - 1) + 48) (by omega) (by unfold WX; omega)
        ⟨by omega, by omega, Or.inr (by unfold mkCur mkBlk; omega)⟩ ⟨by omega, by omega, Or.inr (by unfold mkCur mkBlk; omega)⟩
      have e48 : WIT + (mkBo n (hL n - 1) + 48) = mkBlk n (hL n - 1) + 48 := by unfold WIT mkBlk; omega
      rw [e48] at hsib
      refine ⟨?_, hsib, ?_, ?_⟩
      · simpa [mkCur] using hnode
      · rw [hpad.1]; exact pad_lo32 _
      · rw [hpad.2]; exact pad_hi _
    · rw [hb] at hnode hO
      simp only [hb, show (1 : Nat) ≠ 0 by decide, if_false, sibOff, if_true, Nat.add_zero]
      have hsib := hO.dig (mkBo n (hL n - 1)) (by omega) (by unfold WX; omega)
        ⟨by omega, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩ ⟨by omega, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩
      have e0 : WIT + mkBo n (hL n - 1) = mkBlk n (hL n - 1) := by unfold WIT mkBlk; omega
      rw [e0] at hsib
      refine ⟨hsib, ?_, ?_, ?_⟩
      · simpa [mkCur] using hnode
      · rw [hpad.1]; exact pad_lo32 _
      · rw [hpad.2]; exact pad_hi _
  · -- the witness of the layers below, original
    intro j hj ⟨h1, h2⟩
    exact ht.orig j hj ⟨h1, by omega, Or.inl (by unfold mkCur mkBlk; omega)⟩
  · -- full E8: the output pointer is the node slot of block `h - 1`
    have hbl := mkBit_lt (route index (Fin.ofNat 4 n)).1 (hL n - 1)
    simp only [dstSet, if_neg hn3, List.mem_cons, List.not_mem_nil, or_false, mkCur, hB.1]
    omega

/-! ## The layers -/

/-- Cycles of layers `n - 1 .. 0` (V1's `layerCost` at `Z = 0`, V3's `mkCyc` at the top and `mkCycP` below) and the
compare (8). -/
def lCyc : Nat → Nat
  | 0 => 8
  | n + 1 => layerCost n 0 + (if n = 0 then mkCyc n else mkCycP n) + lCyc n

/-- Steps of the same. -/
def lFuel : Nat → Nat
  | 0 => 9
  | n + 1 => layerFuel n + (if n = 0 then mkFuel n else mkFuelP n) + lFuel n

theorem lCyc_4 : lCyc 4 = 5898 := by decide
theorem lFuel_4 : lFuel 4 = 7989 := by decide

/-- **The layers and the compare**: from `RestIn … n M s`, `layersP w index n M` continued by `kFin pk`. -/
theorem layers_good (w : WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ M s, RestIn w pk index n M s →
      GoodQ s (lFuel n) (lCyc n) Q (lCyc n) (ccM (layersP w index n M) (kFin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ M s hs
    simp only [RestIn, if_true] at hs
    rw [show layersP w index 0 M = pure (some M.1) from rfl, ccM_pure, kFin_some]
    exact cmp_good pk M.1 s hs Q hQ
  | succ n ih =>
    intro hn M s hs
    have hs' : LayerIn w pk index n M s := by simpa [RestIn] using hs
    have hv := ofNat4_val n (by omega)
    by_cases h0 : n = 0
    · subst h0
      have hg := layersP_good_top w pk index M s hs' (kFin pk) (kFin_none pk) (lFuel 0 + mkFuel 0)
        (lCyc 0 + mkCyc 0) (lCyc 0 + mkCyc 0) Q (fun ends u hu => by
          rw [ccM_bind]
          have hm := merkle_good w pk index (Fin.ofNat 4 0) ends u hidx hu
            (fun r => ccM (layersP w index 0 (r, 0, 0)) (kFin pk)) (lFuel 0) (lCyc 0) (lCyc 0) Q
            (fun root t ht => ih (by omega) (root, 0, 0) t (by
              simp only [RestIn, if_true]
              exact mkEnd_cmp w pk index ends u hu root t (by rw [hv] at ht; exact ht))) hv
          rw [hv] at hm
          exact hm)
      exact hg.mono (by simp only [lFuel, ↓reduceIte]; omega) (by simp only [lCyc, ↓reduceIte]; omega)
        (fun q => ⟨q, by simp only [lCyc, ↓reduceIte]; omega⟩)
    · have hg := layersP_good_low w pk index n (by omega) h0 M s hs' (kFin pk) (kFin_none pk) (lFuel n + mkFuelP n)
        (lCyc n + mkCycP n) (lCyc n + mkCycP n) Q (fun ends u hu => by
          have hh : height (Fin.ofNat 4 n) = hL n := by rw [← hL_eq, hv]
          have e : (leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
              merklePairP w index (Fin.ofNat 4 n) >>= layersP w index n) =
              (leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
                fun v => (List.range (hL n - 1)).foldlM (mkStep w index (Fin.ofNat 4 n)) v) >>= fun node =>
                layersP w index n (T3.pairOf (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n))
                  (wpath w (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n) - 1))
                  ((wmerklePad w (Fin.ofNat 4 n) (height (Fin.ofNat 4 n) - 1)).extractLsb' 32 96) node) := by
            simp only [bind_assoc]
            congr 1; funext v
            rw [merklePairP_eq, hh]
            simp only [bind_assoc, pure_bind]
          rw [e, ccM_bind]
          have hm := merkle_pair_good w pk index (Fin.ofNat 4 n) ends u hidx hu
            (fun node => ccM (layersP w index n (T3.pairOf (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n))
              (wpath w (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).1 (height (Fin.ofNat 4 n) - 1))
              ((wmerklePad w (Fin.ofNat 4 n) (height (Fin.ofNat 4 n) - 1)).extractLsb' 32 96) node)) (kFin pk))
            (lFuel n) (lCyc n) (lCyc n) Q
            (fun node t ht => ih (by omega) _ t (by
              simp only [RestIn, if_neg h0]
              exact mkAfter_next w pk index hidx n (by omega) h0 ends u hu node t (by rw [hv] at ht; exact ht)))
          rw [hv] at hm
          exact hm)
      exact hg.mono (by simp only [lFuel, if_neg h0]; omega) (by simp only [lCyc, if_neg h0]; omega)
        (fun q => ⟨q, by simp only [lCyc, if_neg h0]; omega⟩)

/-! ## From V2's `FtsOut` and from the initial state -/

/-- **After the FTS** (V2's `verifyP_good_fts` interface): from `FtsOut`, `afterFts` — the four layers and the
compare — with fuel and every-path bound 8061 (`5 + lFuel 4 = 7994`) and accepting cycles 5903 (`5 + lCyc 4`; the
five-cycle load block starts at630 and preserves the carried constants). -/
theorem after_good (pk : Digest) (w : WBytes) (Q : Prop) (hQ : Q) (a : HashOutput) (root : Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ root u) :
    GoodQ u 8061 8061 Q 5903 (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb) := by
  have hidx : a.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ root u hidx h.glob h.idx h.pc h.root h.wit
  have hg := layers_good w pk _ hidx Q hQ 4 le_rfl (root, 0, 0) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb =
      ccM (layersP w (a.toNat % 2 ^ 31) 4 (root, 0, 0)) (kFin pk) := by
    unfold afterFts; rw [ccM_bind]; rfl
  rw [e]
  rw [lFuel_4, lCyc_4] at hg
  exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)

/-- **The whole verify run**: from the initial state, every run finishes within 15484 cycles with fuel 15477, and
accepting runs take at most `8547 = 2644 + 5903` cycles; the observation is `countCalls (mrealize 0 (verifyP m pk w))`. -/
theorem verifyP_good (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitOK m pk w s) :
    GoodQ s 15477 15484 True 8547 (ccM (verifyP m pk w) Kb) :=
  verifyP_good_fts m pk w s hs 8061 5903 True (fun a root u h => after_good pk w True trivial a root u h)

end SigGolfCandidate.T3M
