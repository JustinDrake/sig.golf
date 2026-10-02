import SigGolfCandidate.T3M.Verify.LeafSem

/-! # V1 layers: one layer of `layersP`, from `LayerIn` to `LeafOut` (`layer_good`), and its cost

W's layer loop `layersP w index (n + 1) M` (layer `lay = n`) is `layerHead w index lay M R` (`layersP_succ`):
the counter check, the encoding query, the decode, the chains with their pads (`chainsP`, `layerP`'s `mapM`), then
`R ends` = the leaf pk (`leafHash`), the Merkle path (`merkleP`) and the remaining layers.

**`layer_good`**: from `LayerIn w pk index lay M s` (V2's `FtsOut` for layer 3, V3's Merkle end for layers 2, 1, 0),
given that every `LeafOut w pk index lay ends u` (V3's Merkle shape blocks) continues as `R ends`, the machine
refines `layerHead w index lay M R`: the counter rejection (HALT(1)), the encoding HASH, the decode rejections
(HALT(1)), the 43 / 58 chain queries, the leaf-pk block — with fuel `layerFuel lay` and at most `layerCost lay 0`
cycles on every path (all runs and the accepting ones).

**`layerCost lay Z`** = `stepsA + 8 + B + leaf-pk block + chainCost0 lay − Z`: the cycles from `LayerIn` to
`LeafOut` of a run whose digits have the max-digit savings `Z` (one cycle per maximal digit, two for the lower
checksum chain: `LCtx.zSum 0 43` resp. `QCtx.topZ`; exactly `chainCost0 lay − Z` for the chains by
`LCtx.lowCost_accept` / `QCtx.topCost_accept`); `layerCost lay 0` = 1377, 1349, 1349, 1273 for layers 3, 2, 1, 0
(sum 5359). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 width shortHash leafHash)

/-! ## The layer as a program -/

/-- Core's chains of layer `lay` with the witness pads and values (`layerP`'s `mapM`). -/
def chainsP (w : WBytes) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : T3.M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (2 ^ width lay i.val - 1 - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wvalue w lay i.val)

/-- `layerP`'s Merkle path from the leaf value (V3's part). -/
def merkleP (w : WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay (route index lay).1 j.val
    let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
      pair.1 (wmerklePad w lay j.val) pair.2) value

theorem layerP_eq (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerP w index lay digits = chainsP w lay (route index lay).2 (route index lay).1 digits >>= fun ends =>
      leafHash lay (route index lay).2 (route index lay).1 ends >>= merkleP w index lay := by
  unfold layerP chainsP merkleP
  generalize route index lay = p
  obtain ⟨leaf, tree⟩ := p
  rfl

/-- **One layer of `layersP` up to the chain ends**, continued by `R`. -/
def layerHead {β : Type} (w : WBytes) (index : Nat) (lay : Layer) (M : Digest)
    (R : List Digest → T3.M (Option β)) : T3.M (Option β) :=
  if (wctr w lay).toNat ≥ counterLimit then pure none else
  shortHash (encodingInput lay (route index lay).2 (route index lay).1 M (wctr w lay)) >>= fun answer =>
    match decode lay answer with
    | none => pure none
    | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R

/-- **W's layer loop, one step**: layer `n` is `layerHead` continued by the leaf pk, the Merkle path and the
layers below. -/
theorem layersP_succ (w : WBytes) (index n : Nat) (M : Digest) :
    layersP w index (n + 1) M = layerHead w index (Fin.ofNat 4 n) M (fun ends =>
      leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 ends >>=
        merkleP w index (Fin.ofNat 4 n) >>= layersP w index n) := by
  rw [layersP]
  unfold layerHead
  split_ifs with h
  · rfl
  · simp only [layerP_eq, bind_assoc]
    generalize hr : route index (Fin.ofNat 4 n) = p
    obtain ⟨leaf, tree⟩ := p
    simp only
    congr 1; funext answer
    cases decode (Fin.ofNat 4 n) answer <;> rfl

/-! ## Costs -/

/-- Steps / cycles of the decode part B up to the chain code (lower 31 / 34, top 51 / 57). -/
def stB (lay : Nat) : Nat := if lay = 0 then 51 else 31
def cyB (lay : Nat) : Nat := if lay = 0 then 57 else 34
/-- The chain phase's accepting cycles without maximal digits: lower `3036 − 9 target`, top `1180`. -/
def chainCost0 (lay : Nat) : Nat := if lay = 0 then 1180 else 3036 - 9 * tgtL lay
/-- The chain phase's steps on every path. -/
def chainFuel (lay : Nat) : Nat := if lay = 0 then 2321 else 1720

/-- **The cycles of one layer from `LayerIn` to `LeafOut`** with the max-digit savings `Z`: A (`stepsA`), the
encoding HASH (8), B, the leaf-pk block, the chains `chainCost0 lay − Z`. -/
def layerCost (lay Z : Nat) : Nat := stepsA lay + 8 + cyB lay + lfSteps lay + chainCost0 lay - Z

/-- The steps of one layer on every path. -/
def layerFuel (lay : Nat) : Nat := stepsA lay + 1 + stB lay + chainFuel lay + lfSteps lay

theorem layerCost_vals :
    layerCost 3 0 = 1375 ∧ layerCost 2 0 = 1348 ∧ layerCost 1 0 = 1348 ∧ layerCost 0 0 = 1273 := by decide

theorem layerFuel_vals :
    layerFuel 3 = 1795 ∧ layerFuel 2 = 1777 ∧ layerFuel 1 = 1777 ∧ layerFuel 0 = 2401 := by decide

/-! ## Decode facts -/

theorem ckOf_lt (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (ds : List Nat)
    (hds : decode lay (a.extractLsb' 0 128) = some ds) : ckOf lay a < 8 := by
  rw [decode_lower lay hlay] at hds
  split_ifs at hds with h1 h2
  unfold ckOf; rw [tgtL_eq]; exact h2

theorem decode_top_sum (value : Digest) (ds : List Nat) (h : decode 0 value = some ds) :
    ds = dataDigits 0 value ∧ (dataDigits 0 value).sum = 126 := by
  unfold decode at h
  by_cases h1 : value.toNat ≥ 2 ^ T3.encodedBits 0
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    dsimp only at h
    rw [if_pos rfl] at h
    by_cases h2 : (dataDigits 0 value).sum = target 0
    · rw [if_pos h2] at h
      exact ⟨(Option.some.inj h).symm, h2⟩
    · rw [if_neg h2] at h; cases h

theorem s6v_chainBlock (lay : Layer) (h : lay ≠ 0) : s6v lay.val = 0x800 + chainBlock lay 42 + 1024 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide

theorem chainCount_top : chainCount (0 : Layer) = 58 := by decide

/-! ## The exact accepting cost -/

/-- **The accepting cost of a lower layer is `layerCost lay Z`**: on an accepted encoding (`decode = some ds`) the
run from `LayerIn` to `LeafOut` — A (`stepsA`), the encoding HASH (8), B (34), the chain phase (`lowCost`), the
leaf-pk block (11) — costs `layerCost lay Z` cycles with `Z = zSum 0 43` (the max-digit savings). -/
theorem layerCost_low (w : WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (p : Nat)
    (ds : List Nat) (hds : decode lay (a.extractLsb' 0 128) = some ds) :
    stepsA lay.val + 8 + 34 + (lctxOf w index lay a p).lowCost + 10 =
      layerCost lay.val ((lctxOf w index lay a p).zSum 0 43) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hD := lctx_digits w index lay a p hlay ds hds
  have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
  have hck : (lctxOf w index lay a p).ck < 8 := ckOf_lt lay hlay a ds hds
  have hacc := (lctxOf w index lay a p).lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
  rw [← tgtL_eq] at hacc
  simp only [layerCost, cyB, lfSteps, chainCost0, if_neg h0]
  omega

/-- **The accepting cost of the top layer is `layerCost 0 Z`** (`Z = topZ`; B 57 cycles, the leaf-pk block 13). -/
theorem layerCost_top (w : WBytes) (index : Nat) (a : BitVec 256) (p : Nat) (ds : List Nat)
    (hds : decode 0 (a.extractLsb' 0 128) = some ds) (hfit : (qctxOf w index a p).TopFit (a.extractLsb' 0 128)) :
    stepsA 0 + 8 + 57 + (qctxOf w index a p).topCost + 13 = layerCost 0 ((qctxOf w index a p).topZ - 5) := by
  obtain ⟨-, hsum⟩ := decode_top_sum _ ds hds
  have hsave := (qctxOf w index a p).topZ_ge_five hfit hsum
  have hacc := (qctxOf w index a p).topCost_accept hfit hsum
  have e : layerCost 0 ((qctxOf w index a p).topZ - 5) = 15 + 8 + 57 + 13 + 1180 - ((qctxOf w index a p).topZ - 5) := rfl
  rw [e, show stepsA 0 = 15 from rfl]
  omega

/-! ## One layer -/

/-- **A lower layer** (`lay ≠ 0`): `layerHead` from `LayerIn` to `LeafOut`. -/
theorem layer_good_low (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (M : Digest)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCost lay.val 0)
      (ccM (layerHead w index lay M R) K) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hidx := hs.idx
  have hA := encA_step w pk index lay M s hs
  have hT : 9 * tgtL lay.val ≤ 3036 := by fin_cases lay <;> decide
  have hfuel : layerFuel lay.val = stepsA lay.val + 1 + 31 + 1720 + 10 := by simp [layerFuel, stB, chainFuel, lfSteps, h0]
  have hcost : layerCost lay.val 0 = stepsA lay.val + 8 + 34 + 10 + (3036 - 9 * tgtL lay.val) := by
    simp only [layerCost, cyB, lfSteps, chainCost0, if_neg h0]; omega
  unfold layerHead
  by_cases hctr : (wctr w lay).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    have hblk := blocks_encodingInput lay (route index lay).2 (route index lay).1 M (wctr w lay)
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + 10 + 1720 + 31) (C + 10 + (3036 - 9 * tgtL lay.val) + 34)
        Q (A + 10 + (3036 - 9 * tgtL lay.val) + 34)
        (ccM (match decode lay (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R) K) := by
      intro a
      have hB := encB_step w pk index lay hlay c hc hidx t hpre a
      cases hds : decode lay (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure, hK0]
        obtain ⟨v, k, cy, hst', hf', h5', h10', hk, hcy⟩ := hB.1 hds
        exact GoodQ.steps' hst' (GoodQ.reject (Q := Q) (A := 0) hf' h5' h10') (by omega) (by omega)
          (fun hq => ⟨hq, by omega⟩)
      | some ds =>
        dsimp only
        obtain ⟨s0, hst0, hLok, hkn, hO0, hIn, hG0, hOr0, h23, h30⟩ := hB.2 (by rw [hds]; simp)
        set L := lctxOf w index lay a (trPc lay.val c) with hLd
        have hD := lctx_digits w index lay a (trPc lay.val c) hlay ds hds
        have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
        have hck : L.ck < 8 := ckOf_lt lay hlay a ds hds
        have hacc := L.lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
        rw [← tgtL_eq] at hacc
        have hP := L.lowP_eq hlay rfl ds hD (s6v_chainBlock lay hlay)
        have hG := L.lower_good hLok rfl rfl hck hkn hO0 (fun ends => ccM (R ends) K) (N + 10) (C + 10) (A + 10) Q
          (fun ends t ht => by
            obtain ⟨u, hstu, hu⟩ := leafL_step w pk index lay hlay c hc hidx a s0 hkn hG0 hOr0 h23 h30 ends t ht
            exact GoodQ.steps' hstu (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩))
          s0 hIn
        have e : chainsP w lay (route index lay).2 (route index lay).1 ds = L.lowP := by
          rw [hP]; unfold chainsP; rw [LCtx.chainCount_lower lay hlay]; rfl
        rw [ccM_bind, e]
        exact GoodQ.steps' hst0 hG (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have := GoodQ.shortHash_bind (f := fun answer => match decode lay answer with
      | none => pure none
      | some digits => chainsP w lay (route index lay).2 (route index lay).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)

/-- **The top layer** (`lay = 0`): `layerHead` from `LayerIn` to `LeafOut`. -/
theorem layer_good_top (w : WBytes) (pk : Digest) (index : Nat) (M : Digest)
    (s : MachineState) (hs : LayerIn w pk index 0 M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index 0 ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel 0) (C + layerCost 0 0) Q (A + layerCost 0 0) (ccM (layerHead w index 0 M R) K) := by
  have hidx := hs.idx
  have hA := encA_step w pk index 0 M s hs
  have hfuel : layerFuel 0 = 15 + 1 + 51 + 2321 + 13 := by decide
  have hcost : layerCost 0 0 = 15 + 8 + 57 + 13 + 1180 := by decide
  have hsA : stepsA (0 : Layer).val = 15 := rfl
  unfold layerHead
  by_cases hctr : (wctr w 0).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    rw [hsA] at hst
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    rw [hsA] at hst
    have hblk := blocks_encodingInput 0 (route index 0).2 (route index 0).1 M (wctr w 0)
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + 13 + 2321 + 51) (C + 13 + 1180 + 57) Q (A + 13 + 1180 + 57)
        (ccM (match decode 0 (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) K) := by
      intro a
      have hB := encBt_step w pk index c hc hidx t hpre a
      cases hds : decode 0 (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure, hK0]
        obtain ⟨v, k, cy, hst', hf', h5', h10', hk, hcy⟩ := hB.1 hds
        exact GoodQ.steps' hst' (GoodQ.reject (Q := Q) (A := 0) hf' h5' h10') (by omega) (by omega)
          (fun hq => ⟨hq, by omega⟩)
      | some ds =>
        dsimp only
        obtain ⟨s0, hst0, hQok, hfit, hkn, hO0, hlO0, hIn, hG0, hOr0, h23, h30, hkB⟩ := hB.2 (by rw [hds]; simp)
        set Qc := qctxOf w index a (trPc 0 c) with hQd
        obtain ⟨rfl, hsum⟩ := decode_top_sum _ ds hds
        have hacc := Qc.topCost_accept hfit hsum
        have hsave := Qc.topZ_ge_five hfit hsum
        have hP := Qc.topP_eq hfit
        have hG := Qc.top_good hQok hkn hO0 hlO0 (fun ends => ccM (R ends) K) (N + 13) (C + 13) (A + 13) Q
          (fun ends t ht => by
            obtain ⟨u, hstu, hu⟩ := leafT_step w pk index c hc hidx a s0 hkn hkB hG0 hOr0 h23 h30 ends t ht
            exact GoodQ.steps' hstu (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩))
          s0 hIn
        have e : chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 (a.extractLsb' 0 128)) = Qc.topP := by
          rw [hP]; unfold chainsP; rw [chainCount_top]; rfl
        rw [ccM_bind, e]
        exact GoodQ.steps' hst0 hG (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have := GoodQ.shortHash_bind (f := fun answer => match decode 0 answer with
      | none => pure none
      | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)

/-- **One layer** (`layer_good`): `layerHead` from `LayerIn` to `LeafOut`, fuel `layerFuel lay`, at most
`layerCost lay 0` cycles on every path. -/
theorem layer_good (w : WBytes) (pk : Digest) (index : Nat) (lay : Layer) (M : Digest)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCost lay.val 0)
      (ccM (layerHead w index lay M R) K) := by
  by_cases h0 : lay = 0
  · subst h0
    exact layer_good_top w pk index M s hs R K hK0 N C A Q hR
  · exact layer_good_low w pk index lay h0 M s hs R K hK0 N C A Q hR

/-- **W's layer loop, one layer** (`layersP w index (n + 1) M`, layer `n < 4`): the form V3 composes, with the
continuation from `LeafOut` = the leaf pk, `merkleP` and the layers below. -/
theorem layersP_good (w : WBytes) (pk : Digest) (index n : Nat) (hn : n < 4) (M : Digest) (s : MachineState)
    (hs : LayerIn w pk index n M s) (K : Option Digest → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0))
    (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index (Fin.ofNat 4 n) ends u →
      GoodQ u N C Q A (ccM (leafHash (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
        ends >>= merkleP w index (Fin.ofNat 4 n) >>= layersP w index n) K)) :
    GoodQ s (N + layerFuel n) (C + layerCost n 0) Q (A + layerCost n 0) (ccM (layersP w index (n + 1) M) K) := by
  have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn]
  rw [layersP_succ]
  have := layer_good w pk index (Fin.ofNat 4 n) M s (by rw [hv]; exact hs) _ K hK0 N C A Q hR
  rwa [hv] at this

/-! ## Interfaces: V2's `FtsOut` → layer 3's `LayerIn`; V3's Merkle end → the next `LayerIn` -/

/-- **V2's `FtsOut` is layer 3's `LayerIn`** (stated on `FtsOut`'s fields `glob`, `idx`, `pc` (`layerPc = 656 =
xtr3_1`), `root`, `wit`, with `F.idx = a.toNat % 2^31 < 2^31`). -/
theorem layerIn_of_fts (w : WBytes) (pk : Digest) (idx : Nat) (root : Digest) (u : MachineState)
    (hidx : idx < 2 ^ 31) (hglob : Glob baseK w pk u) (hreg : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hpc : u.pc = pcOf 656) (hroot : DigAt u 0x100 root)
    (hwit : Verify.Orig w (fun o => o < 64 ∨ 11288 ≤ o) u) (hcarry1 : u.getReg .x6 = 1) :
    LayerIn w pk idx 3 root u where
  lay4 := by norm_num
  idx := hidx
  copy := ⟨0, by rw [nCopy_eq.1]; norm_num, by rw [hpc]; rfl⟩
  glob := by
    refine ⟨fun p hp => ?_, hglob.2⟩
    simp only [preK, ↓reduceIte, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hglob.1 p hp
    · exact hcarry1
  route := by rw [show rReg 3 = .x22 from rfl, hreg, show below 3 = 0 from rfl, pow_zero, Nat.div_one]
  msg := hroot
  orig := hwit.mono (fun o ho => Or.inr ho.1)

/-- The tree index of layer `L > 0` is the next layer's remaining index (`t5` at the next transition). -/
theorem tree_next (index : Nat) (L : Layer) (h : L ≠ 0) : (route index L).2 = index / 2 ^ below (L.val - 1) := by
  rw [route_snd]
  fin_cases L
  · exact absurd rfl h
  all_goals rfl

/-- The next layer's region ends where layer `L`'s Merkle blocks begin. -/
theorem layerEnd_prev (L : Layer) (h : L ≠ 0) : layerEnd (L.val - 1) = layerBase L := by
  fin_cases L
  · exact absurd rfl h
  all_goals decide

end SigGolfCandidate.T3M
