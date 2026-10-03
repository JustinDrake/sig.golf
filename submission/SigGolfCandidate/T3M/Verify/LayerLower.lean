import SigGolfCandidate.T3M.Verify.LeafSem

/-! Shared layer interfaces and costs, together with correctness of the unchanged lower layers.
The mixed-radix top transition and chain composition are assembled in `LayerGood`. -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 width maxDigit shortHash leafHash)

/-! ## The layer as a program -/

/-- Core's chains of layer `lay` with the witness pads and values (`layerP`'s `mapM`). -/
def chainsP (w : WBytes) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : T3.M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
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

/-- Steps / cycles of decode and entry dispatch (lower31 /34, top118-step conservative fuel /72 cycles). -/
def stB (lay : Nat) : Nat := if lay = 0 then 118 else 31
def cyB (lay : Nat) : Nat := if lay = 0 then 72 else 34
/-- The chain phase's accepting cycles without maximal digits: lower `3008 − 9 target`, top `1183` after the mandatory eleven-cycle terminal-store credit. -/
def chainCost0 (lay : Nat) : Nat := if lay = 0 then 1183 else 3008 - 9 * tgtL lay
/-- The chain phase's steps on every path. -/
def chainFuel (lay : Nat) : Nat := if lay = 0 then 2321 else 1720

/-- **The cycles of one layer from `LayerIn` to `LeafOut`** with the max-digit savings `Z`: A (`stepsA`), the
encoding HASH (8), B, the leaf-pk block, the chains `chainCost0 lay − Z`. -/
def layerCost (lay Z : Nat) : Nat := stepsA lay + 8 + cyB lay + lfSteps lay + chainCost0 lay - Z

/-- The steps of one layer on every path. -/
def layerFuel (lay : Nat) : Nat := stepsA lay + 1 + stB lay + chainFuel lay + lfSteps lay

theorem layerCost_vals :
    layerCost 3 0 = 1335 ∧ layerCost 2 0 = 1322 ∧ layerCost 1 0 = 1322 ∧ layerCost 0 0 = 1292 := by decide

theorem layerFuel_vals :
    layerFuel 3 = 1783 ∧ layerFuel 2 = 1779 ∧ layerFuel 1 = 1779 ∧ layerFuel 0 = 2469 := by decide

/-! ## Decode facts -/

theorem ckOf_lt (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (ds : List Nat)
    (hds : decode lay (a.extractLsb' 0 128) = some ds) : ckOf lay a < 8 := by
  rw [decode_lower lay hlay] at hds
  split_ifs at hds with h1 h2
  unfold ckOf; rw [tgtL_eq]; exact h2

theorem decode_top_sum (value : Digest) (ds : List Nat) (h : decode 0 value = some ds) :
    ds = dataDigits 0 value ∧ (dataDigits 0 value).sum = 126 := by
  rw [Search.decode_top] at h
  split_ifs at h with hp
  · exact ⟨(Option.some.inj h).symm, hp.2.2⟩

theorem s6v_chainBlock (lay : Layer) (h : lay ≠ 0) : s6v lay.val = 0x800 + chainBlock lay 42 + 1024 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide

theorem chainCount_top : chainCount (0 : Layer) = 54 := by decide

/-! ## The exact accepting cost -/

/-- **The accepting cost of a lower layer is `layerCost lay Z`**: on an accepted encoding (`decode = some ds`) the
run from `LayerIn` to `LeafOut` — A (`stepsA`), the encoding HASH (8), B (34), the chain phase (`lowCost`), the
leaf-pk block (12) — costs `layerCost lay Z` cycles with `Z = zSum 0 43` (the max-digit savings). -/
theorem layerCost_low (w : WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (p : Nat)
    (ds : List Nat) (hds : decode lay (a.extractLsb' 0 128) = some ds) :
    stepsA lay.val + 8 + 34 + (lctxOf w index lay a p).lowCost + 12 =
      layerCost lay.val ((lctxOf w index lay a p).zSum 0 43) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hD := lctx_digits w index lay a p hlay ds hds
  have hsum := LCtx.decode_lower_sum lay hlay _ ds hds
  have hck : (lctxOf w index lay a p).ck < 8 := ckOf_lt lay hlay a ds hds
  have hacc := (lctxOf w index lay a p).lowCost_accept hck ds hD hsum.1 (target lay) hsum.2
  rw [← tgtL_eq] at hacc
  simp only [layerCost, cyB, lfSteps, chainCost0, if_neg h0]
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
  have hT : 9 * tgtL lay.val ≤ 3008 := by fin_cases lay <;> decide
  have hfuel : layerFuel lay.val = stepsA lay.val + 1 + 31 + 1720 + 12 := by simp [layerFuel, stB, chainFuel, lfSteps, h0]
  have hcost : layerCost lay.val 0 = stepsA lay.val + 8 + 34 + 12 + (3008 - 9 * tgtL lay.val) := by
    simp only [layerCost, cyB, lfSteps, chainCost0, if_neg h0]; omega
  unfold layerHead
  by_cases hctr : (wctr w lay).toNat ≥ counterLimit
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    exact GoodQ.steps' hst (GoodQ.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, c, hc, hpre⟩ := hA.2 (by omega)
    have hblk := blocks_encodingInput lay (route index lay).2 (route index lay).1 M (wctr w lay)
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + 12 + 1720 + 31) (C + 12 + (3008 - 9 * tgtL lay.val) + 34)
        Q (A + 12 + (3008 - 9 * tgtL lay.val) + 34)
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
        have hG := L.lower_good hLok rfl rfl hck hkn hO0 (fun ends => ccM (R ends) K) (N + 12) (C + 12) (A + 12) Q
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

/-! ## Interfaces: V2's `FtsOut` → layer 3's `LayerIn`; V3's Merkle end → the next `LayerIn` -/

/-- **V2's `FtsOut` reaches layer 3's `LayerIn`** (stated on `FtsOut`'s fields `glob`, `idx`, `pc` (`layerPc = 656`),
`root`, `wit`, with `F.idx = a.toNat % 2^31 < 2^31`): the load block (words 656 .. 660, `ld3Spec`, 5 cycles) reads
five layer constants from the embedded data (`DataOK`, part of `Glob`); the copy `xtr3_1` starts at 661. The four carried constants remain known. -/
theorem layerIn_of_fts (w : WBytes) (pk : Digest) (idx : Nat) (root : Digest) (u : MachineState)
    (hidx : idx < 2 ^ 31) (hglob : Glob carryK w pk u) (hreg : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hpc : u.pc = pcOf 656) (hroot : DigAt u 0x100 root)
    (hwit : Verify.Orig w (fun o => o < 64 ∨ 11288 ≤ o) u) :
    ∃ t, Steps image u 5 5 t ∧ LayerIn w pk idx 3 root t := by
  obtain ⟨t, ht⟩ := spec_run ld3Check_ok u hpc hglob.1 (by simp [ld3Spec]) (by simp)
  have hm : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have hD : DataOK u := hglob.2.2.2.2.2
  have r28 : t.getReg .x28 = (E.ld (kw DATA)).eval u := ht.regs (.x28, .ld (kw DATA)) (by simp [ld3Spec])
  have r21 : t.getReg .x21 = (E.ld (kw (DATA + 8))).eval u := ht.regs (.x21, .ld (kw (DATA + 8))) (by simp [ld3Spec])
  have r20 : t.getReg .x20 = (E.ld (kw (DATA + 16))).eval u :=
    ht.regs (.x20, .ld (kw (DATA + 16))) (by simp [ld3Spec])
  have r27 : t.getReg .x27 = (E.ld (kw (DATA + 24))).eval u :=
    ht.regs (.x27, .ld (kw (DATA + 24))) (by simp [ld3Spec])
  have r2 : t.getReg .x2 = (E.ld (kw (DATA + 32))).eval u := ht.regs (.x2, .ld (kw (DATA + 32))) (by simp [ld3Spec])
  have e28 : t.getReg .x28 = BitVec.ofNat 64 (2 ^ 40) :=
    r28.trans (hD.word 0 (by omega) (2 ^ 40) (by decide) DATA (by omega))
  have e21 : t.getReg .x21 = BitVec.ofNat 64 M2c :=
    r21.trans (hD.word 1 (by omega) M2c (by decide) (DATA + 8) (by omega))
  have e20 : t.getReg .x20 = BitVec.ofNat 64 M1c :=
    r20.trans (hD.word 2 (by omega) M1c (by decide) (DATA + 16) (by omega))
  have e27 : t.getReg .x27 = BitVec.ofNat 64 (hw 1 3) :=
    r27.trans (hD.word 3 (by omega) (hw 1 3) (by decide) (DATA + 24) (by omega))
  have e2 : t.getReg .x2 = BitVec.ofNat 64 0x3fe00 :=
    r2.trans (hD.word 4 (by omega) 0x3fe00 (by decide) (DATA + 32) (by omega))
  have hG0 : Glob afterLoadK w pk t := ht.glob _ _ _ hglob (RelOK.nil u)
  have hpk : preK 3 = afterLoadK ++ [(.x28, BitVec.ofNat 64 (2 ^ 40)), (.x21, BitVec.ofNat 64 M2c),
      (.x20, BitVec.ofNat 64 M1c), (.x27, BitVec.ofNat 64 (hw 1 3)), (.x2, BitVec.ofNat 64 0x3fe00)] := rfl
  have hk : ∀ p ∈ preK 3, t.getReg p.1 = p.2 := by
    intro p hp
    rw [hpk] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl | rfl
    · exact ht.known p hp
    · exact e28
    · exact e21
    · exact e20
    · exact e27
    · exact e2
  refine ⟨t, ht.steps, ⟨by norm_num, hidx, ⟨0, by rw [nCopy_eq.1]; norm_num, by rw [ht.pc rfl]; rfl⟩, ⟨hk, hG0.2⟩,
    ?_, ?_, ?_⟩⟩
  · rw [show rReg 3 = .x22 from rfl, ht.keep .x22 (by simp), hreg, show below 3 = 0 from rfl, pow_zero, Nat.div_one]
  · exact ⟨(hm _).trans hroot.1, (hm _).trans hroot.2⟩
  · exact (hwit.mono (fun o ho => Or.inr ho.1)).frame (fun j _ _ => hm _)

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
