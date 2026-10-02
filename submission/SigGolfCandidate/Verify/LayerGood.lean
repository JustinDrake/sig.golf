import SigGolfCandidate.Verify.LeafSem
import SigGolfCandidate.Verify.ChainGood
import SigGolfCandidate.Verify.ChainCheckAll

/-! # Hypertree layers (W1a): the simulation judgment for one layer, all layers, and the comparison -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def layerSpec (w : List Byte) (idx lay : Nat) (M : Val) : OracleComp HashSpec (Option Val) := do
  let (e, tau) := route idx lay
  let d ← encodingHash (encInput lay tau e M (witCounter w lay))
  match decodeDigits lay d with
  | none => pure none
  | some x => do
    let leaf ← verifyLeafP w lay tau e x
    let node ← foldPath (nodeInput lay tau) e leaf
      (if lay = 0 then witPath w lay else (witPath w lay).take (height lay - 1))
    pure (some node)

/-- The message entering `verifyLayers w idx n`, given the 16-byte value `X` the machine holds there: the
final root itself (`n = 0`), `P ++` the PORS root (`n = 5`), else the two children of the root of the
tree of layer `n`, `X` the one on the path. -/
def msgAt (w : List Byte) (idx n : Nat) (X : Val) : Val :=
  if n = 0 then X else if n = 5 then P ++ X
  else topPair (route idx n).1 (height n) X (witSib w n (height n - 1))

theorem verifyLayers_succ (w : List Byte) (idx lay : Nat) (hlay : lay < 5) (M : Val) :
    verifyLayers w idx (lay + 1) M = layerSpec w idx lay M >>= fun o => match o with
      | none => pure none
      | some v => verifyLayers w idx lay (msgAt w idx lay v) := by
  rcases hr : route idx lay with ⟨e, tau⟩
  have he : (route idx lay).1 = e := by rw [hr]
  simp only [verifyLayers, layerSpec, hr, bind_assoc]
  congr 1; funext d
  cases h : decodeDigits lay d with
  | none => simp
  | some x =>
    simp only [bind_assoc, pure_bind]
    congr 1; funext leaf
    by_cases h0 : lay = 0
    · subst h0; simp [msgAt]
    · simp [h0, msgAt, show lay ≠ 5 by omega, he]

def FoldEndL (L : LCtx) (u : MachineState) : Prop :=
  ∃ s0, FoldEnd (layFC L) s0 u ∧ LeafCarry L s0

/-- Cycles of layer `lay` (an upper bound: each digit-7 chain saves one more cycle): the sibling copy
(below layer 4) and the transition up to the encoding hash, the hash, the check and chain prologue
(`remu` 4 cycles), the 42 chains (`chainsBound lay`, the digit sum being `targetFor lay`), the leaf tweak
and dispatch, the leaf hash (11 blocks), the fold (to the root in layer 0, else to the node under it). -/
def layerCost (lay : Nat) : Nat :=
  stepsA lay + 8 + cyclesB lay + chainsBound lay + (leafSteps lay + 1) + 88 +
    foldCost lay 0 (if lay = 0 then heightL lay else heightL lay - 1)

theorem blocks_q (n : Nat) (ws : List Word) : (queryOfWords n ws).blocks = n + 1 := rfl

theorem pathOff_eqL (lay : Nat) (h : lay < 5) : pathOff lay = pathOffL lay := by
  interval_cases lay <;> decide

theorem witPath_eq (L : LCtx) (hL : L.lay < 5) : witPath L.wl L.lay = (layFC L).path := by
  unfold witPath FCtx.path layFC
  simp only [heightL_eq _ hL]
  apply List.map_congr_left
  intro l _
  simp [witSib, pathOff_eqL _ hL, pathStrideL, pathStride]

theorem Good.reject {s : MachineState} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : Good s 1 1 (pure (false, 0)) := by
  have := Good.halt hf h5
  rw [h10] at this
  exact this

theorem foldlM_congr_mem {m : Type → Type} [Monad m] {α β : Type} (f g : β → α → m β) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ b, f b a = g b a) → l.foldlM f b = l.foldlM g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    simp only [List.foldlM_cons]
    rw [h a (List.mem_cons_self ..)]
    congr 1; funext b'
    exact foldlM_congr_mem f g l b' (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- The fold over the first `k` levels of the path. -/
theorem foldPath_take (fc : FCtx) (v : Val) (k : Nat) (hk : k ≤ fc.h) :
    foldPath fc.node fc.E v (fc.path.take k) = (List.range' 0 k).foldlM fc.stepFn v := by
  unfold foldPath
  rw [show (fc.path.take k).length = k by simp [FCtx.path]; omega, List.range_eq_range']
  apply foldlM_congr_mem
  intro lam hlam b
  have hl : lam < k := by simpa using hlam
  have e : (fc.path.take k).getD lam [] = fc.path.getD lam [] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, hl]
  simp only [FCtx.stepFn, e]

theorem msg_eq (L : LCtx) (hL : L.ok) (X : Val) : L.msg X = msgAt L.wl L.idx (L.lay + 1) X := by
  have hlay := hL.1
  unfold LCtx.msg msgAt
  rw [if_neg (show ¬ (L.lay + 1 = 0) by omega)]
  by_cases h4 : L.lay = 4
  · rw [if_pos h4, if_pos (show L.lay + 1 = 5 by omega)]
  · rw [if_neg h4, if_neg (show ¬ (L.lay + 1 = 5) by omega), route_eq L.idx (L.lay + 1) (by omega),
      ← heightL_eq (L.lay + 1) (by omega)]
    rfl

/-! ## Layer transitions -/

/-- Below the top layer the fold stops under the root: its last state is the start of the next layer,
with the node under the root in EB+32 and the top sibling of the path still in its fresh slot. -/
theorem foldInv_layerIn (wl pk : List Byte) (lay idx : Nat) (h1 : 1 ≤ lay) (h7 : lay < 5)
    (hidx : idx < 2 ^ 34) (hwl : wl.length = 16384)
    (s0 : MachineState) (v : Val) (u : MachineState)
    (hu : FoldInv (layFC ⟨wl, pk, lay, idx⟩) s0 (heightL lay - 1) v u)
    (hc : LeafCarry ⟨wl, pk, lay, idx⟩ s0) :
    LayerIn ⟨wl, pk, lay - 1, idx⟩ v u := by
  have hfc := layFC_ok ⟨wl, pk, lay, idx⟩ ⟨h7, hidx, hwl⟩
  have hh := heightL_le lay h7
  obtain ⟨hG, hK, -, hNB, -, hm0, hm8, hvl, hF, hpc, hFresh, h12, _⟩ := hu
  obtain ⟨h30, hCB, -, -, hEH⟩ := hc
  have hsw := sib_words (layFC ⟨wl, pk, lay, idx⟩) hfc (heightL lay - 1)
    (by show heightL lay - 1 < heightL lay; omega) u hG hFresh
  have hsl := length_sib (layFC ⟨wl, pk, lay, idx⟩) hfc (heightL lay - 1)
    (by show heightL lay - 1 < heightL lay; omega)
  have hvA : (layFC ⟨wl, pk, lay, idx⟩).vA (heightL lay - 1) =
      encD (lay - 1) (LCtx.sub ⟨wl, pk, lay - 1, idx⟩).e := by
    unfold FCtx.vA nodeDst
    rw [if_pos ⟨by simp only [layFC]; omega, by simp only [layFC]; omega⟩]
    simp only [layFC, LCtx.lay, LCtx.sub, LCtx.e, encD, xLeft, Nat.sub_add_cancel h1,
      show (lay - 1 != 4) = true by simp; omega, Bool.true_and]
    have hb := bitOf_lt (idx / 2 ^ layS lay % 2 ^ heightL lay) (heightL lay - 1)
    unfold bitOf at hb ⊢
    split <;> rename_i h <;> simp_all <;> omega
  rw [hvA] at hm0 hm8 h12
  have hK1 : KnownOK (foldK lay 64) u := by
    have e : lvlK lay (heightL lay - 1) = foldK lay 64 := by
      unfold lvlK; rw [if_neg (by omega)]
    rw [← e]; exact hK
  have kf : ∀ r ∈ fkeep false, u.getReg r = s0.getReg r := hF.1
  refine ⟨hG, ?_, ?_, hm0, hm8, hvl, fun _ => trivial, ?_, ?_, ?_,
    fun h => absurd h (show ¬ (lay - 1 = 4) by omega), fun _ => ?_, ?_⟩
  · simp only [LCtx.lay, preK, if_neg (show lay - 1 ≠ 4 by omega), aK, Nat.sub_add_cancel h1]
    intro p hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp | hp | hp | hp
    · exact hK1 p (by simp [foldK, fk, gkOf, hp])
    · subst hp; exact hK1 _ (by simp [foldK, fk, gkOf])
    · subst hp; exact hK1 _ (by simp [foldK, fk, gkOf])
    · subst hp; exact h12
    · subst hp; exact hK1 (.x22, BitVec.ofNat 64 (s6N lay)) (by simp [foldK, s6N_eq])
  · simp only [routeReg, routeIn, if_neg (show lay - 1 ≠ 4 by omega)]
    rw [kf _ (by simp [fkeep]), h30]
    simp only [LCtx.tau, LCtx.lay, if_neg (show lay ≠ 0 by omega)]
    rw [layS_succ (lay - 1) (by omega), Nat.sub_add_cancel h1]
  · intro _
    have hn := hNB.2 (by omega : heightL lay - 1 ≠ 0)
    rw [hn]
    congr 1
    simp only [FCtx.lo0, layFC, LCtx.tau]
    have ht := tau_lt lay idx h7 hidx
    rw [Nat.div_eq_of_lt (by omega : idx / 2 ^ (layS lay + heightL lay) < 2 ^ 32)]
    rw [Nat.sub_add_cancel h1]
    convert Ref.MaskHeader.header_node lay h7 using 2 <;> omega
  · intro _
    change EncHeader (lay - 1 + 1) u
    rw [Nat.sub_add_cancel h1]
    exact hEH.frame (hF.2 0x100 (by decide) (Or.inl (by decide)))
  · exact Fresh_sub hFresh (fun a b k hw => FreshW_layer h1 hw)
  · show u.getMem (BitVec.ofNat 64 (topSib (lay - 1))) =
        vw0 (witSib wl (lay - 1 + 1) (heightL (lay - 1 + 1) - 1)) ∧
      u.getMem (BitVec.ofNat 64 (topSib (lay - 1) + 8)) =
        vw1 (witSib wl (lay - 1 + 1) (heightL (lay - 1 + 1) - 1)) ∧
      (witSib wl (lay - 1 + 1) (heightL (lay - 1 + 1) - 1)).length = 16
    have e1 : topSib (lay - 1) = sibAddr lay (heightL lay - 1) := by
      unfold topSib; rw [Nat.sub_add_cancel h1]
    have e2 : witSib wl (lay - 1 + 1) (heightL (lay - 1 + 1) - 1) =
        (layFC ⟨wl, pk, lay, idx⟩).sib (heightL lay - 1) := by
      rw [Nat.sub_add_cancel h1]
      simp [witSib, FCtx.sib, layFC, pathOff_eqL _ h7, pathStrideL, pathStride, show lay ≠ 0 by omega]
    rw [e1, e2]
    exact ⟨hsw.1, hsw.2, hsl⟩
  · refine ⟨(layFC ⟨wl, pk, lay, idx⟩).blk (nCh lay - 1), ?_, ?_, fun _ => ?_⟩
    · simp only [nCopy, if_neg (show lay - 1 ≠ 4 by omega), Nat.sub_add_cancel h1]
      exact blk_lt _ _
    · rw [hpc]
      simp only [preStart, if_neg (show lay - 1 ≠ 4 by omega), Nat.sub_add_cancel h1, FCtx.X, FCtx.ci,
        FCtx.kk, layFC]
      have e : chOf lay (heightL lay - 1) = nCh lay - 1 ∧
          heightL lay - 1 - chB0 lay (nCh lay - 1) = chBits lay (nCh lay - 1) - 1 := by
        interval_cases lay <;> decide
      rw [e.1, e.2]
      all_goals rfl
    · have e1 : chB0 lay (nCh lay - 1) = 0 := by unfold chB0; rw [if_neg (by omega)]
      have e2 : chBits lay (nCh lay - 1) = heightL lay := by unfold chBits; rw [if_neg (by omega)]
      simp only [FCtx.blk, layFC, LCtx.sub, LCtx.e, Nat.sub_add_cancel h1]
      rw [e1, e2, Nat.pow_zero, Nat.div_one, Nat.mod_mod]

theorem layer_good (L : LCtx) (hL : L.ok) (X : Val) (Kopt : Option Val → OracleComp HashSpec Obs)
    (hnone : Kopt none = pure (false, 0)) (N C : Nat)
    (hK0 : L.lay = 0 → ∀ a u, FoldEndL L u →
      Good (writeHash u a) N C (Kopt (some (answerBytes 16 a))))
    (hK1 : L.lay ≠ 0 → ∀ v u, LayerIn ⟨L.wl, L.pk, L.lay - 1, L.idx⟩ v u → Good u N C (Kopt (some v)))
    (s : MachineState) (hs : LayerIn L X s) :
    Good s (N + 5000) (C + layerCost L.lay) (cc (layerSpec L.wl L.idx L.lay (L.msg X)) Kopt) := by
  have hmsglen : (L.msg X).length = 32 := by
    rcases hs with ⟨_, _, _, _, _, hx, _, _, _, _, _, hsib, _⟩
    unfold LCtx.msg
    split_ifs with h4
    · simp [P, hx]
    · have hv := (hsib h4).2.2
      unfold topPair
      split <;> simp [hx, hv]
  have hL' := hL
  obtain ⟨hlay, hidx, hwl⟩ := hL'
  obtain ⟨t, ht, t1, hst1, hf1, h51, hv1, hin1, hblk1, hpost1⟩ := enc_step L hL X s hs
  unfold layerSpec
  rw [route_eq L.idx L.lay hlay]
  simp only []
  rw [cc_bind]
  have hfc := layFC_ok L hL
  have htarget := targetFor_le L.lay
  have hhL := heightL_le L.lay hlay
  have hcb : chainsBound L.lay ≥ 1200 := by unfold chainsBound; omega
  have hsA : stepsA L.lay ≤ 16 := by unfold stepsA stepsT; split_ifs <;> omega
  have hcB : cyclesB L.lay ≤ 32 := by unfold cyclesB stepsB; omega
  have hsB : stepsB L.lay ≤ 29 := by unfold stepsB; omega
  have H : ∀ a, Good (writeHash t1 a) (N + 4900) (C + layerCost L.lay - stepsA L.lay - 8)
      (cc (match decodeDigits L.lay (encodingBytes a) with
        | none => pure none
        | some x => do
          let leaf ← verifyLeafP L.wl L.lay L.tau L.e x
          let node ← foldPath (nodeInput L.lay L.tau) L.e leaf
            (if L.lay = 0 then witPath L.wl L.lay else (witPath L.wl L.lay).take (height L.lay - 1))
          pure (some node)) Kopt) := by
    intro a
    obtain ⟨hrej, hacc⟩ := encpost_step L hL t ht a _ (hpost1 a)
    cases hd : decodeDigits L.lay (encodingBytes a) with
    | none =>
      obtain ⟨k, hk, c, hc, u, hst, hf, h5, h10⟩ := hrej hd
      simp only [cc_pure, hnone]
      exact Good.steps' hst (Good.reject hf h5 h10) (by omega) (by unfold layerCost; omega)
    | some xs =>
      obtain ⟨t2, hst2, hent, hcok, hxs, hsum, hlen⟩ := hacc xs hd
      have hsBp := stepsBPath_le (selOf a) L.lay
      have hcBp : cyclesBPath (selOf a) L.lay ≤ cyclesB L.lay := cyclesBPath_le _ _
      simp only [verifyLeafP, bind_assoc, cc_bind]
      have hcost : chainsCost (L.cctx t a) 0 42 ≤ chainsBound L.lay := chainsCost_le (L.cctx t a) xs hlen hxs hsum
      have hch := chains_good0 (L.cctx t a) hcok (pcOf_even _) xs hxs
        (fun ends => cc (hash16 (leafInput L.lay L.tau L.e ends)) (fun leaf =>
          cc (foldPath (nodeInput L.lay L.tau) L.e leaf
              (if L.lay = 0 then witPath L.wl L.lay else (witPath L.wl L.lay).take (height L.lay - 1)))
            (fun root => cc (pure (some root)) Kopt)))
        (N + 2000) (C + 88 + (leafSteps L.lay + 1) +
          foldCost L.lay 0 (if L.lay = 0 then heightL L.lay else heightL L.lay - 1))
        (by
          intro ends u hH42
          obtain ⟨t3, hst3, hf3, h53, hv3, hin3, hpost3⟩ := leaf_step L hL t ht a ends u hH42
          obtain ⟨⟨-, -, -, -, -, -, hends, hvs, -⟩, -, -⟩ := chainNext_42 hH42
          have H3 : ∀ ans, Good (writeHash t3 ans) (N + 1900)
              (C + foldCost L.lay 0 (if L.lay = 0 then heightL L.lay else heightL L.lay - 1))
              (cc (foldPath (nodeInput L.lay L.tau) L.e (answerBytes 16 ans)
                  (if L.lay = 0 then witPath L.wl L.lay else (witPath L.wl L.lay).take (height L.lay - 1)))
                (fun root => cc (pure (some root)) Kopt)) := by
            intro ans
            obtain ⟨hfi, hcar⟩ := hpost3 ans
            have hnH : NodeH (layFC L) :=
              ⟨rfl, rfl, by have := tau_lt L.lay L.idx hL.1 hL.2.1; simpa [layFC, LCtx.tau] using (show L.tau < 2 ^ 32 by exact lt_of_lt_of_le this (by decide))⟩
            simp only [cc_pure]
            by_cases h0 : L.lay = 0
            · rw [if_pos h0, if_pos h0, nodeInput_eq, witPath_eq L hlay,
                show nodeF 3 L.lay L.tau = (layFC L).node from rfl, show L.e = (layFC L).E from rfl,
                foldPath_eq]
              have hfold := fold_good (layFC L) hfc hnH h0 (layFC_check L hL) _
                (fun root => Kopt (some root))
                N C (fun a u hend => hK0 h0 a u ⟨_, hend, hcar⟩) (heightL L.lay) 0 (by simp [layFC])
                (by omega) _ _ hfi
              exact hfold.mono (by omega) (by simp [layFC])
            · rw [if_neg h0, if_neg h0, ← heightL_eq L.lay hlay, nodeInput_eq, witPath_eq L hlay,
                show nodeF 3 L.lay L.tau = (layFC L).node from rfl, show L.e = (layFC L).E from rfl,
                foldPath_take (layFC L) _ (heightL L.lay - 1) (by simp [layFC])]
              have hfold := fold_steps (layFC L) hfc hnH (layFC_check L hL) _
                (fun node => Kopt (some node))
                N C (heightL L.lay - 1) (by show heightL L.lay - 1 < heightL L.lay; omega)
                (fun v u hinv => hK1 h0 v u
                  (foldInv_layerIn L.wl L.pk L.lay L.idx (by omega) hlay hidx hwl _ v u hinv hcar))
                (heightL L.lay - 1) 0 (by omega) _ _ hfi
              exact hfold.mono (by omega) (by simp [layFC])
          have h3 := Good.hash (x := leafInput L.lay L.tau L.e ends) (K := fun leaf => cc (foldPath (nodeInput L.lay L.tau) L.e leaf
            (if L.lay = 0 then witPath L.wl L.lay else (witPath L.wl L.lay).take (height L.lay - 1)))
            (fun root => cc (pure (some root)) Kopt))
            hf3 h53 hv3 hin3 H3
          rw [addrFmt_leafInput_words _ _ _ _ hends hvs, blocks_q] at h3
          have hls : leafSteps L.lay ≤ 13 := by unfold leafSteps; split_ifs <;> omega
          exact Good.steps' hst3 h3 (by omega) (by omega))
        t2 hent
      have e1 : List.range nChains = List.range 42 := rfl
      rw [e1]
      refine Good.steps' hst2 (hch.congr ?_) (by omega) (by unfold layerCost; omega)
      rfl
  have h3 := Good.encodingHashF (x := encInput L.lay L.tau L.e (L.msg X) (witCounter L.wl L.lay)) (K := fun d => cc (match decodeDigits L.lay d with
        | none => pure none
        | some x => do
          let leaf ← verifyLeafP L.wl L.lay L.tau L.e x
          let node ← foldPath (nodeInput L.lay L.tau) L.e leaf
            (if L.lay = 0 then witPath L.wl L.lay else (witPath L.wl L.lay).take (height L.lay - 1))
          pure (some node)) Kopt) hf1 h51 hv1 hin1 H
  rw [hblk1] at h3
  exact Good.steps' hst1 h3 (by omega) (by unfold layerCost; omega)

/-! ## The final comparison -/

theorem leNat_inj : ∀ (l1 l2 : List Byte), l1.length = l2.length → leNat l1 = leNat l2 → l1 = l2
  | [], [], _, _ => rfl
  | a :: l1, b :: l2, hl, h => by
    simp only [leNat] at h
    have ha := a.isLt; have hb := b.isLt
    have h1 : a.toNat = b.toNat := by omega
    have h2 : leNat l1 = leNat l2 := by omega
    rw [BitVec.eq_of_toNat_eq h1, leNat_inj l1 l2 (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem w64_inj (l1 l2 : List Byte) (h1 : l1.length = 8) (h2 : l2.length = 8) :
    w64 l1 = w64 l2 ↔ l1 = l2 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [w64_toNat _ (by omega), w64_toNat _ (by omega)] at this
    exact leNat_inj _ _ (by omega) this
  · intro h; rw [h]

theorem val_eq_iff (M P : Val) (hM : M.length = 16) (hP : P.length = 16) :
    M = P ↔ vw0 M = w64 (P.take 8) ∧ vw1 M = w64 (P.drop 8) := by
  unfold vw0 vw1
  rw [w64_inj _ _ (by simp; omega) (by simp; omega), w64_inj _ _ (by simp; omega) (by simp; omega)]
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← List.take_append_drop 8 M, ← List.take_append_drop 8 P, h1, h2]

def FinalIn (wl pk : List Byte) (idx : Nat) (M : Val) (s : MachineState) : Prop :=
  ∃ u a, FoldEndL ⟨wl, pk, 0, idx⟩ u ∧ s = writeHash u a ∧ M = answerBytes 16 a

theorem cmp_link : ∀ t, t < 32 → m4Pc 0 1 t 4 + 7 + 1 = cmpPc (31 - t) := by decide

theorem compare_good (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (M : Val)
    (s : MachineState) (hs : FinalIn wl pk idx M s) : Good s 8 8 (pure (M == pk, 0)) := by
  obtain ⟨u, a, ⟨s0, ⟨hG, hK, hF, hpc, -, -⟩, -⟩, rfl, rfl⟩ := hs
  let D := (layFC ⟨wl, pk, 0, idx⟩).dst
  have hD : D = 864 ∨ D = 880 := by
    dsimp [D, layFC, dstOf]
    omega
  have hDb : D + 32 < 2 ^ 64 := by omega
  have h12 : u.getReg .x12 = BitVec.ofNat 64 D :=
    hK (.x12, _) (List.mem_append_right _ (List.mem_singleton_self _))
  have hsafe : safeDest D = true := by rcases hD with h | h <;> rw [h] <;> decide
  have hob : ∀ reject, ∀ o ∈ cmpObl reject, o.holds (writeHash u a) := by
    intro reject o ho
    have hchoice : o = .valid ⟨some (.reg .x12), 8⟩ 8 ∨
        o = .valid ⟨some (.reg .x12), 0⟩ 8 := by
      cases reject <;> simp_all [cmpObl]
    rcases hchoice with rfl | rfl
    all_goals simp only [Oblig.holds, Addr.eval, Rv.E.eval, writeHash_getReg, h12]
    all_goals rcases hD with h | h <;> rw [h] <;> decide
  have hG' := Glob_writeHash hG a _ h12 hsafe
  set tt := (layFC ⟨wl, pk, 0, idx⟩).blk 1 with htt
  have htt2 : tt < 32 := blk_lt _ 1
  have hK' : KnownOK cmpK (writeHash u a) := fun p hp => by
    rw [writeHash_getReg]
    simp only [cmpK] at hp
    apply hK p
    exact List.mem_append_left _ (List.mem_append_left _ hp)
  have hpc' : (writeHash u a).pc = pcOf (cmpPc (31 - tt)) := by
    rw [writeHash_pc, hpc, pcOf_add4, ← cmp_link tt htt2]
    rfl
  have m0 : (writeHash u a).getMem (BitVec.ofNat 64 D) = vw0 (answerBytes 16 a) :=
    (writeHash_at0 _ a _ h12 (by omega)).trans (vw0_answer a).symm
  have m1 : (writeHash u a).getMem (BitVec.ofNat 64 (D + 8)) = vw1 (answerBytes 16 a) :=
    (writeHash_at8 _ a D h12 (by omega)).trans (vw1_answer a).symm
  have p0 : (writeHash u a).getMem (BitVec.ofNat 64 160) = w64 (pk.take 8) := hG'.2.2.1.1
  have p1 : (writeHash u a).getMem (BitVec.ofNat 64 168) = w64 (pk.drop 8) := hG'.2.2.1.2
  have heq := val_eq_iff (answerBytes 16 a) pk (by simp) hpk
  obtain ⟨r1, r2⟩ := lc_cmp (lay := 0) (by omega) (show 31 - tt < 32 by omega) rfl
  by_cases e0 : vw0 (answerBytes 16 a) = w64 (pk.take 8)
  · obtain ⟨v, hv⟩ := specO_run r1 _ hpc' hK' (hob false) (by
      intro b hb
      simp only [specAcc, List.mem_singleton] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, cmpRoot, Rv.E.eval, ldE, cw, writeHash_getReg, h12, m0, p0, e0, bne_self_eq_false])
    have hsub : ∀ x y : Word, x - y = 0 ↔ x = y := fun x y => by
      constructor
      · intro h; have := congrArg (· + y) h; simpa [BitVec.sub_add_cancel] using this
      · intro h; subst h; exact BitVec.sub_self x
    have hdiff : cmpDiff.eval (writeHash u a) = vw1 (answerBytes 16 a) - w64 (pk.drop 8) := by
      have hadd : BitVec.ofNat 64 D + BitVec.ofNat 64 8 = BitVec.ofNat 64 (D + 8) := by
        rcases hD with h | h <;> rw [h] <;> decide
      simp only [cmpDiff, Rv.E.eval, BinOp.eval, ldE, cw, writeHash_getReg, h12, hadd, m1, p1] <;> rfl
    have hret : decide (v.getReg .x10 = 0) = (answerBytes 16 a == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq]
      rw [hv.regs (.x10, cmpDiff) (by simp [specAcc]), hdiff, hsub, heq]
      simp only [e0, true_and]
    have := Good.steps hv.steps (Good.halt (hv.ecall rfl) (hv.regs (.x5, cw 1) (by simp [specAcc])))
    rw [hret] at this
    exact this.mono (by simp [specAcc]) (by simp [specAcc])
  · obtain ⟨v, hv⟩ := specO_run r2 _ hpc' hK' (hob true) (by
      intro b hb
      simp only [specCR1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, cmpRoot, Rv.E.eval, ldE, cw, writeHash_getReg, h12, m0, p0]; simpa using e0)
    have hb : (answerBytes 16 a == pk) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact e0 (heq.mp h).1
    have := Good.steps hv.steps (Good.reject (hv.ecall rfl) (hv.regs (.x5, cw 1) (by simp [specCR1, rejK]))
      (hv.regs (.x10, cw 1) (by simp [specCR1, rejK])))
    rw [hb]; exact this.mono (by simp [specCR1]) (by simp [specCR1])

/-! ## All layers -/

def Kfin (pk : List Byte) : Option Val → OracleComp HashSpec Obs
  | none => pure (false, 0)
  | some root => pure (root == pk, 0)

def InLayer (wl pk : List Byte) (idx : Nat) : Nat → Val → MachineState → Prop
  | 0 => FinalIn wl pk idx
  | n + 1 => LayerIn ⟨wl, pk, n, idx⟩

def layersCost : Nat → Nat
  | 0 => 8
  | n + 1 => layersCost n + layerCost n

theorem layers_good (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (hidx : idx < 2 ^ 34)
    (hwl : wl.length = 16384) :
    ∀ n, n ≤ 5 → ∀ X s, InLayer wl pk idx n X s →
      Good s (5000 * n + 9) (layersCost n) (cc (verifyLayers wl idx n (msgAt wl idx n X)) (Kfin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ M s hs
    rw [show msgAt wl idx 0 M = M from if_pos rfl]
    simp only [verifyLayers, cc_pure, Kfin, layersCost]
    exact (compare_good wl pk hpk idx M s hs).mono (by omega) (le_refl _)
  | succ n ih =>
    intro hn X s hs
    have hL : (⟨wl, pk, n, idx⟩ : LCtx).ok := ⟨show n < 5 by omega, hidx, hwl⟩
    have hm : msgAt wl idx (n + 1) X = (⟨wl, pk, n, idx⟩ : LCtx).msg X :=
      (msg_eq ⟨wl, pk, n, idx⟩ hL X).symm
    rw [hm, verifyLayers_succ wl idx n (by omega), cc_bind]
    have := layer_good ⟨wl, pk, n, idx⟩ hL X
      (fun o => cc (match o with
        | none => pure none
        | some r => verifyLayers wl idx n (msgAt wl idx n r)) (Kfin pk)) (by simp [Kfin])
      (5000 * n + 9) (layersCost n)
      (by
        intro h0 a u hu
        have h0' : n = 0 := h0
        subst h0'
        exact ih (by omega) _ _ ⟨u, a, hu, rfl, rfl⟩)
      (by
        intro h0 v u hu
        cases n with
        | zero => exact absurd rfl h0
        | succ m => exact ih (by omega) v u hu) s hs
    exact this.mono (by omega) (by dsimp only; simp only [layersCost]; omega)

/-- The cycles of the five layers and the comparison (`8`). Against the head without the pair
message: `-14` per lower layer (no root hash) and `+4` in each upper transition (the sibling copy). -/
theorem layersCost_5 : layersCost 5 = 7439 := by decide

end SigGolfCandidate.Verify
