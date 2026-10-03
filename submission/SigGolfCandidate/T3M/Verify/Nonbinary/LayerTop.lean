import SigGolfCandidate.T3M.Verify.Nonbinary.LayerProgram
import SigGolfCandidate.T3M.Verify.Nonbinary.LayerLeaf
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGlobal

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 shortHash leafHash)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem nctx_topP_eq (w : WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).topP = chainsP w 0 (route index 0).2 (route index 0).1 (dataDigits 0 v) := by
  unfold NCtx.topP NCtx.chainF
  rw [foldlM_app_mapM]
  simp only [List.nil_append, id_map']
  rw [← List.range_eq_range', ← finRange_mapM]
  exact nctx_mapM_eq w index v p

theorem nctx_initial (w : WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hvalid : T3.topRanksValid v = true) :
    (nctxOf w index v p).ChainIn s 0 [] s := by
  let c := nctxOf w index v p
  have hf : c.Fit v := fun i hi => rfl
  refine ⟨⟨fun r hr => rfl, Frame.refl s _, by simp⟩,rfl,?_⟩
  rw [he.pc]
  change pcOf (176744 + 256 * (v.toNat % 128)) = pcOf (c.startPc 0)
  rw [NCtx.startPc, if_pos (by decide), c.fit_rank hf hvalid 0 (by decide)]
  simp [Nonbinary.entW,Search.topRank]

theorem nctx_encoded (u s : MachineState) (v : Digest) (p : Nat) (he : TopEntry u v p s)
    (hv : v.toNat < 2 ^ 125) : NCtx.Encoded v s := by
  refine ⟨he.lo,?_,?_,he.mask,he.table⟩
  · rw [he.hi]
    exact Search.topWindow_cross v
  · rw [he.tail,Search.topWindow_tail v hv]

/-- The mixed-radix top layer, including all rejected encodings and the eleven-cycle mandatory credit. -/
theorem layer_good_top (w : WBytes) (pk : Digest) (index : Nat) (M : Digest)
    (s : MachineState) (hs : LayerIn w pk index 0 M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index 0 ends u → GoodQ u N C Q A (ccM (R ends) K)) :
    GoodQ s (N + layerFuel 0) (C + layerCost 0 0) Q (A + layerCost 0 0) (ccM (layerHead w index 0 M R) K) := by
  have hidx := hs.idx
  have hA := encA_step w pk index 0 M s hs
  have hfuel : layerFuel 0 = 11 + 1 + 117 + 2321 + 12 := by decide
  have hcost : layerCost 0 0 = 11 + 8 + 69 + 12 + 1129 := by decide
  have hsA : stepsA (0 : Layer).val = 11 := rfl
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
    have H : ∀ a : BitVec 256, GoodQ (writeHash t a) (N + 12 + 2321 + 117) (C + 12 + 1129 + 69) Q (A + 12 + 1129 + 69)
        (ccM (match decode 0 (a.extractLsb' 0 128) with
          | none => pure none
          | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) K) := by
      intro a
      cases hds : decode 0 (a.extractLsb' 0 128) with
      | none =>
        dsimp only
        rw [ccM_pure,hK0]
        obtain ⟨k,z,st,hk,hz,h5z,h10z⟩ := topTransition_reject w pk index c hc t hpre a hds
        exact GoodQ.steps' st (GoodQ.reject (Q := Q) (A := 0) hz h5z h10z) (by omega) (by omega)
          (fun hq => ⟨hq,by omega⟩)
      | some ds =>
        dsimp only
        have hcan : decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128)) := by
          rw [hds,(decode_top_sum _ _ hds).1]
          rfl
        obtain ⟨s0,st0,he⟩ := topTransition_ok w pk index c hc t hpre a hcan
        let L := nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)
        have hLok : L.ok := nctx_ok w index _ c hidx
        have hkn : KnownOK L.known s0 := nctx_known w pk index c t s0 a hpre he
        have h12 : t.getReg .x12 = 320#64 := hpre.glob.1 (_, _) (by simp [bK])
        have hDs0 : DataOK s0 := (Glob_writeHash hpre.glob a 320 h12 (by decide)).2.2.2.2.2.congr
          (fun A _ hA => he.frame.get (by omega) (by simp))
        have hO := nctx_orig w index (a.extractLsb' 0 128) (trPc 0 c) s0
          (topEntry_orig w pk index c t s0 a hpre he) hDs0
        have hfit : L.Fit (a.extractLsb' 0 128) := fun i hi => rfl
        have hdec := NCtx.decode_facts hds
        have hIn := nctx_initial w index _ (trPc 0 c) _ s0 he hdec.2.1
        have hEnc := nctx_encoded _ s0 _ (trPc 0 c) he hdec.1
        have hG := L.top_good hLok hkn hO hEnc hfit hds (fun ends => ccM (R ends) K)
          (N+12) (C+12) (A+12) Q (fun ends z hz => by
            obtain ⟨hr,hf,hlen,hend,hpc,h15⟩ := hz
            have hregs : RegsExcept s0 z topChainRegs := by
              intro r hrn
              apply hr r
              · intro hh;exact hrn ((by decide : chainRegs ⊆ topChainRegs) hh)
              · intro hh;subst r;exact hrn (by decide)
            have hframe : Frame s0 z topChainWrites := by
              exact hf
            have hready := topLeafReady_of w pk index c t s0 z a ends hpre he hpc hregs hframe h15 hlen
              (fun j hj => by have h := hend j (by omega);exact h)
            obtain ⟨u,st,hu⟩ := leafT_step w pk index c hc hidx ends z hready
            exact GoodQ.steps' st (hR ends u hu) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)) s0 hIn
        have e : chainsP w 0 (route index 0).2 (route index 0).1 ds = L.topP := by
          rw [(decode_top_sum _ _ hds).1]
          exact (nctx_topP_eq w index _ (trPc 0 c)).symm
        rw [ccM_bind,e]
        exact GoodQ.steps' st0 hG (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
    have := GoodQ.shortHash_bind (f := fun answer => match decode 0 answer with
      | none => pure none
      | some digits => chainsP w 0 (route index 0).2 (route index 0).1 digits >>= R) hf h5 hv hin H
    rw [hblk] at this
    exact GoodQ.steps' hst this (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

end SigGolfCandidate.T3M
