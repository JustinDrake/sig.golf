import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodBounds
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsInline
import SigGolfCandidate.T3M.Verify.Judg

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem chainInputP_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    pad64 (chainInputP lay tree leaf i step p0 p1 v)=chainInputP lay tree leaf i step p0 p1 v :=
  pad64_of_aligned _ (by rw [chainInputP_length])

theorem chainInputP_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    (toQ (chainInputP lay tree leaf i step p0 p1 v)).blocks=1 := by
  rw [blocks_toQ ⟨by rw [chainInputP_length];omega,by rw [chainInputP_length]⟩,chainInputP_length]

def rest (c : NCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (topMax i-m)).foldlM
    (fun v step => shortHash (chainInputP 0 c.tree c.leaf i step (c.pad0 i) (c.pad1 i) v)) v

theorem rest_succ (c : NCtx) (i m : Nat) (h : m ≤ last i) (v : Digest) :
    c.rest i m v=shortHash (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) >>= c.rest i (m+1) := by
  have hm := topMax_bounds i
  unfold last at h
  unfold rest
  rw [show topMax i-m=(topMax i-(m+1))+1 by omega,List.range'_succ,List.foldlM_cons]

theorem rest_max (c : NCtx) (i : Nat) (v : Digest) : c.rest i (topMax i) v=pure v := by
  simp [rest]

theorem chainP_rest (c : NCtx) (i d : Nat) (v : Digest) :
    chainP 0 c.tree c.leaf i d (topMax i-d) (c.pad0 i) (c.pad1 i) v=c.rest i d v := rfl

def preCost (i m : Nat) : Nat := 8+9*(last i-m)+(if m< last i then 1 else 0)

theorem steps_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → Verify.GoodQ t N C Q A (K (acc++[v]))) :
    ∀k m,m+k=last i → c.dig i ≤ m → ∀v s,c.PreHash s0 i acc m v s →
      Verify.GoodQ s (N+3*(topMax i-m)+5) (C+preCost i m) Q (A+preCost i m)
        (Verify.ccM (c.rest i m v) (fun v => K (acc++[v]))) := by
  have hmax := topMax_bounds i
  have hlast := last_bounds i
  have hlastEq : last i+1=topMax i := by unfold last;omega
  intro k
  induction k with
  | zero =>
      intro m hm hd v s hs
      obtain rfl : m=last i := by omega
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc s0 hk h0 i (last i) hi (le_refl _) hd acc v s hs
      rw [rest_succ c i (last i) (le_refl _)]
      have hf := hs.2.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,Verify.GoodQ (writeHash s a) N C Q A
          (Verify.ccM (c.rest i (last i+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        rw [hlastEq,rest_max,Verify.ccM_pure]
        exact hK _ _ ((hpost a).2 rfl)
      have h3 := Verify.GoodQ.shortHash_bind (f:=c.rest i (last i+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputP_pad];exact hin) H
      rw [chainInputP_pad,chainInputP_blocks] at h3
      exact h3.mono (by omega) (by simp [preCost]) (fun hq => ⟨hq,by simp [preCost]⟩)
  | succ k ih =>
      intro m hm hd v s hs
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
      rw [rest_succ c i m (by omega)]
      have hf := hs.2.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,Verify.GoodQ (writeHash s a) (N+3*(topMax i-(m+1))+5+2)
          (C+preCost i (m+1)+(if m+1=last i then 2 else 1)) Q
          (A+preCost i (m+1)+(if m+1=last i then 2 else 1))
          (Verify.ccM (c.rest i (m+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        have hrun := c.chk_rung hds i (m+1) hi (by omega) (by omega) (fun _ => by omega)
        obtain ⟨u,hu,hp⟩ := c.rung_step hc hk i (m+1) hi (by omega) (c.rungPc_lt i _ (by omega)) hrun acc _ _
          ((hpost a).1 (by omega))
        have ht := ih (m+1) (by omega) (by omega) _ _ hp
        exact Verify.GoodQ.steps' hu ht (by split <;> omega) (by omega) (fun hq => ⟨hq,by omega⟩)
      have h3 := Verify.GoodQ.shortHash_bind (f:=c.rest i (m+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputP_pad];exact hin) H
      rw [chainInputP_pad,chainInputP_blocks] at h3
      refine h3.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega

end SigGolfCandidate.T3M.Nonbinary.NCtx
