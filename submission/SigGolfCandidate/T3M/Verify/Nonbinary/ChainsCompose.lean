import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatch

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- The first two chains of each triple fall through to the following inline chain. -/
theorem next_inline (c : NCtx) (s0 : MachineState) (i : Nat) (hi : i<54) (h2 : i%3≠2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    c.ChainIn s0 (i+1) acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  unfold endPc startPc
  have e : (i+1)/3=i/3 := by omega
  by_cases h0 : i%3=0
  · rw [if_pos h0,if_neg (show (i+1)%3≠0 by omega),if_pos (show (i+1)%3=1 by omega)]
    unfold qB;rw [e]
  · rw [if_neg h0,if_pos (show i%3=1 by omega),if_neg (show (i+1)%3≠0 by omega),
      if_neg (show (i+1)%3≠1 by omega)]
    unfold qC;rw [e]

def chainF (c : NCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.val i)
  pure (ends++[v])

def chainsCost (c : NCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => chainCost j (c.dig j)).sum

/-- Finish a nonempty suffix of one triple, before its four-instruction dispatch. -/
theorem group_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<18) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,c.EndInv s0 (3*q+2) ends t → Verify.GoodQ t N C Q A (K ends)) :
    ∀ k i, 3*q ≤ i → i+k = 3*q+3 → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      Verify.GoodQ s (N+40*k) (C+c.chainsCost i k) Q (A+c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro i _ _ h;omega
  | succ k ih =>
    intro i hi hik _ acc s hs
    rw [List.range'_succ,List.foldlM_cons]
    simp only [chainF,bind_assoc,pure_bind,Verify.ccM_bind]
    have H := c.chain_good hc hds hk h0 i (by omega) acc
      (fun ends => Verify.ccM ((List.range' (i+1) k).foldlM c.chainF ends) K)
      (N+40*k) (C+c.chainsCost (i+1) k) (A+c.chainsCost (i+1) k) Q
      (fun v t ht => by
        by_cases hk0 : k=0
        · subst hk0
          have he : i=3*q+2 := by omega
          rw [he] at ht
          simpa [chainsCost] using hK _ t ht
        · have ht' : c.ChainIn s0 (i+1) (acc++[v]) t := c.next_inline s0 i (by omega) (by omega) (acc++[v]) t ht
          exact ih (i+1) (by omega) (by omega) (by omega) (acc++[v]) t ht') s hs
    refine H.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega

end SigGolfCandidate.T3M.Nonbinary.NCtx
