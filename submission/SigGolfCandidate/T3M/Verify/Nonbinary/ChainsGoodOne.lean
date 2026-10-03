import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodRest

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def tableJump (i : Nat) : Nat := if i%3=0 then 1 else 0

/-- T3Z (BIG3): a head is `5` (inline: the table load with the first digit, no first-rung `sb`) or `6` (table slot:
the same load and the jump past the first rung's `sb`); a max-digit copy is `4` (inline, no bump) or `5` (table slot,
no `s9` update). -/
def chainCost (i d : Nat) : Nat :=
  if d=topMax i then 4+tableJump i
  else 5+tableJump i+9*(topMax i-d)-(if d+1=topMax i then 1 else 0)

theorem chainCost_positive (i d : Nat) (hd : d< topMax i) :
    chainCost i d=5+tableJump i+preCost i d := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost preCost
  rw [if_neg (by omega)]
  split_ifs <;> omega

theorem positive_head (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (hd : c.dig i< topMax i) (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃t,Steps vimage s (5+tableJump i) (5+tableJump i) t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  have hl : last i+1=topMax i := by have := topMax_bounds i;unfold last;omega
  have hsp := c.startPc_lt hds i hi
  by_cases htab : i%3=0
  · have hrun2 := c.chk_tail hds i (c.dig i) hi htab (by omega)
    have hrp : c.rungPc i (c.dig i)+1<210432 := by
      have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
      have hl2 := last_bounds i
      unfold rungPc qb
      rw [if_pos htab]
      omega
    by_cases ht : c.dig i=last i
    · have hrun1 := c.chk_headJTerm hds i hi htab ht
      obtain ⟨t,hst,htp⟩ := c.headJTerm_step hc hk h0 i hi ht hsp hrp hrun1 hrun2 acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
    · have hrun1 := c.chk_headJ hds i hi htab (by omega)
      obtain ⟨t,hst,htp⟩ := c.headJ_step hc hk h0 i hi (by omega) hsp hrp hrun1 hrun2 acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
  · by_cases ht : c.dig i=last i
    · have hrun := c.chk_headRTerm hds i hi htab ht
      have hr : c.rungPc i (c.dig i)=c.startPc i+3 := by rw [inline_rungPc c i htab,if_pos ht]
      obtain ⟨t,hst,htp⟩ := c.headRTerm_step hc hk h0 i hi ht hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
    · have hrun := c.chk_headR hds i hi htab (by omega)
      have hr : c.rungPc i (c.dig i)=c.startPc i+4 := by rw [inline_rungPc c i htab,if_neg ht]
      obtain ⟨t,hst,htp⟩ := c.headR_step hc hk h0 i hi (by omega) hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩

/-- One exact mixed-radix chain, ending before the next dispatch. -/
theorem chain_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → Verify.GoodQ t N C Q A (K (acc++[v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    Verify.GoodQ s (N+40) (C+chainCost i (c.dig i)) Q (A+chainCost i (c.dig i))
      (Verify.ccM (chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.val i))
        (fun v => K (acc++[v]))) := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  have hd := hds i hi
  have hsp := c.startPc_lt hds i hi
  by_cases hmax : c.dig i=topMax i
  · rw [hmax,Nat.sub_self]
    have hp : chainP 0 c.tree c.leaf i (topMax i) 0 (c.pad0 i) (c.pad1 i) (c.val i)=pure (c.val i) := rfl
    rw [hp,Verify.ccM_pure]
    by_cases htab : i%3=0
    · obtain ⟨t,hst,ht⟩ := c.copyN_step hc hk h0 i hi hsp
        (c.chk_copyJ hds i hi htab hmax) acc s hs
      exact Verify.GoodQ.steps' hst (hK _ _ ht) (by omega) (by simp [chainCost,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,tableJump,htab]⟩)
    · obtain ⟨t,hst,ht⟩ := c.copyFH_step hc hk h0 i hi hsp
        (c.inline_copy_end i htab hmax) (c.chk_copyF hds i hi htab hmax) acc s hs
      exact Verify.GoodQ.steps' hst (hK _ _ ht) (by omega) (by simp [chainCost,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,tableJump,htab]⟩)
  · have hd' : c.dig i< topMax i := by omega
    rw [chainP_rest]
    have H := c.steps_good hc hds hk h0 i hi acc K N C A Q hK (last i-c.dig i) (c.dig i) (by omega) (le_refl _)
    obtain ⟨t,hst,ht⟩ := c.positive_head hc hds hk h0 i hi hd' acc s hs
    have hj : tableJump i≤1 := by unfold tableJump;split <;> omega
    have he := chainCost_positive i (c.dig i) hd'
    exact Verify.GoodQ.steps' hst (H _ _ ht) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

#print axioms chain_good
end SigGolfCandidate.T3M.Nonbinary.NCtx
