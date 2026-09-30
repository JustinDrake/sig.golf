import SigGolfCandidate.Verify.ChainSem
import SigGolfCandidate.Verify.ThreadedCheckAll

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

private theorem digit_lt8 (c : CCtx) (i : Nat) : dig c i < 8 := by
  unfold dig
  exact Nat.mod_lt _ (by decide)

private theorem singles {i : Nat} (h : isSingle i = true) : i=20 ∨ i=41 := by
  simpa only [isSingle, Bool.or_eq_true, decide_eq_true_eq] using h

private theorem second_parts {i : Nat} (h : isSecond i = true) :
    isSingle i = false ∧ isFirst i = false := by
  cases hs : isSingle i <;> cases hf : isFirst i <;> simp_all [isSecond]

private theorem not_second_parts {i : Nat} (h : isSecond i = false) :
    isSingle i = true ∨ isFirst i = true := by
  cases hs : isSingle i <;> cases hf : isFirst i <;> simp_all [isSecond]

/-- Every context selects only blocks certified by the finite kernel checks. -/
theorem chainEvidence_at (c : CCtx) (hc : c.ok) (i : Nat) (hi : i<42) : ChainEvidence c i := by
  have hl : c.lay<5 := hc.1
  have hd : dig c i<8 := digit_lt8 c i
  have hd2 : c.d2 i<8 := digit_lt8 c _
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro mu hm hm7 hdm
    by_cases hs : isSingle i = true
    · have h := Threaded.single_step_ok (d2:=c.d2 i) hl (singles hs) hm hm7
      simpa only [Threaded.stepOK,Threaded.stepPost,CCtx.s1] using h
    · have hs' : isSingle i = false := Bool.eq_false_iff.mpr hs
      by_cases hf : isFirst i = true
      · have h := Threaded.first_step_ok hl (Threaded.first_member hi hf) hd2 hm hm7
        simpa only [Threaded.stepOK,Threaded.stepPost,CCtx.s1] using h
      · have hf' : isFirst i = false := Bool.eq_false_iff.mpr hf
        obtain ⟨hp,hpos⟩ := Threaded.second_member hi hf' hs'
        have heq : i-1+1=i := by omega
        have hd2eq : c.d2 i=dig c i := by simp only [CCtx.d2,hf',Bool.false_eq_true,if_false]
        have h := Threaded.second_step_ok hl hp hd hdm hm7
        simpa only [Threaded.stepOK,Threaded.stepPost,CCtx.s1,heq,hd2eq] using h
  · intro hz hn
    have h := Threaded.common_head_ok hl (Threaded.common_member hi hz (not_second_parts hn))
    exact h
  · intro hn
    by_cases hs : isSingle i = true
    · have h := optBeq_eq (Threaded.single_entry_at hl (singles hs) hd)
      simpa only [entryCtxExp,entIdx,CCtx.s1,CCtx.endPc,Threaded.chainS1,
        Threaded.chainEnd,hs,Bool.true_eq,if_true] using h
    · have hs' : isSingle i = false := Bool.eq_false_iff.mpr hs
      have hf : isFirst i = true := (not_second_parts hn).resolve_left hs
      have h := optBeq_eq (Threaded.first_entry_at hl (Threaded.first_member hi hf) hd hd2)
      simpa only [Threaded.entryCheck,entryCtxExp,entIdx,pf,CCtx.s1,CCtx.endPc,
        Threaded.chainS1,Threaded.chainEnd,CCtx.d2,hs',hf,Bool.false_eq_true,Bool.true_eq,
        if_false,if_true] using h
  · intro hsecond
    obtain ⟨hs,hf⟩ := second_parts hsecond
    obtain ⟨hp,hpos⟩ := Threaded.second_member hi hf hs
    have heq : i-1+1=i := by omega
    have h := Threaded.second_ok hl hp hd
    simpa only [Threaded.secondOK,Threaded.secondPost,heq] using h
  · intro hsecond
    obtain ⟨hs,hf⟩ := second_parts hsecond
    obtain ⟨hp,hpos⟩ := Threaded.second_member hi hf hs
    have heq : i-1+1=i := by omega
    have h := Threaded.tail_ok hl hp hd
    simpa only [Threaded.tailOK,heq] using h

#print axioms chainEvidence_at
end SigGolfCandidate.Verify
