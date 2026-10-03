import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.W9Machine.WctRoutineModel

section


namespace W9Machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M shortHash pad64 Digest)
theorem chainPiece_shortHash {β : Type} (p : ChainPiece)
    (hlink : sliceChecked p.pc p.words = true) (hcheck : p.checked = true)
    (s : MachineState) (hpc : s.pc = pcOf p.pc)
    (hob : ∀ o ∈ p.result.st.obl, o.holds s) (hstop : p.result.stop = .ecall)
    (N C A : Nat) (Q : Prop) (input : List UInt8)
    (f : Digest → M β) (K : β → OracleComp HashSpec Obs)
    (h5 : (p.result.toState s).getReg .x5 = 0)
    (hv : hashArgumentsValid (p.result.toState s) = true)
    (hin : hashInput (p.result.toState s) = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQFor Frozen.image (writeHash (p.result.toState s) a)
      N C Q A (ccM (f (a.extractLsb' 0 128)) K)) :
    GoodQFor Frozen.image s (N + 1 + p.result.steps)
      (C + 8 * (toQ (pad64 input)).blocks + p.result.cycles) Q
      (A + 8 * (toQ (pad64 input)).blocks + p.result.cycles)
      (ccM (shortHash input >>= f) K) := by
  exact GoodQFor.steps (chainPiece_steps p hlink hcheck s hpc hob)
    (GoodQFor.shortHash_bind (chainPiece_ecall p hlink hcheck s hob hstop) h5 hv hin h)
end W9Machine
end

section


namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify RiscvZkvm.Rv64
def chainPlan : List ChainPiece → MachineState → OracleComp HashSpec MachineState
  | [], s => pure s
  | p :: ps, s =>
      let t := p.result.toState s
      if p.isHash then do
        let ans ← (liftM (HashSpec.query (hashInput t)) : OracleComp HashSpec (BitVec 256))
        chainPlan ps (writeHash t ans)
      else chainPlan ps t
def planFuel : List ChainPiece → Nat
  | [] => 0
  | p :: ps => planFuel ps + p.result.steps + if p.isHash then 1 else 0
def planCycles : List ChainPiece → Nat
  | [] => 0
  | p :: ps => planCycles ps + p.totalCycles
def PlanReady : List ChainPiece → MachineState → (MachineState → Prop) → Prop
  | [], s, post => post s
  | p :: ps, s, post =>
      sliceChecked p.pc p.words = true ∧ p.checked = true ∧ s.pc = pcOf p.pc ∧
      (∀ o ∈ p.result.st.obl, o.holds s) ∧
      (if p.isHash then
        p.result.stop = .ecall ∧ (p.result.toState s).getReg .x5 = 0 ∧
        hashArgumentsValid (p.result.toState s) = true ∧
        (hashInput (p.result.toState s)).blocks = 1 ∧
        ∀ ans, PlanReady ps (writeHash (p.result.toState s) ans) post
      else PlanReady ps (p.result.toState s) post)
theorem chainPlan_good (ps : List ChainPiece) (s : MachineState) (post : MachineState → Prop)
    (hready : PlanReady ps s post) (N C A : Nat) (Q : Prop)
    (K : MachineState → OracleComp HashSpec Obs)
    (hK : ∀ t, post t → GoodQFor Frozen.image t N C Q A (K t)) :
    GoodQFor Frozen.image s (N + planFuel ps) (C + planCycles ps) Q (A + planCycles ps)
      (cc (chainPlan ps s) K) := by
  induction ps generalizing s with
  | nil => simpa only [chainPlan, planFuel, planCycles, Nat.add_zero, cc_pure] using hK s hready
  | cons p ps ih =>
    obtain ⟨hl, hc, hpc, hob, hr⟩ := hready
    by_cases hh : p.isHash = true
    · rw [if_pos hh] at hr
      obtain ⟨hstop, h5, hv, hb, htail⟩ := hr
      have hq := GoodQFor.query (chainPiece_ecall p hl hc s hob hstop) h5 hv rfl
        (fun ans => ih _ (htail ans))
      have hs := GoodQFor.steps (chainPiece_steps p hl hc s hpc hob) hq
      simpa only [chainPlan, if_pos hh, cc_bind, planFuel, planCycles,
        ChainPiece.totalCycles, hh, if_true, hb, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    · rw [if_neg hh] at hr
      have hs := GoodQFor.steps (chainPiece_steps p hl hc s hpc hob) (ih _ hr)
      simpa only [chainPlan, if_neg hh, planFuel, planCycles, ChainPiece.totalCycles,
        Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
end W9Machine
end
