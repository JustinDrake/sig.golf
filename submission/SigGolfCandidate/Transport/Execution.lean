import SigGolf
import SigGolfCandidate.Legacy

/-!
Transport of the baseline's instrumented execution model to the organizer contract.
The private model is copied from leanEthereum/sig.golf-dev at a3960394d13c; the current
organizer-owned definitions remain unchanged at the repository root.
The legacy model is private proof machinery; the exported certificate must use SigGolf.Certificate.
-/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Transport
open OracleComp RiscvZkvm.Rv64

def program : Legacy.Phase → SigGolf.Program
  | .keygen => .keygen
  | .sign => .sign
  | .expand => .expand
  | .verify => .verify

def sizes (s : Legacy.Sizes) : SigGolf.Sizes := ⟨s.signature, s.witness, s.cache⟩
def layout (l : Legacy.Layout) : SigGolf.Layout :=
  ⟨l.message, l.secretKey, l.publicKey, l.cache, l.signature, l.witness⟩
def image (i : Legacy.Riscv.Image) : SigGolf.Riscv.Image := ⟨i.code, i.data⟩
def exit : Legacy.Riscv.Exit → SigGolf.Riscv.Exit
  | .success => .success
  | .failure => .failure
  | .unfinished => .unfinished

def execution (e : Legacy.Riscv.Execution) : SigGolf.Riscv.Execution :=
  ⟨exit e.exit, e.state, e.cycles, e.hashCompressions⟩

theorem decode_eq (w : BitVec 32) :
    Legacy.Riscv.decodeInstruction w = SigGolf.Riscv.decodeInstruction w := rfl

theorem memory_eq (s : MachineState) (i : Instr) :
    Legacy.Riscv.memoryArgumentsValid s i = SigGolf.Riscv.memoryArgumentsValid s i := by
  cases i <;> rfl

theorem ordinary_eq (s : MachineState) (i : Legacy.Riscv.Instruction) :
    Legacy.Riscv.ordinaryStep s i = SigGolf.Riscv.ordinaryStep s i := by
  cases i with
  | base i => cases i <;> simp [Legacy.Riscv.ordinaryStep, SigGolf.Riscv.ordinaryStep, memory_eq]
  | word op rd rs1 rs2 => rfl
  | sraiw rd rs1 shift => rfl

theorem fetch_eq (i : Legacy.Riscv.Image) (s : MachineState) :
    Legacy.Riscv.fetch i s = SigGolf.Riscv.fetch (image i) s := by
  simp [Legacy.Riscv.fetch, SigGolf.Riscv.fetch, image, decode_eq]
  split
  · rw [if_neg (by omega)]
  · rw [if_pos (by omega)]
    cases i.code[(s.pc.toNat - 4096) / 4]? <;> rfl

lemma fold_range (f : Nat → Nat) (n a : Nat) :
    (List.range n).foldl (fun acc i => acc + f i) a = a + ∑ i ∈ Finset.range n, f i := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ, Nat.add_assoc]

theorem readBuffer_eq (s : MachineState) (address n : Nat) :
    Legacy.readBuffer s address n = SigGolf.Riscv.readBuffer s address n := by
  simp [Legacy.readBuffer, SigGolf.Riscv.readBuffer, fold_range]

theorem hashInput_eq (s : MachineState) :
    Legacy.Riscv.hashInput s = SigGolf.Riscv.hashInput s := by
  simp [Legacy.Riscv.hashInput, SigGolf.Riscv.hashInput, SigGolf.Riscv.readBuffer,
    fold_range, BitVec.ofNat_add]

theorem hashArguments_eq (s : MachineState) :
    Legacy.Riscv.hashArgumentsValid s = SigGolf.Riscv.hashArgumentsValid s := by
  apply Bool.eq_iff_iff.mpr
  change ((_ && _ && decide (_ ≤ _) && (decide (_ ≤ _) && decide (_ = 0)) && decide (_ ≤ _)) = true ↔
    (_ && _ && decide (_ ≤ _) && decide (_ = 0) && decide (_ ≤ _)) = true)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  unfold Legacy.MEMORY_BYTES SigGolf.MEMORY_BYTES
  omega

theorem charge_eq (e : Legacy.Riscv.Execution) (c h b : Nat) :
    execution (e.charge c h b) = (execution e).charge c b := rfl

theorem cost_eq (i : Legacy.Riscv.Instruction) :
    Legacy.Riscv.instructionCycles i = SigGolf.Riscv.instructionCycles i := rfl

theorem execute_eq (i : Legacy.Riscv.Image) (n : Nat) (s : MachineState) :
    execution <$> Legacy.Riscv.execute n i s = SigGolf.Riscv.execute (image i) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [Legacy.Riscv.execute, SigGolf.Riscv.execute, ← fetch_eq]
    cases hf : Legacy.Riscv.fetch i s with
    | none => rfl
    | some inst =>
      cases inst with
      | base inst =>
        cases inst <;> dsimp only
        all_goals try
          rw [← ordinary_eq]
          split <;> simp_all only [← ih, map_eq_bind_pure_comp, bind_assoc,
            Function.comp_apply, pure_bind] <;> rfl
        simp only [← hashInput_eq, ← hashArguments_eq, Bool.and_eq_true, decide_eq_true_eq]
        split
        · simp only [map_bind, map_pure, ← ih]
          congr 1
          · exact congrArg (fun q : Legacy.Query => (liftM (Legacy.HashSpec.query q) : OracleComp Legacy.HashSpec (BitVec 256))) (hashInput_eq s)
          · funext a
            simp only [Functor.map_map, bind_map_left, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
            simp [execution, Legacy.Riscv.Execution.charge, SigGolf.Riscv.Execution.charge,
              Legacy.Query.blocks, SigGolf.Query.blocks, hashInput_eq]
            rfl
        · split <;> simp only [map_pure]
          · split <;> rfl
          · rfl
      | word op rd r1 r2 =>
        dsimp only
        rw [← ordinary_eq]
        simp only [Legacy.Riscv.ordinaryStep, ← ih, map_bind, map_pure, Functor.map_map,
          bind_map_left, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
        rfl
      | sraiw rd r sh =>
        dsimp only
        rw [← ordinary_eq]
        simp only [Legacy.Riscv.ordinaryStep, ← ih, map_bind, map_pure, Functor.map_map,
          bind_map_left, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
        rfl

def phase : SigGolf.Program → Legacy.Phase
  | .keygen => .keygen
  | .sign => .sign
  | .expand => .expand
  | .verify => .verify

@[simp] theorem phase_program (p : Legacy.Phase) : phase (program p) = p := by cases p <;> rfl
@[simp] theorem program_phase (p : SigGolf.Program) : program (phase p) = p := by cases p <;> rfl

def submission (s : Legacy.Submission) : SigGolf.Submission :=
  ⟨sizes s.sizes, layout s.layout, fun p => image (s.image (phase p))⟩

def input (sz : Legacy.Sizes) : (p : Legacy.Phase) → Legacy.Input sz p → SigGolf.Input (sizes sz) (program p)
  | .keygen, x => x
  | .sign, x => x
  | .expand, x => x
  | .verify, x => x

def output (sz : Legacy.Sizes) : (p : Legacy.Phase) → Legacy.Output sz p → SigGolf.Output (sizes sz) (program p)
  | .keygen, x => x
  | .sign, x => x
  | .expand, x => x
  | .verify, x => x

theorem image_valid (i : Legacy.Riscv.Image) (sz : Legacy.Sizes) (l : Legacy.Layout) :
    i.Valid sz l ↔ (image i).Valid (sizes sz) (layout l) := by
  simp [Legacy.Riscv.Image.Valid, SigGolf.Riscv.Image.Valid,
    Legacy.Riscv.layoutValid, SigGolf.Riscv.LayoutValid,
    Legacy.Riscv.layoutBuffers, SigGolf.Riscv.layoutBuffers,
    Legacy.Riscv.buffersDisjoint, List.all_cons, List.all_nil,
    Legacy.Riscv.disjointBuffers, SigGolf.Riscv.DisjointBuffers,
    List.pairwise_cons, List.mem_cons, image, sizes, layout,
    Legacy.Riscv.Image.byteSize, SigGolf.Riscv.Image.byteSize,
    Legacy.Riscv.dataBase, SigGolf.Riscv.dataBase,
    Legacy.MAX_IMAGE_BYTES, SigGolf.MAX_PROGRAM_BYTES,
    Legacy.MEMORY_BYTES, SigGolf.MEMORY_BYTES]

theorem admission (s : Legacy.Submission) (h : s.Admissible) : (submission s).Admission := by
  refine ⟨?_, fun p => (image_valid _ _ _).mp (h.2 (phase p))⟩
  exact ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩

theorem initialState_eq (s : Legacy.Submission) (h : s.Admissible)
    (p : Legacy.Phase) (x : Legacy.Input s.sizes p) :
    Legacy.initialState s p x = some (SigGolf.initialState (submission s) (program p) (input _ p x)) := by
  unfold Legacy.initialState
  rw [if_pos (h.2 p)]
  cases p <;> rfl

theorem readOutput_eq (sz : Legacy.Sizes) (l : Legacy.Layout) (p : Legacy.Phase) (st : MachineState) :
    output sz p (Legacy.readOutput sz l p st) = SigGolf.readOutput (sizes sz) (layout l) (program p) st := by
  cases p <;> simp [output, Legacy.readOutput, SigGolf.readOutput, program, layout, sizes, readBuffer_eq] <;> rfl

def runResult (sz : Legacy.Sizes) (p : Legacy.Phase) (r : Legacy.RunResult (Legacy.Output sz p)) :
    SigGolf.RunResult (SigGolf.Output (sizes sz) (program p)) :=
  ⟨r.value.map (output sz p), r.cycles, r.hashCompressions⟩

theorem run_eq (s : Legacy.Submission) (h : s.Admissible)
    (p : Legacy.Phase) (x : Legacy.Input s.sizes p) :
    runResult s.sizes p <$> s.run p x = (submission s).run (program p) (input _ p x) := by
  simp only [Legacy.Submission.run, SigGolf.Submission.run, initialState_eq s h, map_bind, map_pure]
  have ex := execute_eq (s.image p) Legacy.CYCLE_LIMIT
    (SigGolf.initialState (submission s) (program p) (input _ p x))
  simp only [submission, phase_program] at *
  simp only [Legacy.CYCLE_LIMIT, SigGolf.CYCLE_LIMIT] at ex ⊢
  rw [← ex, bind_map_left]
  congr 1
  funext e
  cases he : e.exit <;> simp [runResult, execution, exit, he, readOutput_eq]

end SigGolfCandidate.Transport
