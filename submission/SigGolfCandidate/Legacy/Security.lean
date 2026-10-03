import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Interpreter.Decode

section




namespace SigGolfCandidate.Legacy
def BUDGET_KEYGEN : Nat := 2 ^ 20
def BUDGET_SIGN : Nat := 2 ^ 17
def BUDGET_EXPAND : Nat := 2 ^ 20
def LIFETIME : Nat := 2 ^ 32
def SECURITY_BITS : Nat := 127
def CYCLE_LIMIT : Nat := 2 ^ 32
def MEMORY_BYTES : Nat := 2 ^ 24
def MAX_IMAGE_BYTES : Nat := 2 ^ 20
def MAX_CACHE_BYTES : Nat := 2 ^ 17
def MAX_SIGNATURE_BYTES : Nat := 2 ^ 14
def MAX_WITNESS_BYTES : Nat := 2 ^ 17
noncomputable def FAILURE : ENNReal := 1 / 2 ^ 128
abbrev Byte := BitVec 8
abbrev Bytes (n : Nat) := BitVec (8 * n)
abbrev SecretKey := Bytes 32
abbrev Message := Bytes 32
abbrev PublicKey := Bytes 16
inductive Phase where
  | keygen | sign | expand | verify
  deriving DecidableEq, Repr
def Phase.budget : Phase → Nat
  | .keygen => BUDGET_KEYGEN
  | .sign => BUDGET_SIGN
  | .expand => BUDGET_EXPAND
  | .verify => 0
def Phase.budgeted : List Phase := [.keygen, .sign, .expand]
structure Sizes where
  signature : Nat
  witness : Nat
  cache : Nat
  deriving DecidableEq, Repr
structure Layout where
  message : Nat
  secretKey : Nat
  publicKey : Nat
  cache : Nat
  signature : Nat
  witness : Nat
  deriving DecidableEq, Repr
def Sizes.Valid (sizes : Sizes) : Prop :=
  1 ≤ sizes.signature ∧ sizes.signature ≤ MAX_SIGNATURE_BYTES ∧ sizes.witness ≤ MAX_WITNESS_BYTES ∧
    sizes.cache ≤ MAX_CACHE_BYTES
def witnessCycles (bytes : Nat) : Nat := (bytes + 255) / 256
end SigGolfCandidate.Legacy
end

section

namespace SigGolfCandidate.Legacy
open OracleSpec OracleComp
abbrev Query := (n : Nat) × Bytes (64 * (n + 1))
def Query.blocks (query : Query) : Nat := query.1 + 1
abbrev HashSpec : OracleSpec Query := Query →ₒ BitVec 256
abbrev Hash := QueryImpl HashSpec Id
abbrev World := unifSpec + HashSpec
noncomputable def withRandomOracle {α : Type} (program : OracleComp HashSpec α) : ProbComp α :=
  (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) program).run' ∅
noncomputable def withRandomness {α : Type} (program : OracleComp World α) : ProbComp α :=
  (simulateQ (unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))) program).run' ∅
noncomputable def sampleSecretKey : ProbComp SecretKey := $ᵗ SecretKey
end SigGolfCandidate.Legacy
end

section



namespace SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter OracleComp OracleSpec
structure Image where
  code : List (BitVec 32)
  data : List Byte
  deriving Repr
def Image.byteSize (image : Image) : Nat := 4 * image.code.length + image.data.length
def dataBase (image : Image) : Nat := 16 * ((MEMORY_BYTES - image.data.length) / 16)
def signatureBase (sizes : Sizes) : Nat := 0x60 + 8 * ((sizes.cache + 7) / 8)
def witnessBase (sizes : Sizes) : Nat := signatureBase sizes + 8 * ((sizes.signature + 7) / 8)
def standardLayout (sizes : Sizes) : Layout :=
  ⟨0, 0x20, 0x40, 0x60, signatureBase sizes, witnessBase sizes⟩
def layoutBuffers (layout : Layout) (sizes : Sizes) : List (Nat × Nat) :=
  [(layout.message, 32), (layout.secretKey, 32), (layout.publicKey, 16),
   (layout.cache, sizes.cache), (layout.signature, sizes.signature),
   (layout.witness, sizes.witness)]
def disjointBuffers (left right : Nat × Nat) : Prop :=
  left.2 = 0 ∨ right.2 = 0 ∨ left.1 + left.2 ≤ right.1 ∨ right.1 + right.2 ≤ left.1
instance (left right : Nat × Nat) : Decidable (disjointBuffers left right) := by
  unfold disjointBuffers
  infer_instance
def buffersDisjoint : List (Nat × Nat) → Bool
  | [] => true
  | first :: rest =>
      rest.all (fun second => decide (disjointBuffers first second)) && buffersDisjoint rest
def layoutValid (layout : Layout) (sizes : Sizes) (image : Image) : Prop :=
  (layoutBuffers layout sizes).all (fun buffer =>
    decide (buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤ dataBase image)) = true ∧
  buffersDisjoint (layoutBuffers layout sizes) = true
instance (layout : Layout) (sizes : Sizes) (image : Image) :
    Decidable (layoutValid layout sizes image) := by
  unfold layoutValid
  infer_instance
def Image.Valid (image : Image) (sizes : Sizes) (layout : Layout) : Prop :=
  image.byteSize < MAX_IMAGE_BYTES ∧ layoutValid layout sizes image
instance (image : Image) (sizes : Sizes) (layout : Layout) : Decidable (image.Valid sizes layout) :=
  inferInstanceAs (Decidable (image.byteSize < MAX_IMAGE_BYTES ∧ layoutValid layout sizes image))
def rangeValid (address : BitVec 64) (bytes : Nat) : Bool :=
  decide (address.toNat + bytes ≤ MEMORY_BYTES)
def accessValid (address : BitVec 64) (bytes : Nat) : Bool :=
  rangeValid address bytes && decide (address.toNat % bytes = 0)
inductive WordOp where
  | add | sub | sll | srl | sra | mul | div | divu | rem | remu
  deriving DecidableEq, Repr
inductive Instruction where
  | base (instruction : Instr)
  | word (op : WordOp) (rd rs1 rs2 : Reg)
  | sraiw (rd rs1 : Reg) (shift : BitVec 5)
  deriving Repr
def decodeInstruction (word : BitVec 32) : Option Instruction := do
  let opcode := (word.extractLsb' 0 7).toNat
  let rd := regOfBits (word.extractLsb' 7 5)
  let rs1 := regOfBits (word.extractLsb' 15 5)
  let rs2 := regOfBits (word.extractLsb' 20 5)
  let f3 := (word.extractLsb' 12 3).toNat
  let f7 := (word.extractLsb' 25 7).toNat
  if opcode = 0x73 then
    if word = 0x00000073 then return .base .ECALL
    else if word = 0x00100073 then return .base .EBREAK
    else none
  else if opcode = 0x3b then
    let op ← match f7, f3 with
      | 0, 0 => some WordOp.add
      | 0x20, 0 => some .sub
      | 0, 1 => some .sll
      | 0, 5 => some .srl
      | 0x20, 5 => some .sra
      | 1, 0 => some .mul
      | 1, 4 => some .div
      | 1, 5 => some .divu
      | 1, 6 => some .rem
      | 1, 7 => some .remu
      | _, _ => none
    return .word op rd rs1 rs2
  else if opcode = 0x1b && f3 = 5 && f7 = 0x20 then
    return .sraiw rd rs1 (word.extractLsb' 20 5)
  else
    return .base (← RiscvZkvm.Interpreter.decode word)
def wordResult (op : WordOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % 32)
  | .srl => a >>> (b.toNat % 32)
  | .sra => a.sshiftRight (b.toNat % 32)
  | .mul => a * b
  | .div => if b = 0 then BitVec.allOnes 32 else a.sdiv b
  | .divu => if b = 0 then BitVec.allOnes 32 else a / b
  | .rem => if b = 0 then a else a.srem b
  | .remu => if b = 0 then a else a % b
def memoryArgumentsValid (state : MachineState) : Instr → Bool
  | .LB _ rs off | .LBU _ rs off | .SB rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 1
  | .LH _ rs off | .LHU _ rs off | .SH rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 2
  | .LW _ rs off | .LWU _ rs off | .SW rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 4
  | .LD _ rs off | .SD rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 8
  | _ => true
def ordinaryStep (state : MachineState) : Instruction → Option MachineState
  | .base (.ECALL) | .base (.EBREAK) | .base (.CSRS _ _) => none
  | .base (.LI _ _) | .base (.MV _ _) | .base (.NOP) => none
  | .base instruction =>
      if memoryArgumentsValid state instruction then some (execInstrBr state instruction) else none
  | .word op rd rs1 rs2 =>
      let value := wordResult op ((state.getReg rs1).truncate 32) ((state.getReg rs2).truncate 32)
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))
  | .sraiw rd rs shift =>
      let value := ((state.getReg rs).truncate 32).sshiftRight shift.toNat
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))
def instructionCycles : Instruction → Nat
  | .base (.MUL ..) | .base (.MULH ..) | .base (.MULHSU ..) | .base (.MULHU ..)
  | .base (.DIV ..) | .base (.DIVU ..) | .base (.REM ..) | .base (.REMU ..) => 4
  | .word .mul .. | .word .div .. | .word .divu .. | .word .rem .. | .word .remu .. => 4
  | _ => 1
def fetch (image : Image) (state : MachineState) : Option Instruction := do
  if state.pc.toNat < 0x1000 || state.pc.toNat % 4 != 0 then none else
    let word ← image.code[(state.pc.toNat - 0x1000) / 4]?
    decodeInstruction word
def hashArgumentsValid (state : MachineState) : Bool :=
  let source := state.getReg .x10
  let bytes := (state.getReg .x11).toNat
  let destination := state.getReg .x12
  decide (source.toNat % 8 = 0) && decide (0 < bytes ∧ bytes % 64 = 0) && rangeValid source bytes &&
    accessValid destination 8 && rangeValid destination 32
def hashInput (state : MachineState) : Query :=
  let n := (state.getReg .x11).toNat / 64 - 1
  ⟨n, BitVec.ofNat (8 * (64 * (n + 1))) ((List.range (64 * (n + 1))).foldl (fun acc i =>
    acc + (state.getByte (state.getReg .x10 + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0)⟩
def writeHash (state : MachineState) (answer : BitVec 256) : MachineState :=
  (state.writeWords (state.getReg .x12)
    [answer.extractLsb' 0 64, answer.extractLsb' 64 64,
      answer.extractLsb' 128 64, answer.extractLsb' 192 64]).setPC (state.pc + 4)
inductive Exit where
  | success | failure | unfinished
  deriving DecidableEq, Repr
structure Execution where
  exit : Exit
  state : MachineState
  cycles : Nat := 0
  hashCalls : Nat := 0
  hashCompressions : Nat := 0
def Execution.charge (result : Execution) (cycles hashes blocks : Nat) : Execution :=
  { result with
    cycles := cycles + result.cycles
    hashCalls := hashes + result.hashCalls
    hashCompressions := blocks + result.hashCompressions }
def execute : Nat → Image → MachineState → OracleComp HashSpec Execution
  | 0, _, state => pure ⟨.unfinished, state, 0, 0, 0⟩
  | fuel + 1, image, state =>
    match fetch image state with
    | none => pure ⟨.failure, state, 0, 0, 0⟩
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 && hashArgumentsValid state then do
        let input := hashInput state
        let answer ← HashSpec.query input
        let result ← execute fuel image (writeHash state answer)
        return result.charge (8 * input.blocks) 1 input.blocks
      else if state.getReg .x5 = 1 then
        pure ⟨if state.getReg .x10 = 0 then .success else .failure, state, 1, 0, 0⟩
      else pure ⟨.failure, state, 1, 0, 0⟩
    | some instruction =>
      match ordinaryStep state instruction with
      | none => pure ⟨.failure, state, 1, 0, 0⟩
      | some next => (fun result => result.charge (instructionCycles instruction) 0 0) <$>
          execute fuel image next
end SigGolfCandidate.Legacy.Riscv
end

section

namespace SigGolfCandidate.Legacy
open OracleComp OracleSpec RiscvZkvm.Rv64
structure Submission where
  sizes : Sizes
  layout : Layout
  image : Phase → Riscv.Image
def Submission.score (submission : Submission) (cycles : Nat) : Nat :=
  submission.sizes.signature * cycles
def Input (sizes : Sizes) : Phase → Type
  | .keygen => SecretKey
  | .sign => SecretKey × Bytes sizes.cache × Message
  | .expand => Message × PublicKey × Bytes sizes.signature
  | .verify => Message × PublicKey × Bytes sizes.witness
def Output (sizes : Sizes) : Phase → Type
  | .keygen => PublicKey × Bytes sizes.cache
  | .sign => Bytes sizes.signature
  | .expand => Bytes sizes.witness
  | .verify => Unit
def bytes {n : Nat} (value : Bytes n) : List Byte :=
  (List.range n).map fun i => value.extractLsb' (8 * i) 8
def readBuffer (state : MachineState) (address n : Nat) : Bytes n :=
  BitVec.ofNat (8 * n) ((List.range n).foldl
    (fun acc i => acc + (state.getByte (BitVec.ofNat 64 (address + i))).toNat * 2 ^ (8 * i)) 0)
def inputBuffers (sizes : Sizes) (layout : Layout) :
    (phase : Phase) → Input sizes phase → List (Nat × List Byte)
  | .keygen, secretKey => [(layout.secretKey, bytes secretKey)]
  | .sign, (secretKey, cache, message) =>
      [(layout.secretKey, bytes secretKey), (layout.cache, bytes cache),
        (layout.message, bytes message)]
  | .expand, (message, pk, signature) =>
      [(layout.message, bytes message), (layout.publicKey, bytes pk),
        (layout.signature, bytes signature)]
  | .verify, (message, pk, witness) =>
      [(layout.message, bytes message), (layout.publicKey, bytes pk),
        (layout.witness, bytes witness)]
def initialState (submission : Submission) (phase : Phase) (input : Input submission.sizes phase) :
    Option MachineState :=
  let image := submission.image phase
  if image.Valid submission.sizes submission.layout then
    let blank : MachineState :=
      { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
    let withData := blank.writeBytesAsWords (BitVec.ofNat 64 (Riscv.dataBase image)) image.data
    let loaded := (inputBuffers submission.sizes submission.layout phase input).foldl
      (fun state buffer => state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) withData
    some (loaded.setReg .x2 (BitVec.ofNat 64 (Riscv.dataBase image)))
  else none
def readOutput (sizes : Sizes) (layout : Layout) :
    (phase : Phase) → MachineState → Output sizes phase
  | .keygen, state =>
      (readBuffer state layout.publicKey 16, readBuffer state layout.cache sizes.cache)
  | .sign, state => readBuffer state layout.signature sizes.signature
  | .expand, state => readBuffer state layout.witness sizes.witness
  | .verify, _ => ()
structure RunResult (α : Type) where
  value : Option α
  finished : Bool
  cycles : Nat
  hashCalls : Nat
  hashCompressions : Nat
def Submission.run (submission : Submission) (phase : Phase) (input : Input submission.sizes phase) :
    OracleComp HashSpec (RunResult (Output submission.sizes phase)) := do
  match initialState submission phase input with
  | none => return ⟨none, true, 0, 0, 0⟩
  | some state =>
    let execution ← Riscv.execute CYCLE_LIMIT (submission.image phase) state
    return ⟨if execution.exit = .success then some (readOutput submission.sizes submission.layout phase execution.state)
      else none, execution.exit != .unfinished, execution.cycles, execution.hashCalls,
      execution.hashCompressions⟩
def Submission.runWith (submission : Submission) (hash : Hash) (phase : Phase)
    (input : Input submission.sizes phase) : RunResult (Output submission.sizes phase) :=
  evalWithAnswerFn hash (submission.run phase input)
structure HonestResult where
  success : Bool
  costs : Phase → Nat
  verificationCycles : Nat
def recordCost (costs : Phase → Nat) (phase : Phase) (cost : Nat) : Phase → Nat :=
  fun other => if other = phase then cost else costs other
def Submission.honest (submission : Submission) (secretKey : SecretKey) (message : Message) :
    OracleComp HashSpec HonestResult := do
  let mut costs : Phase → Nat := fun _ => 0
  let keygen ← submission.run .keygen secretKey
  costs := recordCost costs .keygen keygen.hashCompressions
  let some (pk, cache) := keygen.value | return ⟨false, costs, 0⟩
  let sign ← submission.run .sign (secretKey, cache, message)
  costs := recordCost costs .sign sign.hashCompressions
  let some signature := sign.value | return ⟨false, costs, 0⟩
  let expand ← submission.run .expand (message, pk, signature)
  costs := recordCost costs .expand expand.hashCompressions
  let some witness := expand.value | return ⟨false, costs, 0⟩
  let verify ← submission.run .verify (message, pk, witness)
  costs := recordCost costs .verify verify.hashCompressions
  return ⟨verify.value.isSome, costs, verify.cycles + witnessCycles submission.sizes.witness⟩
noncomputable def Submission.honestWorkload (submission : Submission) (secretKey : SecretKey) :
    ProbComp HonestResult := do
  let message ← ($ᵗ Message : ProbComp Message)
  withRandomOracle (submission.honest secretKey message)
structure HonestSummary where
  allSucceed : Bool := true
  maxCosts : Phase → Nat := fun _ => 0
noncomputable def Submission.allMessages (submission : Submission) (secretKey : SecretKey) :
    OracleComp HashSpec HonestSummary :=
  (Finset.univ : Finset Message).toList.foldlM (fun summary message => do
    let result ← submission.honest secretKey message
    return ⟨summary.allSucceed && result.success,
      fun phase => max (summary.maxCosts phase) (result.costs phase)⟩) {}
end SigGolfCandidate.Legacy
end

section

namespace SigGolfCandidate.Legacy
open OracleComp OracleSpec
structure SigningRequest (sizes : Sizes) where
  message : Message
  cache : Bytes sizes.cache
def Submission.signingOracle (submission : Submission) (secretKey : SecretKey)
    (request : SigningRequest submission.sizes) : OracleComp HashSpec (RunResult (Bytes submission.sizes.signature)) :=
  submission.run .sign (secretKey, request.cache, request.message)
inductive Forgery (sizes : Sizes) where
  | witness (message : Message) (witness : Bytes sizes.witness)
  | signature (message : Message) (signature : Bytes sizes.signature)
inductive Action (sizes : Sizes) (state : Type) where
  | submit (candidate : Forgery sizes)
  | hash (input : Query) (resume : BitVec 256 → state)
  | sign (request : SigningRequest sizes) (resume : Option (Bytes sizes.signature) → state)
  | sample (n : Nat) (resume : Fin (n + 1) → state)
  | step (next : state)
structure Adversary (sizes : Sizes) where
  State : Type
  initial : PublicKey → Bytes sizes.cache → State
  step : State → Action sizes State
structure Transcript (sizes : Sizes) where
  signed : List (Message × Bytes sizes.signature) := []
  signingRequests : Nat := 0
  hashCalls : Nat := 0
def Transcript.record {sizes : Sizes} (transcript : Transcript sizes) (message : Message)
    (result : RunResult (Bytes sizes.signature)) : Transcript sizes :=
  { signed := match result.value with
      | none => transcript.signed
      | some signature => (message, signature) :: transcript.signed
    signingRequests := transcript.signingRequests + 1
    hashCalls := transcript.hashCalls + result.hashCalls }
structure AttackResult where
  won : Bool
  hashCalls : Nat
  deriving DecidableEq, Repr
def Transcript.freshMessage {sizes : Sizes} (transcript : Transcript sizes) (message : Message) : Bool :=
  !transcript.signed.any (fun entry => entry.1 == message)
def Transcript.freshSignature {sizes : Sizes} (transcript : Transcript sizes)
    (message : Message) (signature : Bytes sizes.signature) : Bool :=
  !transcript.signed.contains (message, signature)
def Submission.checkForgery (submission : Submission) (pk : PublicKey)
    (transcript : Transcript submission.sizes) : Forgery submission.sizes → OracleComp HashSpec AttackResult
  | .witness message witness => do
      let verify ← submission.run .verify (message, pk, witness)
      return ⟨verify.value.isSome && transcript.freshMessage message,
        transcript.hashCalls + verify.hashCalls⟩
  | .signature message signature => do
      let expand ← submission.run .expand (message, pk, signature)
      let calls := transcript.hashCalls + expand.hashCalls
      let some witness := expand.value | return ⟨false, calls⟩
      let verify ← submission.run .verify (message, pk, witness)
      return ⟨verify.value.isSome && transcript.freshSignature message signature,
        calls + verify.hashCalls⟩
def Submission.interact (submission : Submission) (adversary : Adversary submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) : Nat → adversary.State → Transcript submission.sizes →
      OracleComp World AttackResult
  | 0, _, transcript => pure ⟨false, transcript.hashCalls⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit candidate => liftM (submission.checkForgery pk transcript candidate)
      | .hash input resume => do
          let answer ← liftM (HashSpec.query input)
          submission.interact adversary secretKey pk rounds (resume answer)
            { transcript with hashCalls := transcript.hashCalls + 1 }
      | .sign request resume => do
          if transcript.signingRequests < LIFETIME then
            let result ← liftM (submission.signingOracle secretKey request)
            submission.interact adversary secretKey pk rounds (resume result.value)
              (transcript.record request.message result)
          else return ⟨false, transcript.hashCalls⟩
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          submission.interact adversary secretKey pk rounds (resume answer) transcript
      | .step next => submission.interact adversary secretKey pk rounds next transcript
noncomputable def Submission.securityExperiment (submission : Submission)
    (adversary : Adversary submission.sizes) (rounds : Nat) : ProbComp AttackResult :=
  withRandomness do
    let secretKey ← liftM sampleSecretKey
    let keygen ← liftM (submission.run .keygen secretKey)
    let some (pk, cache) := keygen.value | return ⟨false, keygen.hashCalls⟩
    submission.interact adversary secretKey pk rounds (adversary.initial pk cache)
      { hashCalls := keygen.hashCalls }
def Submission.Secure (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (rounds Q : Nat), 1 ≤ Q →
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q |
      submission.securityExperiment adversary rounds] ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS
end SigGolfCandidate.Legacy
end
