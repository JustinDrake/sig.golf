import SigGolfCandidate.AlternativeVerifierTemplates

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

namespace VerifyImage
open ChainCode FrontCode

/-- Branch targets use absolute positions in the core, including its rejection stub. -/
def appendLayer (initialPart : List Instruction) (lay : Nat) : List Instruction :=
  initialPart ++ LayerCode.caller lay (4*initialPart.length) ++ LayerCode.leafStart lay ++
    LayerFoldCode.dispatch lay 0 ++ (if lay = 0 then LayerFoldCode.dispatch lay 1 else [])

def compare (pc : Nat) : List Instruction :=
  [ld 3 0 384, ld 14 0 160, opR 4 3 3 14,
    ld 24 0 392, ld 26 0 168, opR 4 24 24 26, bor 3 3 24,
    branch 1 3 0 ((4 : Int)-(pc+28 : Nat)), addi 10 0 0, addi 5 0 1, hashInstruction]

def corePrefix : List Instruction :=
  [3,2,1,0].foldl appendLayer (FrontCode.code ++ LayerCode.setup)

def core : List Instruction := corePrefix ++ compare (4*corePrefix.length)

/-- Every fragment's placement requires a separate no-overlap proof. -/
def place (initialPart : List Instruction) (address : Nat) (fragment : List Instruction) : List Instruction :=
  initialPart ++ List.replicate (address/4-initialPart.length) nop ++ fragment

def dispatches : List Instruction :=
  (List.range 16).flatMap fun group => ChainCode.dispatch group ++ List.replicate 4 nop

def code : List Instruction :=
  let a := place core 4096 dispatches
  let b := place a 65536 ChainCode.bodies
  let c := place b 196608 ForestCode.shapes
  let d := place c 524288 ChainCode.entries
  place d 655360 LayerFoldCode.tables

/-- A complete proposed verifier image, not yet refined to the alternate reference.
The scored submission remains the original certified four-program suite. -/
def image : SigGolfCandidate.Legacy.Riscv.Image := ⟨code, LayerCode.maskData⟩

/-! Structural checks are kernel proofs about assembled list sizes; they do not
execute or benchmark the verifier. The execution/refinement theorem is separate. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem core_room : core.length ≤ 1024 := by
  -- Count list constructors without evaluating any instruction word.
  norm_num [core, corePrefix, appendLayer, compare,
    FrontCode.code, FrontCode.digestPrefix, FrontCode.forestSetup,
    FrontCode.forestCall, FrontCode.indexCode, FrontCode.forestFinish, FrontCode.li,
    LayerCode.setup, LayerCode.caller, LayerCode.beforeCounterCheck,
    LayerCode.routeCode, LayerCode.encodingHash, LayerCode.digitSum,
    LayerCode.leafStart, LayerFoldCode.dispatch, LayerFoldCode.shapeBase,
    List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem dispatches_length : dispatches.length = 128 := by
  unfold dispatches
  rw [flatMap_length_constant (List.range 16) _ 8]
  · decide
  · intro group hg
    simp [ChainCode.dispatch_length]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem bodies_length : ChainCode.bodies.length = 26693 := by
  have hg (group : Nat) (h : group < 15) :
      ((List.range 64).flatMap (ChainCode.body group)).length = 1776 := by
    simpa only [List.length_flatMap,Function.comp_def,ChainCode.body_length]
      using ChainCode.group_words group h
  have ht : ((List.range 4).flatMap (ChainCode.body 15)).length = 53 := by
    simpa only [List.length_flatMap,Function.comp_def,ChainCode.body_length]
      using ChainCode.tail_words
  unfold ChainCode.bodies
  rw [show (16 : Nat) = 15+1 from rfl,List.range_succ,List.flatMap_append]
  simp only [List.length_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [if_true,ht]
  have hmain : ((List.range 15).flatMap fun group =>
      (List.range (if group = 15 then 4 else 64)).flatMap (ChainCode.body group)).length = 15*1776 := by
    apply flatMap_length_constant
    intro group hgroup
    have hb := List.mem_range.mp hgroup
    rw [if_neg (by omega)]
    exact hg group hb
  rw [hmain]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem forest_length : ForestCode.shapes.length = 65536 := by
  unfold ForestCode.shapes
  rw [flatMap_length_constant (List.range 512) _ 128]
  · decide
  · intro leaf hleaf
    exact ForestCode.shape_length leaf (List.mem_range.mp hleaf)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem entries_length : ChainCode.entries.length = 32768 := by
  unfold ChainCode.entries
  rw [flatMap_length_constant (List.range 256) _ 128]
  · decide
  · intro row hrow
    rw [flatMap_length_constant (List.range 16) _ 8]
    · decide
    · intro group hgroup
      exact ChainCode.entry_length group row

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem folds_length : LayerFoldCode.tables.length = 32768 := by
  simp [LayerFoldCode.tables,List.length_append,LayerFoldCode.table_length,LayerFoldCode.bits]

theorem image_bytes : image.byteSize = 786448 := by
  have hc := core_room
  simp only [image, SigGolfCandidate.Legacy.Riscv.Image.byteSize, code, place,
    List.length_append, List.length_replicate, dispatches_length, bodies_length,
    forest_length, entries_length, folds_length, LayerCode.maskData_length]
  norm_num only [Nat.reduceDiv]
  omega

theorem image_room : image.byteSize < 2^20 := by rw [image_bytes]; decide

end VerifyImage

/-! Initial symbolic block checks for official-kernel validation. These certify
opcode decoding and symbolic transitions up to the next HASH or branch; their
memory obligations still require the image-level framing/refinement proof. -/
namespace AsmChecks
open SigGolfCandidate.Rv

set_option maxRecDepth 4096
set_option maxHeartbeats 500000

sym_block chain_zero := symRun { noAlias := true } (ChainCode.code 0 0) 65536 64
sym_block chain_one := symRun { noAlias := true } (ChainCode.code 0 1) 65536 64
sym_block chain_two := symRun { noAlias := true } (ChainCode.code 0 2) 65536 64
sym_block chain_three := symRun { noAlias := true } (ChainCode.code 0 3) 65536 64
sym_block last_chain_two := symRun { noAlias := true } (ChainCode.code 61 2) 65536 64
sym_block digest_prefix := symRun { noAlias := true } FrontCode.digestPrefix 16 64
sym_block digit_sum := symRun { noAlias := true } LayerCode.digitSum 0 64
sym_block quad_dispatch := symRun { noAlias := true } (ChainCode.dispatch 0) 4096 16
sym_block tail_dispatch := symRun { noAlias := true } (ChainCode.dispatch 15) 4576 16

end AsmChecks

end SigGolfCandidate.Base4Candidate.Reference
