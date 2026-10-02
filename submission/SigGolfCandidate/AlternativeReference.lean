import SigGolfCandidate.AlternativeVerifierImage

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

namespace Assembler
open ChainCode FrontCode

inductive Item where
  | word (instruction : Instruction)
  | mark (label : Nat)
  | jump (rd label : Nat)
  | imageJump (rd address : Nat)
  | branchTo (funct left right label : Nat)

def emit (instructions : List Instruction) : List Item := instructions.map Item.word

def labelPc (label : Nat) : List Item → Nat → Nat
  | [], _ => 0
  | .mark found :: rest, pc => if label = found then pc else labelPc label rest pc
  | _ :: rest, pc => labelPc label rest (pc+4)

def assembleAt (whole : List Item) : List Item → Nat → List Instruction
  | [], _ => []
  | .mark _ :: rest, pc => assembleAt whole rest pc
  | .word instruction :: rest, pc => instruction :: assembleAt whole rest (pc+4)
  | .jump rd label :: rest, pc =>
    jal rd ((labelPc label whole 0 : Int)-(pc : Int)) :: assembleAt whole rest (pc+4)
  | .imageJump rd address :: rest, pc =>
    jal rd ((address : Int)-(pc : Int)) :: assembleAt whole rest (pc+4)
  | .branchTo funct left right label :: rest, pc =>
    branch funct left right ((labelPc label whole 0 : Int)-(pc : Int)) :: assembleAt whole rest (pc+4)

def assemble (program : List Item) : List Instruction := assembleAt program program 0

/-- Count emitted words without resolving any branch or jump target. -/
def wordCount : List Item → Nat
  | [] => 0
  | .mark _ :: rest => wordCount rest
  | _ :: rest => wordCount rest + 1

theorem assembleAt_length (whole rest : List Item) (pc : Nat) :
    (assembleAt whole rest pc).length = wordCount rest := by
  induction rest generalizing pc with
  | nil => rfl
  | cons item rest ih =>
    cases item <;> simp [assembleAt,wordCount,ih,Nat.add_comm]

theorem assemble_length (program : List Item) :
    (assemble program).length = wordCount program :=
  assembleAt_length program program 0

theorem wordCount_append (left right : List Item) :
    wordCount (left ++ right) = wordCount left + wordCount right := by
  induction left with
  | nil => simp [wordCount]
  | cons item rest ih =>
    cases item <;> simp [wordCount,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem wordCount_emit (instructions : List Instruction) :
    wordCount (emit instructions) = instructions.length := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih => simp [emit,wordCount] at * <;> omega

/-- Addresses used by this assembler are image-relative offsets; the common
0x1000 load base cancels in relative jump displacements.
Static assembler obligations: labels exist, control transfers are aligned,
and every displacement fits the actual instruction field. -/
def labels : List Item → List Nat
  | [] => []
  | .mark label :: rest => label :: labels rest
  | _ :: rest => labels rest

def fitsTransfer (pc address radius : Nat) : Bool :=
  let delta : Int := (address : Int)-(pc : Int)
  decide (- (radius : Int) ≤ delta ∧ delta < (radius : Int) ∧ delta % 4 = 0)

def transfersOK (whole : List Item) : List Item → Nat → Bool
  | [], _ => true
  | .mark _ :: rest, pc => transfersOK whole rest pc
  | .word _ :: rest, pc => transfersOK whole rest (pc+4)
  | .jump _ label :: rest, pc =>
    decide (label ∈ labels whole) && fitsTransfer pc (labelPc label whole 0) (2^20) &&
      transfersOK whole rest (pc+4)
  | .imageJump _ address :: rest, pc =>
    fitsTransfer pc address (2^20) && transfersOK whole rest (pc+4)
  | .branchTo _ _ _ label :: rest, pc =>
    decide (label ∈ labels whole) && fitsTransfer pc (labelPc label whole 0) (2^12) &&
      transfersOK whole rest (pc+4)

def WellFormed (program : List Item) : Prop :=
  (labels program).Nodup ∧ transfersOK program program 0 = true

instance (program : List Item) : Decidable (WellFormed program) := by
  unfold WellFormed
  infer_instance

end Assembler

/-! The key generator uses 32-byte temporary tree slots, so a HASH's full output
cannot corrupt an already-built sibling while parents are constructed in reverse
heap order. Only each slot's low sixteen bytes enter the public tree and cache. -/
namespace KeygenCode
open ChainCode FrontCode Assembler

/-- One selected half of a paired PRF answer, followed by all three chain steps. -/
def chain (source : Nat) : List Instruction :=
  [ld 3 0 source, ld 14 0 (source+8), sd 3 0 304, sd 14 0 312,
    sd 27 0 256, addi 10 0 256, addi 12 0 304, hashInstruction,
    sb 6 0 260, hashInstruction, sb 7 0 260, addi 12 28 0, hashInstruction,
    addi 27 27 64, addi 28 28 16]

def program : List Item :=
  emit ([addi 6 0 1, addi 7 0 2, addi 8 0 3, addi 19 0 31,
      addi 3 0 2, sd 3 0 192, sd 0 0 200, sd 0 0 208, sd 0 0 216,
      sd 0 0 272, sd 0 0 280, sd 0 0 288, sd 0 0 296,
      addi 3 0 514, sd 3 0 832, sd 0 0 848, sd 0 0 856] ++
    (List.range 4).flatMap (fun i => [ld 3 0 (128+8*i), sd 3 0 (224+8*i)]) ++
    li 20 720896 ++ li 21 4096 ++ li 22 851968 ++ [addi 17 0 0]) ++
  [.mark 0] ++
  emit ([slli 29 17 32, sd 29 0 264, sd 29 0 840, ForestCode.sw 17 0 204] ++
    li 27 5376 ++ [addi 28 0 864, addi 18 0 0]) ++
  [.mark 1] ++
  emit ([ForestCode.sw 18 0 196, addi 10 0 192, addi 11 0 64, addi 12 0 320,
      hashInstruction] ++ chain 320 ++ chain 336 ++ [addi 18 18 1]) ++
  [.branchTo 1 18 19 1] ++
  emit [addi 10 0 832, addi 11 0 1024, addi 12 22 0, hashInstruction,
    addi 22 22 32, addi 17 17 1] ++
  [.branchTo 6 17 21 0] ++
  emit (li 23 2048 ++ [addi 3 0 770, sd 3 0 832, sd 0 0 840,
    addi 10 0 832, addi 11 0 64]) ++
  [.mark 2] ++
  emit [ForestCode.sw 23 0 844, slli 3 23 6, add 3 3 20,
    ld 14 3 0, sd 14 0 864, ld 14 3 8, sd 14 0 872,
    ld 14 3 32, sd 14 0 880, ld 14 3 40, sd 14 0 888,
    slli 12 23 5, add 12 12 20, hashInstruction, addi 23 23 1] ++
  [.branchTo 6 23 21 2] ++ emit [srli 21 21 1, srli 23 21 1] ++
  [.branchTo 1 23 0 2] ++
  emit ([ld 3 20 32, sd 3 0 160, ld 3 20 40, sd 3 0 168] ++
    li 3 3330 ++ [sd 3 0 192, sd 0 0 200, addi 25 0 2] ++
    li 21 8192 ++ li 24 32800 ++ [addi 10 0 192, addi 12 0 320]) ++
  [.mark 3] ++
  emit [ForestCode.sw 25 0 204, hashInstruction, slli 3 25 5, add 3 3 20,
    ld 14 3 0, ld 26 0 320, opR 4 14 14 26, sd 14 24 0,
    ld 14 3 8, ld 26 0 328, opR 4 14 14 26, sd 14 24 8,
    addi 25 25 1, addi 24 24 16] ++
  [.branchTo 1 25 21 3] ++
  emit ([sd 0 24 0, sd 0 24 8, sd 0 24 16, sd 0 24 24] ++
    li 31 32736 ++ li 3 3586 ++ [sd 3 31 0, sd 0 31 8, sd 0 31 16, sd 0 31 24] ++
    (List.range 4).flatMap (fun i => [ld 3 0 (128+8*i), sd 3 31 (32+8*i)]) ++
    [addi 10 31 0] ++ li 11 131136 ++ [addi 12 0 320, hashInstruction] ++
    (List.range 4).flatMap (fun i => [ld 3 0 (320+8*i), sd 3 31 (32+8*i)]) ++
    [addi 10 0 0, addi 5 0 1, hashInstruction])

def code : List Instruction := assemble program

def image : SigGolfCandidate.Legacy.Riscv.Image := ⟨code, []⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem image_room : image.byteSize < 2^20 := by
  simp only [image,SigGolfCandidate.Legacy.Riscv.Image.byteSize,code,
    Assembler.assemble_length,List.length_nil,Nat.add_zero,LayerCode.maskData_length]
  decide +kernel

/-- Scratch slots remain inside the pinned memory even with their full HASH outputs. -/
theorem scratch_room : 720896+8192*32 < 2^24 ∧ 163840+32 < 196608 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem assembly_wellFormed : Assembler.WellFormed program := by decide +kernel

end KeygenCode

/-! Signer front end. Local labels 0--3 are reserved for rejection and the
paired digest loop; the forest uses four labels per tree starting at 100.
The program falls through with the FORS root at 288 and index at x25. -/
namespace SignFrontCode
open ChainCode FrontCode Assembler

/-- Authenticate the cache before using any cached node. The stored tag is
saved before its memory is reused for the MAC's private seed input. -/
def authenticate : List Item :=
  [.jump 0 1, .mark 0] ++ emit [addi 10 0 1, addi 5 0 1, hashInstruction] ++
  [.mark 1] ++ emit (li 31 32736 ++
    (List.range 4).flatMap (fun i => [ld 3 31 (32+8*i), sd 3 0 (448+8*i),
      ld 3 0 (128+8*i), sd 3 31 (32+8*i)]) ++
    li 3 3586 ++ [sd 3 31 0, sd 0 31 8, sd 0 31 16, sd 0 31 24] ++
    li 24 163840 ++ [sd 0 24 0, sd 0 24 8, sd 0 24 16, sd 0 24 24,
      addi 10 31 0] ++ li 11 131136 ++ [addi 12 0 320, hashInstruction]) ++
    (List.range 4).flatMap (fun i => emit [ld 3 0 (320+8*i), ld 14 0 (448+8*i)] ++
      [.branchTo 1 3 14 0])

/-- Pack the deliberately unaligned private randomizer query. Only 26 seed
bytes occur in this domain, as in the paired production search. -/
def randomizerInput : List Instruction :=
  [ld 16 0 128, ld 17 0 136, ld 18 0 144, ld 19 0 152,
    slli 3 16 16, addi 3 3 1794, sd 3 0 512,
    srli 3 16 48, slli 14 17 16, bor 3 3 14, sd 3 0 520,
    srli 3 17 48, slli 14 18 16, bor 3 3 14, sd 3 0 528,
    srli 3 18 48, slli 14 19 48, srli 14 14 32, bor 3 3 14,
    ld 16 0 64, slli 14 16 32, bor 3 3 14, sd 3 0 536] ++
  (List.range 3).flatMap (fun i =>
    [ld 17 0 (72+8*i), srli 3 16 32, slli 14 17 32,
      bor 3 3 14, sd 3 0 (544+8*i), addi 16 17 0]) ++
  [srli 3 16 32, sd 3 0 568] ++
  li 3 3074 ++ [sd 3 0 0, sd 0 0 8] ++
  (List.range 4).flatMap (fun i => [ld 3 0 (64+8*i), sd 3 0 (32+8*i)]) ++
  [addi 20 0 0] ++ li 21 (2^20)

def digestTrial (source : Nat) : List Instruction :=
  [ld 3 0 source, sd 3 0 16, ld 3 0 (source+8), sd 3 0 24,
    addi 10 0 0, addi 12 0 352, hashInstruction,
    ld 3 0 368, srli 3 3 58, ld 14 0 376, andi 14 14 63, bor 3 3 14]

def digestSearch : List Item :=
  emit randomizerInput ++ [.mark 2] ++
  emit [ForestCode.sw 20 0 572, addi 10 0 512, addi 11 0 64,
    addi 12 0 320, hashInstruction] ++ emit (digestTrial 320) ++
  [.branchTo 0 3 0 3] ++ emit (digestTrial 336) ++ [.branchTo 0 3 0 3] ++
  emit [addi 20 20 1] ++ [.branchTo 6 20 21 2, .jump 0 0, .mark 3] ++
  emit (li 24 196608 ++ [ld 3 0 16, sd 3 24 0, ld 3 0 24, sd 3 24 8] ++
    (List.range 4).flatMap (fun i => [ld 3 0 (352+8*i), sd 3 0 (448+8*i)]) ++
    [ld 25 0 448, slli 25 25 31, srli 25 25 31, srli 26 25 32,
      slli 26 26 24] ++ li 3 2818 ++
    [add 3 3 26, sd 3 0 512, slli 31 25 32, srli 31 31 32,
      sd 31 0 520, sd 0 0 528, sd 0 0 536,
      sd 0 0 208, sd 0 0 216, sd 0 0 848, sd 0 0 856] ++
    (List.range 4).flatMap (fun i => [ld 3 0 (128+8*i), sd 3 0 (224+8*i)]))

def selectedLeaf (tree : Nat) : List Instruction :=
  let offset := 33+9*tree
  let shift := offset%64
  [ld 28 0 (448+8*(offset/64)), srli 28 28 shift] ++
    (if shift+9 ≤ 64 then [] else
      [ld 14 0 (456+8*(offset/64)), slli 14 14 (64-shift), bor 28 28 14]) ++
    [andi 28 28 511, srli 29 28 1]

def leaf (source : Nat) : List Instruction :=
  [ForestCode.sw 17 0 844, ld 3 0 source, sd 3 0 864,
    ld 3 0 (source+8), sd 3 0 872, addi 10 0 832, addi 12 22 0,
    hashInstruction, addi 17 17 1, addi 22 22 32]

/-- One full height-nine tree. The secret is copied before either leaf hash;
all tree slots are 32-byte aligned, while only their first 16 bytes are used. -/
def forestTree (tree : Nat) : List Item :=
  let label := 100+4*tree
  emit (selectedLeaf tree ++ li 20 262144 ++ li 22 278528 ++
    li 24 (196624+160*tree) ++ li 3 (2050+65536*tree) ++
    [add 3 3 26, sd 3 0 192, sd 31 0 200, addi 3 3 256, sd 3 0 832,
      sd 31 0 840, sd 0 0 880, sd 0 0 888,
      addi 17 0 0, addi 18 0 0, addi 19 0 256]) ++
  [.mark label] ++
  emit [ForestCode.sw 18 0 204, addi 10 0 192, addi 11 0 64,
    addi 12 0 320, hashInstruction] ++ [.branchTo 1 18 29 (label+1)] ++
  emit [andi 3 28 1, slli 3 3 4, addi 3 3 320, ld 14 3 0,
    sd 14 24 0, ld 14 3 8, sd 14 24 8] ++ [.mark (label+1)] ++
  emit (leaf 320 ++ leaf 336 ++ [addi 18 18 1]) ++ [.branchTo 6 18 19 label] ++
  emit (li 3 (2562+65536*tree) ++ [add 3 3 26, sd 3 0 832,
    addi 21 0 512, addi 23 0 256, addi 10 0 832]) ++ [.mark (label+2)] ++
  emit [ForestCode.sw 23 0 844, slli 3 23 6, add 3 3 20,
    ld 14 3 0, sd 14 0 864, ld 14 3 8, sd 14 0 872,
    ld 14 3 32, sd 14 0 880, ld 14 3 40, sd 14 0 888,
    slli 12 23 5, add 12 12 20, hashInstruction, addi 23 23 1] ++
  [.branchTo 6 23 21 (label+2)] ++ emit [srli 21 21 1, srli 23 21 1] ++
  [.branchTo 1 23 0 (label+2)] ++
  emit ([ld 3 20 32, sd 3 0 (544+16*tree),
    ld 3 20 40, sd 3 0 (552+16*tree), addi 28 28 512] ++
    (List.range 9).flatMap (fun level =>
      [srli 3 28 level, opI 19 4 3 3 1, slli 3 3 5, add 3 3 20,
        ld 14 3 0, sd 14 24 (16+16*level),
        ld 14 3 8, sd 14 24 (24+16*level)]))

def program : List Item := authenticate ++ digestSearch ++
  (List.range 17).flatMap forestTree ++ emit FrontCode.forestFinish

def code : List Instruction := assemble program

/- Structural space only: this is not a termination or refinement claim. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem code_room : 4*code.length < 65536 := by
  unfold code
  rw [Assembler.assemble_length]
  decide +kernel

end SignFrontCode

namespace SignLayerCode
open ChainCode FrontCode Assembler

def signatureOffset (lay : Nat) : Nat :=
  if lay = 0 then 2736 else if lay = 1 then 3920 else if lay = 2 then 5024 else 6128

/-- Search exactly the contiguous radix-four antichain used by verification.
The accepted encoding is saved outside all hash buffers. Counters are recovered
by expansion and are not serialized in the compact signature. -/
def search (lay : Nat) : List Item :=
  let label := 2000+10*lay
  emit (LayerCode.routeCode lay ++ li 3 (1026+65536*lay) ++
    [sd 3 0 256, sd 31 0 264, sd 0 0 272, sd 0 0 280,
      addi 26 0 0] ++ li 27 (2^22) ++ li 3 16777200 ++
    [ld 18 3 0, ld 19 3 8, addi 20 0 255, addi 21 0 110]) ++
  [.mark label] ++ emit [addi 3 26 0] ++ emit LayerCode.encodingHash ++
  [.branchTo 1 3 0 (label+1)] ++ emit LayerCode.digitSum ++
  [.branchTo 0 24 21 (label+2), .mark (label+1)] ++
  emit [addi 26 26 1] ++ [.branchTo 6 26 27 label, .jump 0 0, .mark (label+2)] ++
  emit (li 3 24576 ++ [sd 16 3 0, sd 17 3 8])

/-- Shift a two-word little-endian stream by one radix-four digit. -/
def nextDigit : List Instruction :=
  [srli 16 16 2, slli 3 17 62, bor 16 16 3, srli 17 17 2]

def capture : List Instruction :=
  [ld 3 0 304, sd 3 24 0, ld 3 0 312, sd 3 24 8]

/-- Build a complete chain and disclose its selected initialPart. Only the capture
pointer depends on which leaf was selected; hash queries are unaffected. -/
def fullChain (source label : Nat) : List Item :=
  emit [ld 3 0 source, ld 14 0 (source+8), sd 3 0 304, sd 14 0 312,
    sd 27 0 256, andi 29 16 3, addi 10 0 256, addi 12 0 304] ++
  [.branchTo 1 29 0 label] ++ emit capture ++ [.mark label] ++
  (List.range 3).flatMap (fun step =>
    emit ((if step = 0 then [] else [sb (5+step) 0 260]) ++ [hashInstruction]) ++
    [.branchTo 1 29 (6+step) (label+step+1)] ++ emit capture ++
    [.mark (label+step+1)]) ++
  emit ([ld 3 0 304, sd 3 28 0, ld 3 0 312, sd 3 28 8,
    addi 27 27 64, addi 28 28 16, addi 24 24 16] ++ nextDigit)

/-- Rebuild a lower tree, saving only the chosen leaf's prefixes in the output.
The common discarded-initialPart scratch is separate from saved encoding words. -/
def lower (lay : Nat) : List Item :=
  let label := 3000+20*lay
  emit (li 3 (2+65536*lay) ++ [sd 3 0 192, sd 25 0 200,
      sd 0 0 272, sd 0 0 280, sd 0 0 288, sd 0 0 296,
      addi 6 0 1, addi 7 0 2, addi 8 0 3, addi 19 0 31,
      addi 21 0 128, addi 15 0 0] ++ li 20 720896 ++ li 22 724992) ++
  [.mark label] ++ emit (li 3 24576 ++ [ld 16 3 0, ld 17 3 8] ++
    li 24 (196608+signatureOffset lay)) ++ [.branchTo 0 15 23 (label+1)] ++
  emit (li 24 25600) ++ [.mark (label+1)] ++
  emit ([slli 31 15 32, bor 31 31 25, sd 31 0 264, sd 31 0 840,
    ForestCode.sw 15 0 204] ++ li 3 (514+65536*lay) ++ [sd 3 0 832] ++
    li 27 (5376+3968*lay) ++ [addi 28 0 864, addi 18 0 0]) ++
  [.mark (label+2)] ++
  emit [ForestCode.sw 18 0 196, addi 10 0 192, addi 11 0 64,
    addi 12 0 320, hashInstruction] ++
  fullChain 320 (500+20*lay) ++ fullChain 336 (510+20*lay) ++
  emit [addi 18 18 1] ++ [.branchTo 6 18 19 (label+2)] ++
  emit [addi 10 0 832, addi 11 0 1024, addi 12 22 0, hashInstruction,
    addi 22 22 32, addi 15 15 1] ++ [.branchTo 6 15 21 label] ++
  emit (li 3 (770+65536*lay) ++ [sd 3 0 832, sd 25 0 840,
    addi 15 0 64, addi 10 0 832, addi 11 0 64]) ++ [.mark (label+3)] ++
  emit [ForestCode.sw 15 0 844, slli 3 15 6, add 3 3 20,
    ld 14 3 0, sd 14 0 864, ld 14 3 8, sd 14 0 872,
    ld 14 3 32, sd 14 0 880, ld 14 3 40, sd 14 0 888,
    slli 12 15 5, add 12 12 20, hashInstruction, addi 15 15 1] ++
  [.branchTo 6 15 21 (label+3)] ++ emit [srli 21 21 1, srli 15 21 1] ++
  [.branchTo 1 15 0 (label+3)] ++
  emit ([ld 3 20 32, sd 3 0 288, ld 3 20 40, sd 3 0 296,
    addi 23 23 128] ++ li 24 (196608+signatureOffset lay+992) ++
    (List.range 7).flatMap (fun level =>
      [srli 3 23 level, opI 19 4 3 3 1, slli 3 3 5, add 3 3 20,
        ld 14 3 0, sd 14 24 (16*level), ld 14 3 8, sd 14 24 (8+16*level)]))

/-- The top layer computes only the selected initialPart, stopping after digit steps. -/
def prefixChain (source label : Nat) : List Item :=
  emit [ld 3 0 source, sd 3 0 304, ld 3 0 (source+8), sd 3 0 312,
    sd 27 0 256, andi 29 16 3, addi 14 0 0,
    addi 10 0 256, addi 12 0 304] ++
  [.branchTo 0 29 0 (label+1), .mark label] ++
  emit [sb 14 0 260, hashInstruction, addi 14 14 1] ++
  [.branchTo 6 14 29 label, .mark (label+1)] ++
  emit (capture ++ [addi 27 27 64, addi 24 24 16] ++ nextDigit)

def top : List Item :=
  emit ([addi 3 0 2, sd 3 0 192, sd 31 0 200,
      sd 0 0 272, sd 0 0 280, sd 0 0 288, sd 0 0 296] ++
    li 3 24576 ++ [ld 16 3 0, ld 17 3 8] ++
    li 24 199344 ++ li 27 5376 ++ [addi 18 0 0, addi 19 0 31]) ++
  [.mark 4000] ++
  emit [ForestCode.sw 18 0 196, addi 10 0 192, addi 11 0 64,
    addi 12 0 320, hashInstruction] ++
  prefixChain 320 4010 ++ prefixChain 336 4020 ++
  emit [addi 18 18 1] ++ [.branchTo 6 18 19 4000] ++
  emit (li 3 3330 ++ [sd 3 0 192, sd 0 0 200] ++
    li 3 4096 ++ [add 23 23 3] ++ li 20 32768 ++
    [addi 10 0 192, addi 12 0 320]) ++
  (List.range 12).flatMap (fun level => emit
    [srli 28 23 level, opI 19 4 28 28 1, ForestCode.sw 28 0 204,
      hashInstruction, slli 3 28 4, add 3 3 20,
      ld 14 3 0, ld 26 0 320, opR 4 14 14 26, sd 14 24 (16*level),
      ld 14 3 8, ld 26 0 328, opR 4 14 14 26, sd 14 24 (8+16*level)])

def program : List Item := SignFrontCode.program ++
  ([3,2,1] : List Nat).flatMap (fun lay => search lay ++ lower lay) ++
  search 0 ++ top ++ emit [addi 10 0 0, addi 5 0 1, hashInstruction]

def code : List Instruction := assemble program

def image : SigGolfCandidate.Legacy.Riscv.Image := ⟨code, LayerCode.maskData⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem image_room : image.byteSize < 2^20 := by
  simp only [image,SigGolfCandidate.Legacy.Riscv.Image.byteSize,code,
    Assembler.assemble_length,List.length_nil,Nat.add_zero,LayerCode.maskData_length]
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem assembly_wellFormed : Assembler.WellFormed program := by decide +kernel

end SignLayerCode

namespace ExpandCode
open ChainCode FrontCode Assembler

/-- Copy fixed public words. These loops access only the compact input and
output witness; their counts do not depend on untrusted input bytes. -/
def copyWords (source dest count label : Nat) : List Item :=
  emit (li 20 source ++ li 21 dest ++ li 22 count) ++ [.mark label] ++
  emit [ld 3 20 0, sd 3 21 0, addi 20 20 8, addi 21 21 8, addi 22 22 (-1)] ++
  [.branchTo 1 22 0 label]

/-- Restore compact chain values after recovery has mutated their in-place
buffers. Canonical header bytes are zero, independent of the last chain step. -/
def chains (lay label : Nat) (prepareWitness : Bool) : List Item :=
  emit (li 20 (196608+SignLayerCode.signatureOffset lay) ++
    li 21 (5376+3968*lay) ++ [addi 22 0 62]) ++ [.mark label] ++
  emit ([sd 0 21 0, sd 0 21 8] ++
    (if prepareWitness then [sd 0 21 16, sd 0 21 24, sd 0 21 32, sd 0 21 40] else []) ++
    [ld 3 20 0, sd 3 21 48, ld 3 20 8, sd 3 21 56,
      addi 20 20 16, addi 21 21 64, addi 22 22 (-1)]) ++
  [.branchTo 1 22 0 label]

def prepareWitness : List Item :=
  copyWords 196608 2048 342 10 ++
  (List.range 4).flatMap (fun lay =>
    copyWords (196608+SignLayerCode.signatureOffset lay+992)
      (2048+witnessPathOffset lay) (2*height lay) (20+lay) ++
    chains lay (30+lay) true) ++
  emit (li 3 5328 ++ (List.range 6).map fun i => sd 0 3 (8*i))

/-- The same chain and Merkle-fold dispatch tables as verification. Search is
unscored expansion work, and the found counters are serialized in the witness. -/
def layer (lay : Nat) : List Item :=
  SignLayerCode.search lay ++
  emit (li 3 4784 ++ [ForestCode.sw 26 3 (4*lay)] ++ LayerCode.setup ++
    li 27 (514+65536*lay) ++ li 22 (7360+3968*lay)) ++
  [.imageJump 1 4096] ++
  emit (LayerCode.leafStart lay ++ LayerFoldCode.dispatch lay 0 ++
    (if lay = 0 then LayerFoldCode.dispatch lay 1 else []))

def program : List Item :=
  [.jump 0 1, .mark 0] ++ emit [addi 10 0 1, addi 5 0 1, hashInstruction] ++
  [.mark 1] ++ prepareWitness ++ emit FrontCode.digestPrefix ++ [.branchTo 1 3 0 0] ++
  emit (FrontCode.forestSetup ++ (List.range 17).flatMap FrontCode.forestCall ++
    FrontCode.forestFinish) ++
  ([3,2,1,0] : List Nat).flatMap layer ++
  emit [ld 3 0 384, ld 14 0 160, opR 4 3 3 14,
    ld 24 0 392, ld 26 0 168, opR 4 24 24 26, bor 3 3 24] ++
  [.branchTo 0 3 0 40, .jump 0 0, .mark 40] ++
  (List.range 4).flatMap (fun lay => chains lay (50+lay) false) ++
  emit [addi 10 0 0, addi 5 0 1, hashInstruction]

def core : List Instruction := assemble program

def code : List Instruction :=
  let a := VerifyImage.place core 4096 VerifyImage.dispatches
  let b := VerifyImage.place a 65536 ChainCode.bodies
  let c := VerifyImage.place b 196608 ForestCode.shapes
  let d := VerifyImage.place c 524288 ChainCode.entries
  VerifyImage.place d 655360 LayerFoldCode.tables

def image : SigGolfCandidate.Legacy.Riscv.Image := ⟨code, LayerCode.maskData⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem core_room : core.length ≤ 1024 := by
  unfold core
  rw [Assembler.assemble_length]
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem image_bytes : image.byteSize = 786448 := by
  have hc := core_room
  simp only [image, SigGolfCandidate.Legacy.Riscv.Image.byteSize, code, VerifyImage.place,
    List.length_append, List.length_replicate, VerifyImage.dispatches_length,
    VerifyImage.bodies_length, VerifyImage.forest_length, VerifyImage.entries_length,
    VerifyImage.folds_length, LayerCode.maskData_length]
  norm_num only [Nat.reduceDiv]
  omega

theorem image_room : image.byteSize < 2^20 := by rw [image_bytes]; decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem assembly_wellFormed : Assembler.WellFormed program := by decide +kernel

end ExpandCode

end SigGolfCandidate.Base4Candidate.Reference


