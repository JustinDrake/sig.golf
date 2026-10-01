import SigGolfCandidate.AlternativeCodecAlgorithms

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

/-! A first machine-code component for the alternate verifier. The block is
straight-line RV64IM, using x22 as the centered witness-layer base, x31 as header
word one, x6=1, x7=2, x11=64 and x5=0. It deliberately omits a zero step-byte
store after initializing the header from the physical address. A one-HASH chain
sets its final destination immediately, avoiding an intermediate output pointer.
The image-level refinement remains outstanding. -/
namespace ChainCode

abbrev Instruction := BitVec 32

def imm12 (n : Int) : Nat := (n % 4096).toNat

def opI (opcode funct rd rs : Nat) (imm : Int) : Instruction :=
  BitVec.ofNat 32 (opcode + 128*rd + 4096*funct + 32768*rs + 1048576*imm12 imm)

def opS (funct rs value : Nat) (imm : Int) : Instruction :=
  let n := imm12 imm
  BitVec.ofNat 32 (35 + 128*(n%32) + 4096*funct + 32768*rs +
    1048576*value + 33554432*(n/32))

def addi (rd rs : Nat) (imm : Int) : Instruction := opI 19 0 rd rs imm
def ld (rd rs : Nat) (imm : Int) : Instruction := opI 3 3 rd rs imm
def sd (value rs : Nat) (imm : Int) : Instruction := opS 3 rs value imm
def sb (value rs : Nat) (imm : Int) : Instruction := opS 0 rs value imm
def hashInstruction : Instruction := 115

def offset (i : Nat) : Int := 64*(i : Int)-1984
def leafSlot (i : Nat) : Nat := 864+16*i

def rung (i digit step : Nat) : List Instruction :=
  (if step = 0 then [] else [sb (if step = 1 then 6 else 7) 10 4]) ++
    (if step = 2 ∧ digit ≠ 2 then [addi 12 0 (leafSlot i)] else []) ++
    [hashInstruction]

def code (i : Nat) (digit : Fin 4) : List Instruction :=
  if digit.val = 3 then
    [ld 3 22 (offset i+48), ld 14 22 (offset i+56),
      sd 3 0 (leafSlot i), sd 14 0 (leafSlot i+8)]
  else
    [addi 10 22 (offset i),
      if digit.val = 2 then addi 12 0 (leafSlot i) else addi 12 10 48,
      sd 10 10 0, sd 31 10 8] ++
      (List.range' digit.val (3-digit.val)).flatMap (rung i digit.val)

/-- Length of the straight-line instruction list, before HASH surcharges. -/
def instructionCount (digit : Fin 4) : Nat := [10, 9, 6, 4].getD digit.val 0

def chargedCost (digit : Fin 4) : Nat := [31, 23, 13, 4].getD digit.val 0

theorem code_length (i : Nat) (digit : Fin 4) :
    (code i digit).length = instructionCount digit := by
  fin_cases digit <;> simp [code, rung, instructionCount, List.range'_succ]

theorem cost_arithmetic (digit : Fin 4) :
    instructionCount digit + 7*(3-digit.val) = chargedCost digit := by
  fin_cases digit <;> decide

theorem cost_affine (digit : Fin 4) :
    2*chargedCost digit + 19*digit.val ≤ 65 := by
  fin_cases digit <;> decide

/-- The instruction-template arithmetic bound for an entire accepted codeword.
This does not assert a RISC-V execution theorem for a complete verifier image. -/
theorem word_cost (x : Base4Candidate.Word) (hx : Base4Candidate.Valid x) :
    (∑ i, chargedCost (x i)) + 92 ≤ 1062 := by
  have h := Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset Base4Candidate.Index)) => cost_affine (x i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  change (∑ i, (x i).val) = 110 at hx
  omega

theorem input_immediates (i : Nat) (hi : i < 62) :
    -2048 ≤ offset i ∧ offset i+56 < 2048 := by unfold offset; omega

theorem output_immediates (i : Nat) (hi : i < 62) :
    leafSlot i+8 < 2048 := by unfold leafSlot; omega

/-! Quad dispatch layout. Entries are eight words, interleaved across sixteen
groups in each 512-byte row. The final group contains only two chains. The
first HASH executes inside its entry; the remaining first-chain rungs and the
other chains share code for the other three digits. -/
def jal (rd : Nat) (imm : Int) : Instruction :=
  let n := (imm % 2097152).toNat
  BitVec.ofNat 32 (111 + 128*rd + 2147483648*(n/1048576) +
    2097152*(n/2%1024) + 1048576*(n/2048%2) + 4096*(n/4096%256))

def nop : Instruction := addi 0 0 0

def digitOf (q position : Nat) : Fin 4 := ⟨q / 4^position % 4, Nat.mod_lt _ (by decide)⟩

def remainder (group q : Nat) : List Instruction :=
  code (4*group+1) (digitOf q 0) ++
    (if group = 15 then [] else
      code (4*group+2) (digitOf q 1) ++ code (4*group+3) (digitOf q 2))

def caseWords (group q : Nat) : Nat := 6 + (remainder group q).length

def caseOffset (group q : Nat) : Nat :=
  ((List.range q).map (caseWords group)).sum

def dispatchPc (group : Nat) : Nat := 4096 + 32*group

def bodyPc (group q : Nat) : Nat := 65536 + 7104*group + 4*caseOffset group q

def tablePc (group row : Nat) : Nat := 524288 + 512*row + 32*group

def firstLength (digit : Fin 4) : Nat := [5,6,6,4].getD digit.val 0

def entry (group row : Nat) : List Instruction :=
  let d := digitOf row 0
  let q := if group = 15 then row/4%4 else row/4
  let initialPart := (code (4*group) d).take (firstLength d)
  let target := bodyPc group q + 4*(if d.val = 0 then 0 else if d.val = 1 then 2 else 5)
  initialPart ++ [jal 0 ((target : Int) - (tablePc group row + 4*initialPart.length : Nat))] ++
    List.replicate (7-initialPart.length) nop

def body (group q : Nat) : List Instruction :=
  let rest := remainder group q
  [sb 6 10 4, hashInstruction, sb 7 10 4, addi 12 0 (leafSlot (4*group)), hashInstruction] ++
    rest ++ [if group = 15 then opI 103 0 0 1 0 else
      jal 0 ((dispatchPc (group+1) : Int) - (bodyPc group q + 4*(5+rest.length) : Nat))]

/-- x28 holds 255 shifted left nine; x29 holds 4096+524288+2048 (code load base plus table bias). -/
def dispatch (group : Nat) : List Instruction :=
  let shift := 8*(group%8)
  let source := if group < 8 then 16 else 17
  [if shift < 9 then opI 19 1 14 source (9-shift) else opI 19 5 14 source (shift-9),
    BitVec.ofNat 32 (51+128*14+4096*7+32768*14+1048576*28),
    BitVec.ofNat 32 (51+128*14+32768*14+1048576*29),
    opI 103 0 0 14 (32*(group : Int)-2048)]

def bodies : List Instruction :=
  (List.range 16).flatMap fun group =>
    (List.range (if group = 15 then 4 else 64)).flatMap (body group)

def entries : List Instruction :=
  (List.range 256).flatMap fun row => (List.range 16).flatMap fun group => entry group row

theorem first_length_le (digit : Fin 4) : firstLength digit ≤ instructionCount digit := by
  fin_cases digit <;> decide

theorem entry_length (group row : Nat) : (entry group row).length = 8 := by
  have hc := code_length (4*group) (digitOf row 0)
  have hl := first_length_le (digitOf row 0)
  have hm : firstLength (digitOf row 0) ≤ 7 := by
    generalize digitOf row 0 = d
    fin_cases d <;> decide
  simp only [entry, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, List.length_take, hc, Nat.min_eq_left hl]
  omega

theorem body_length (group q : Nat) : (body group q).length = caseWords group q := by
  simp only [body, caseWords, List.length_append, List.length_cons, List.length_nil]
  omega

theorem dispatch_length (group : Nat) : (dispatch group).length = 4 := by simp [dispatch]

theorem remainder_length (group q : Nat) :
    (remainder group q).length = instructionCount (digitOf q 0) +
      (if group = 15 then 0 else instructionCount (digitOf q 1) + instructionCount (digitOf q 2)) := by
  by_cases h : group = 15 <;> simp [remainder, h, code_length]

theorem group_words (group : Nat) (hg : group < 15) :
    ((List.range 64).map (caseWords group)).sum = 1776 := by
  have hn : group ≠ 15 := by omega
  have hf : caseWords group = fun q => 6 + instructionCount (digitOf q 0) +
      (instructionCount (digitOf q 1) + instructionCount (digitOf q 2)) := by
    funext q
    simp only [caseWords, remainder_length, if_neg hn]
    omega
  rw [hf]
  decide

theorem tail_words : ((List.range 4).map (caseWords 15)).sum = 53 := by
  have hf : caseWords 15 = fun q => 6 + instructionCount (digitOf q 0) := by
    funext q
    simp [caseWords, remainder_length]
  rw [hf]
  decide

/-! The reserved code intervals do not overlap: residual bodies fit below the
forest shapes at 0x30000, the 128 KiB entry table occupies 0x80000..0xa0000,
and the upper Merkle shapes have 256 KiB reserved at 0xa0000..0xe0000. These
are layout arithmetic facts, not a certificate for an assembled image. -/
theorem layout_arithmetic :
    65536 + 15*7104 + 4*53 < 196608 ∧
    196608 + 262144 ≤ 524288 ∧
    524288 + 256*16*8*4 = 655360 ∧
    655360 + 262144 < 1048576 := by decide

end ChainCode

/-! FORS fold shape component. A shared 512-entry shape table handles every
tree. x22 points to its disclosed secret, x30 to its root slot, x9 holds tag 10,
x6/x7/x8 hold 1/2/3, and a0/a1 are 832/64. The caller builds the leaf input
and sets the return address. All sibling displacements are at most 152 bytes. -/
namespace ForestCode
open ChainCode

def sw (value rs : Nat) (imm : Int) : Instruction := opS 2 rs value imm

def parent (leaf level : Nat) : Nat := (512+leaf) / 2^(level+1)

def parentRegister (index : Nat) : Nat :=
  if index = 1 then 6 else if index = 2 then 7 else if index = 3 then 8 else 3

def parentCode (index : Nat) : List Instruction :=
  (if index < 4 then [] else [addi 3 0 index]) ++ [sw (parentRegister index) 0 844]

def levelCode (leaf level : Nat) : List Instruction :=
  let side := leaf / 2^level % 2
  [addi 12 0 (864+16*side), hashInstruction] ++
    (if level = 0 then [sb 9 0 833] else []) ++
    parentCode (parent leaf level) ++
    [ld 3 22 (16+16*level), ld 14 22 (24+16*level),
      sd 3 0 (880-16*side), sd 14 0 (888-16*side)]

def code (leaf : Nat) : List Instruction :=
  (List.range 9).flatMap (levelCode leaf) ++
    [addi 12 30 0, hashInstruction, opI 103 0 0 1 0]

def shape (leaf : Nat) : List Instruction :=
  code leaf ++ List.replicate (128-(code leaf).length) nop

def shapes : List Instruction := (List.range 512).flatMap shape

theorem level_length (leaf level : Nat) :
    (levelCode leaf level).length =
      7 + (if level = 0 then 1 else 0) + (if parent leaf level < 4 then 0 else 1) := by
  by_cases hz : level = 0
  · subst level
    by_cases hp : parent leaf 0 < 4 <;> simp [levelCode, parentCode, hp]
  · by_cases hp : parent leaf level < 4 <;> simp [levelCode, parentCode, hz, hp]

theorem level_length_le (leaf level : Nat) :
    (levelCode leaf level).length ≤ 8 + (if level = 0 then 1 else 0) := by
  rw [level_length]
  split_ifs <;> omega

theorem upper_parent (leaf : Nat) (hl : leaf < 512) :
    parent leaf 7 < 4 ∧ parent leaf 8 < 4 := by
  norm_num [parent]
  omega

theorem code_length_le (leaf : Nat) (hl : leaf < 512) : (code leaf).length ≤ 74 := by
  have h0 := level_length_le leaf 0
  have h1 := level_length_le leaf 1
  have h2 := level_length_le leaf 2
  have h3 := level_length_le leaf 3
  have h4 := level_length_le leaf 4
  have h5 := level_length_le leaf 5
  have h6 := level_length_le leaf 6
  have h7 : (levelCode leaf 7).length = 7 := by
    rw [level_length, if_neg (by decide), if_pos (upper_parent leaf hl).1]
  have h8 : (levelCode leaf 8).length = 7 := by
    rw [level_length, if_neg (by decide), if_pos (upper_parent leaf hl).2]
  norm_num only [code, List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    List.length_cons, List.length_nil] at ⊢
  norm_num at h0 h1 h2 h3 h4 h5 h6
  omega

theorem shape_length (leaf : Nat) (hl : leaf < 512) : (shape leaf).length = 128 := by
  have h := code_length_le leaf hl
  simp only [shape, List.length_append, List.length_replicate]
  omega

/-- Structural cost arithmetic: at most 74 instructions including ten HASHes,
whose seven extra cycles give a 144-cycle bound for this proposed component. -/
theorem charged_arithmetic : 74+7*10 = 144 := by decide

end ForestCode

/-! The verifier front end uses an aligned one-block message digest:
16-byte domain header, 16-byte randomizer, 32-byte message. It then calls the
shared forest shapes, with no per-level conditional branches. The resulting
forest root is written at address 288 for the first OTS encoding query. -/
namespace FrontCode
open ChainCode

def opR (funct rd left right : Nat) : Instruction :=
  BitVec.ofNat 32 (51+128*rd+4096*funct+32768*left+1048576*right)

def add (rd left right : Nat) : Instruction := opR 0 rd left right
def bor (rd left right : Nat) : Instruction := opR 6 rd left right

def slli (rd rs shift : Nat) : Instruction := opI 19 1 rd rs shift
def srli (rd rs shift : Nat) : Instruction := opI 19 5 rd rs shift
def andi (rd rs : Nat) (mask : Int) : Instruction := opI 19 7 rd rs mask

def li (rd value : Nat) : List Instruction :=
  if value < 2048 then [addi rd 0 value] else
    [BitVec.ofNat 32 (55+128*rd+4096*((value+2048)/4096)),
      addi rd rd ((value : Int)-4096*((value+2048)/4096 : Nat))]

def branch (funct left right : Nat) (imm : Int) : Instruction :=
  let n := (imm % 8192).toNat
  BitVec.ofNat 32 (99+128*(n/2048%2)+256*(n/2%16)+4096*funct+
    32768*left+1048576*right+33554432*(n/32%64)+2147483648*(n/4096))

def digestPrefix : List Instruction :=
  li 22 2048 ++ li 3 3074 ++ [sd 3 0 0] ++
    ((List.range 2).flatMap fun i => [ld 3 22 (8*i), sd 3 0 (16+8*i)]) ++
    ((List.range 4).flatMap fun i => [ld 3 0 (64+8*i), sd 3 0 (32+8*i)]) ++
    [addi 11 0 64, hashInstruction] ++
    ((List.range 4).map fun i => ld (16+i) 0 (8*i)) ++
    [srli 3 18 58, andi 14 19 63, bor 3 3 14]

def forestSetup : List Instruction :=
  [slli 25 16 31, srli 25 25 31, srli 26 25 32, slli 26 26 24] ++
    li 3 2818 ++
    [add 3 3 26, sd 3 0 512, addi 27 3 (-512),
      slli 31 25 32, srli 31 31 32, sd 31 0 520, sd 31 0 840] ++
    li 28 65536 ++ li 29 200704 ++
    [addi 30 0 544, addi 22 22 16, addi 10 0 832,
      addi 6 0 1, addi 7 0 2, addi 8 0 3, addi 9 0 10]

def indexCode (tree : Nat) : List Instruction :=
  let offset := 33+9*tree
  let r := 16+offset/64
  let shift := offset%64
  [srli 23 r shift] ++
    (if shift+9 ≤ 64 then [] else [slli 14 (r+1) (64-shift), bor 23 23 14]) ++
    [andi 23 23 511]

def forestCall (tree : Nat) : List Instruction :=
  indexCode tree ++
    [sd 27 0 832, ForestCode.sw 23 0 844, sd 0 0 880, sd 0 0 888,
      ld 3 22 0, ld 14 22 8, sd 3 0 864, sd 14 0 872,
      slli 3 23 9, add 3 3 29, opI 103 0 1 3 0] ++
    (if tree = 16 then [] else [addi 22 22 160, addi 30 30 16, add 27 27 28])

def forestFinish : List Instruction :=
  [sd 0 0 816, sd 0 0 824, addi 10 0 512, addi 11 0 320,
    addi 12 0 288, hashInstruction]

/-- Program entry, a rejection stub at byte four, the digest check and forest.
Successful execution falls through to the yet-to-be-assembled layer callers. -/
def code : List Instruction :=
  [jal 0 16, addi 10 0 1, addi 5 0 1, hashInstruction] ++ digestPrefix ++
    [branch 1 3 0 (4-(16+4*digestPrefix.length : Nat) : Int)] ++ forestSetup ++
    (List.range 17).flatMap forestCall ++ forestFinish

/-- The digest layout and its cost remain exactly one compression. -/
theorem digest_layout : 16+16+32 = 64 := by decide

end FrontCode

/-! Layer-side SWAR decoder and chain caller components. Two 64-bit masks
are intended as the image's sixteen embedded data bytes. Their address is
0xfffff0 under the pinned 16 MiB memory layout. The arithmetic keeps the two
encoding words intact for quad dispatch. -/
namespace LayerCode
open ChainCode FrontCode

def band (rd left right : Nat) : Instruction := opR 7 rd left right

def remu (rd left right : Nat) : Instruction :=
  BitVec.ofNat 32 (51+128*rd+4096*7+32768*left+1048576*right+33554432)

/-- x18=0x3333333333333333, x19=0x0f0f0f0f0f0f0f0f, x20=255. -/
def digitSum : List Instruction :=
  [srli 3 16 2, band 3 3 18, band 24 16 18, add 24 24 3,
    srli 3 17 2, band 3 3 18, band 14 17 18, add 14 14 3,
    add 24 24 14, srli 3 24 4, band 3 3 19, band 24 24 19,
    add 24 24 3, remu 24 24 20]

def setup : List Instruction :=
  li 3 16777200 ++ [ld 18 3 0, ld 19 3 8] ++
    li 2 4096 ++ li 28 130560 ++ li 29 530432 ++
    [addi 20 0 255, addi 21 0 110]

/-- Leaf selection precedes the sentinel used by the Merkle-fold code. -/
def routeCode (lay : Nat) : List Instruction :=
  (if lay = 0 then [addi 23 25 0, addi 25 0 0] else
    [andi 23 25 127, srli 25 25 7]) ++
    [slli 31 23 32, bor 31 31 25]

/-- Counter load and message-root payload already have fixed locations. -/
def beforeCounterCheck (lay : Nat) : List Instruction :=
  routeCode lay ++ li 27 (514+65536*lay) ++
    [addi 3 27 512, sd 3 0 256, sd 31 0 264,
      opI 3 6 3 2 (688+4*lay), srli 14 3 22]

def encodingHash : List Instruction :=
  [sd 3 0 304, sd 0 0 312, addi 10 0 256, addi 11 0 64, addi 12 0 320,
    hashInstruction, ld 16 0 320, ld 17 0 328, srli 3 17 60]

/-- Emit checks with branch displacements derived from their actual positions.
The main-program callers must remain within branch reach of the rejection stub. -/
def caller (lay pc : Nat) : List Instruction :=
  let a := beforeCounterCheck lay
  let b := encodingHash
  a ++ [branch 1 14 0 ((4 : Int)-(pc+4*a.length : Nat))] ++
    b ++ [branch 1 3 0 ((4 : Int)-(pc+4*(a.length+1+b.length) : Nat))] ++
    digitSum ++
    [branch 1 24 21 ((4 : Int)-(pc+4*(a.length+1+b.length+1+digitSum.length) : Nat))] ++
    li 22 (7360+3968*lay) ++
    [jal 1 ((dispatchPc 0 : Int)-(pc+4*(a.length+1+b.length+1+digitSum.length+1+
      (li 22 (7360+3968*lay)).length) : Nat))]

/-- Chain code preserves the selected leaf and the two canonical header words. -/
def leafStart (lay : Nat) : List Instruction :=
  [sd 27 0 832, sd 31 0 840, addi 10 0 832, addi 11 0 1024] ++
    (if lay = 0 then [add 23 23 2] else [opI 19 6 23 23 128])

/-- Embedded data bytes, little-endian, for the two SWAR masks. -/
def maskData : List Byte := List.replicate 8 (byte 51) ++ List.replicate 8 (byte 15)

theorem maskData_length : maskData.length = 16 := by simp [maskData]
theorem digitSum_length : digitSum.length = 14 := by rfl

end LayerCode

namespace LayerFoldCode
open ChainCode FrontCode

def firstChunk (lay chunk : Nat) : Bool := lay != 0 || chunk == 0
def lastChunk (lay chunk : Nat) : Bool := lay != 0 || chunk == 1
def bits (lay : Nat) : Nat := if lay = 0 then 6 else 7

def shapeBase (lay chunk : Nat) : Nat :=
  if lay = 0 then 753664+16384*chunk else 655360+32768*(3-lay)

def parentCode (lay chunk value level : Nat) : List Instruction :=
  if lay = 0 ∧ chunk = 0 then
    [srli 3 23 (level+1), ForestCode.sw 3 0 844]
  else ForestCode.parentCode ((2^(bits lay)+value)/2^(level+1))

def levelCode (lay chunk value level : Nat) : List Instruction :=
  let side := value/2^level%2
  let off := 2048+witnessPathOffset lay+16*(6*chunk+level)-4096
  [addi 12 0 (864+16*side), hashInstruction] ++
    (if firstChunk lay chunk && level == 0 then [sb 8 0 833, addi 11 0 64] else []) ++
    parentCode lay chunk value level ++
    [ld 3 2 off, ld 14 2 (off+8), sd 3 0 (880-16*side), sd 14 0 (888-16*side)]

def code (lay chunk value : Nat) : List Instruction :=
  (List.range (bits lay)).flatMap (levelCode lay chunk value) ++
    (if lastChunk lay chunk then
      [addi 12 0 (if lay = 0 then 384 else 288), hashInstruction] else []) ++
    [opI 103 0 0 1 0]

def shape (lay chunk value : Nat) : List Instruction :=
  code lay chunk value ++ List.replicate (64-(code lay chunk value).length) nop

def table (lay chunk : Nat) : List Instruction :=
  (List.range (2^(bits lay))).flatMap (shape lay chunk)

def tables : List Instruction :=
  table 3 0 ++ table 2 0 ++ table 1 0 ++ table 0 0 ++ table 0 1

def dispatch (lay chunk : Nat) : List Instruction :=
  if lay = 0 then
    (if chunk = 0 then [andi 3 23 63] else [srli 3 23 6, andi 3 3 63]) ++
      [slli 3 3 8] ++ li 26 (4096+shapeBase lay chunk) ++ [add 3 3 26, opI 103 0 1 3 0]
  else li 26 (4096+shapeBase lay chunk-32768) ++
    [slli 3 23 8, add 3 3 26, opI 103 0 1 3 0]

end LayerFoldCode

theorem flatMap_length_constant {α β : Type} (xs : List α) (f : α → List β)
    (n : Nat) (h : ∀ x ∈ xs, (f x).length = n) :
    (xs.flatMap f).length = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,hx,ht]
    omega

namespace LayerFoldCode

theorem parentCode_length_le (lay chunk value level : Nat) :
    (parentCode lay chunk value level).length ≤ 2 := by
  unfold parentCode ForestCode.parentCode
  split_ifs <;> simp

theorem levelCode_length_le (lay chunk value level : Nat) :
    (levelCode lay chunk value level).length ≤ 8 + (if level = 0 then 2 else 0) := by
  have hp := parentCode_length_le lay chunk value level
  have hb : (if firstChunk lay chunk && level == 0 then 2 else 0 : Nat) ≤
      (if level = 0 then 2 else 0) := by
    by_cases h : level = 0
    · subst level; simp only [if_pos rfl]; split_ifs <;> omega
    · simp [h]
  simp only [levelCode, List.length_append, List.length_cons, List.length_nil]
  split_ifs at * <;> omega

theorem levels_length_le (lay chunk value n : Nat) :
    ((List.range n).flatMap (levelCode lay chunk value)).length ≤ 8*n+2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := levelCode_length_le lay chunk value n
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
    by_cases hz : n = 0
    · subst n
      simpa using h
    · simp only [if_neg hz] at h
      omega

theorem code_length_le (lay chunk value : Nat) : (code lay chunk value).length ≤ 64 := by
  have h := levels_length_le lay chunk value (bits lay)
  have hb : bits lay ≤ 7 := by unfold bits; split_ifs <;> omega
  simp only [code,List.length_append,List.length_cons,List.length_nil]
  split_ifs <;> omega

theorem shape_length (lay chunk value : Nat) : (shape lay chunk value).length = 64 := by
  have h := code_length_le lay chunk value
  simp only [shape,List.length_append,List.length_replicate]
  omega

theorem table_length (lay chunk : Nat) : (table lay chunk).length = 2^(bits lay)*64 := by
  unfold table
  rw [flatMap_length_constant _ _ 64 (fun _ _ => shape_length _ _ _),List.length_range]

/-- Template charge only: first chunks hash the 1024-byte OTS payload before
switching to 64-byte node inputs. The execution theorem must establish that
these are the actual HASH arguments and that padding is never executed. -/
def templateCharge (lay chunk value : Nat) : Nat :=
  (code lay chunk value).length +
    7 * (bits lay + (if lastChunk lay chunk then 1 else 0)) +
    (if firstChunk lay chunk then 120 else 0)

theorem lower_template_charge (lay value : Nat) (hl : lay ≠ 0) :
    templateCharge lay 0 value ≤ 240 := by
  have h := code_length_le lay 0 value
  simp only [templateCharge,bits,if_neg hl]
  simp [lastChunk,firstChunk,hl]
  omega

theorem top_first_template_charge (value : Nat) :
    templateCharge 0 0 value ≤ 226 := by
  have h := code_length_le 0 0 value
  simp only [templateCharge,bits,firstChunk,lastChunk]
  norm_num at ⊢
  omega

theorem top_last_template_charge (value : Nat) :
    templateCharge 0 1 value ≤ 113 := by
  have h := code_length_le 0 1 value
  simp only [templateCharge,bits,firstChunk,lastChunk]
  norm_num at ⊢
  omega

end LayerFoldCode

end SigGolfCandidate.Base4Candidate.Reference
