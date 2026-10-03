import SigGolfCandidate.T3M.Verify.Digest

/-!
# Selections: expected symbolic results of the sort-tree paths (T3M verify words 15 .. 358)

After the digest, `ld a6/a7/s11/t3` load the four words of `N` and `s6 = N mod 2^31` (`selSetup`). For each
coordinate `c` (code from `selStart c` to the join `selJoin c`): the 25-bit number `gp = N >> (31 + 25 c)` (one
`srli`, or `srli; slli; or` when it straddles a word), `tp = ((gp & 15) << 10) + sp`, the three table
addresses `x_j = (gp >> (1 + 7 j)) & 1016 + tp = TAB + 8 (128 bucket + leaf_j)` (`xE c j`, t3-rl2), then a decision tree: at most three `bgeu`, the stores of
the sorted triple at `ETAB + 24 c + 8 k` (F5: the leaves' header words at `selT8 c k`), and `beq` rejects on the non-strict edges of the path.

Paths `p < 6` (`selDirs`, `selBrs`, `selPerm`) accept with the sorted order `selPerm p`; reject paths `r < 6`
(`selRDirs`, `selRBrs`) end at HALT(1). All 84 runs are checked in `SelCheck`.
-/

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- The 21 sorted heap indices `E = 2048 + 256 bucket + x` (8 bytes each). -/
def ETAB : Nat := 0x140

/-- Registers of the four words of `N`: `a6, a7, s11, t3`. -/
def nReg : Nat → Reg
  | 0 => .x16
  | 1 => .x17
  | 2 => .x27
  | _ => .x28

def selBit (c : Nat) : Nat := 31 + 25 * c

/-- Does coordinate `c`'s 25-bit number straddle two words? -/
def selDbl (c : Nat) : Bool := decide (64 < selBit c % 64 + 25)

/-- `gp`: the 25-bit number of coordinate `c` (in its low bits). -/
def gpE (c : Nat) : E :=
  let w := selBit c / 64
  let o := selBit c % 64
  if selDbl c then .bin .or (.bin .srl (.reg (nReg w)) (cw o)) (.bin .sll (.reg (nReg (w + 1))) (cw (64 - o)))
  else .bin .srl (.reg (nReg w)) (cw o)

/-- t3-rl2: `(gp & 15) << 10` (`tp = this + sp`, `sp = TAB` the header table). -/
def bbE (c : Nat) : E := .bin .sll (.bin .and (gpE c) (cw 15)) (cw 10)

/-- t3-rl2: the table address `TAB + 8 (128 bucket + x_j)` of the `j`-th unsorted leaf, as the executor folds
`x_j + (bb + sp)` (`mkAdd` reassociates the constant `sp`). -/
def xE (c j : Nat) : E :=
  .bin .add (.bin .add (.bin .and (.bin .srl (gpE c) (cw (1 + 7 * j))) (cw 1016)) (bbE c)) (.c (BitVec.ofNat 64 TAB))

/-- Start of coordinate `c`'s selection code (`selStart 7 = 380 = fts_setup`; F5: three header loads per coordinate). -/
def selStart (c : Nat) : Nat := [21, 74, 126, 176, 228, 278, 328, 380].getD c 0
def selJoin (c : Nat) : Nat := selStart (c + 1)

/-- Extraction length (1 or 3 instructions). -/
def selExt (c : Nat) : Nat := if selDbl c then 3 else 1

def geuB (c i j : Nat) (d : Bool) : Br := ⟨.geu, xE c i, xE c j, d⟩
def eqB (c i j : Nat) (d : Bool) : Br := ⟨.eq, xE c i, xE c j, d⟩

/-- The sorted order of accepting path `p`. -/
def selPerm : Nat → List Nat
  | 0 => [0, 1, 2]
  | 1 => [0, 2, 1]
  | 2 => [2, 0, 1]
  | 3 => [1, 0, 2]
  | 4 => [1, 2, 0]
  | _ => [2, 1, 0]

def selDirs : Nat → List Dir
  | 0 => [.br false, .br false]
  | 1 => [.br false, .br true, .br false, .br false]
  | 2 => [.br false, .br true, .br true, .br false]
  | 3 => [.br true, .br false, .br false, .br false]
  | 4 => [.br true, .br false, .br true, .br false]
  | _ => [.br true, .br true, .br false, .br false]

/-- The branch outcomes of accepting path `p`, newest first. -/
def selBrs (c : Nat) : Nat → List Br
  | 0 => [geuB c 1 2 false, geuB c 0 1 false]
  | 1 => [eqB c 2 1 false, geuB c 0 2 false, geuB c 1 2 true, geuB c 0 1 false]
  | 2 => [eqB c 2 0 false, geuB c 0 2 true, geuB c 1 2 true, geuB c 0 1 false]
  | 3 => [eqB c 1 0 false, geuB c 0 2 false, geuB c 1 2 false, geuB c 0 1 true]
  | 4 => [eqB c 2 0 false, geuB c 0 2 true, geuB c 1 2 false, geuB c 0 1 true]
  | _ => [eqB c 1 0 false, eqB c 2 1 false, geuB c 1 2 true, geuB c 0 1 true]

/-- F2: the table address `x_j + 16` of unsorted leaf `j` (the table follows the 16-byte initial-constant prefix at
`sp = TAB`), as the executor folds the offset of the load `ld r, 16(x_j)` into `xE`'s constant. -/
def xT (c j : Nat) : E := addC (xE c j) 16#64

/-- F5: the header-table address of unsorted leaf `j`, as the executor normalizes the load `ld r, 16(x_j)`. -/
def xA (c j : Nat) : Addr := norm (xT c j)

/-- F5: the header word 1 of leaf slot `3 c + k`, at word `+24` of its leaf block (`leafT + 8`). -/
def selT8 (c k : Nat) : Nat := WIT + 64 + 48 * (3 * c + k) + 24

/-- F5: the three table reads (`ld ra/s7/s9, 16(x_j)`), newest first. -/
def selObl (c : Nat) : List Oblig := [.valid (xA c 2) 8, .valid (xA c 1) 8, .valid (xA c 0) 8]

/-- F5: the slots coordinate `c` writes. -/
def selAllow (c : Nat) : List Nat := [selT8 c 0, selT8 c 1, selT8 c 2]

/-- Sort-tree cost of path `p` (bgeu, beq, three `sd`, the jump to the join). -/
def selTree : Nat → Nat
  | 0 => 6
  | 5 => 7
  | _ => 8

def selMem (c p : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (selT8 c 2)⟩, .ld (xT c ((selPerm p).getD 2 0))),
    (⟨none, BitVec.ofNat 64 (selT8 c 1)⟩, .ld (xT c ((selPerm p).getD 1 0))),
    (⟨none, BitVec.ofNat 64 (selT8 c 0)⟩, .ld (xT c ((selPerm p).getD 0 0)))]

def selSpec (c p : Nat) : Spec :=
  ⟨[], selMem c p, selJoin c, false, selExt c + 15 + selTree p, selBrs c p, none, selExt c + 15 + selTree p⟩

/-- The constant registers of the selection code: `baseK` and `sp = TAB`. -/
def selK : List (Reg × Word) := baseK ++ [(.x2, BitVec.ofNat 64 TAB)]

/-- Registers kept through a coordinate: the four words of `N`, `s6 = index`. -/
def selKeep : List Reg := [.x16, .x17, .x27, .x28, .x22]

def selCheck1 (c p : Nat) : Bool :=
  specB (selAllow c) [] baseK (runAt selK [selJoin c] (selStart c) (selDirs p)) (selSpec c p) (selObl c) selK selKeep

/-! ## Reject paths -/

def selRDirs : Nat → List Dir
  | 0 => [.br false, .br true, .br false, .br true]
  | 1 => [.br false, .br true, .br true, .br true]
  | 2 => [.br true, .br false, .br false, .br true]
  | 3 => [.br true, .br false, .br true, .br true]
  | 4 => [.br true, .br true, .br true]
  | _ => [.br true, .br true, .br false, .br true]

def selRBrs (c : Nat) : Nat → List Br
  | 0 => [eqB c 2 1 true, geuB c 0 2 false, geuB c 1 2 true, geuB c 0 1 false]
  | 1 => [eqB c 2 0 true, geuB c 0 2 true, geuB c 1 2 true, geuB c 0 1 false]
  | 2 => [eqB c 1 0 true, geuB c 0 2 false, geuB c 1 2 false, geuB c 0 1 true]
  | 3 => [eqB c 2 0 true, geuB c 0 2 true, geuB c 1 2 false, geuB c 0 1 true]
  | 4 => [eqB c 2 1 true, geuB c 1 2 true, geuB c 0 1 true]
  | _ => [eqB c 1 0 true, eqB c 2 1 false, geuB c 1 2 true, geuB c 0 1 true]

def selRSteps (c r : Nat) : Nat := selExt c + 15 + (if r = 4 then 6 else 7)

def selRCheck1 (c r : Nat) : Bool :=
  specB [] [] [] (runAt selK [] (selStart c) (selRDirs r)) (rejSpec (selRSteps c r) (selRBrs c r)) (selObl c) [] []

/-! ## The setup block (words 15 .. 20) -/

def nE (k : Nat) : E := .ld (cw (0x60 + 8 * k))
def idxE : E := .bin .srl (.bin .sll (nE 0) (cw 33)) (cw 33)

def setupSpec : Spec :=
  ⟨[(.x16, nE 0), (.x17, nE 1), (.x27, nE 2), (.x28, nE 3), (.x22, idxE)], [], 21, false, 6, [], none, 6⟩

def setupCheck : Bool := specB [] [] baseK (runAt selK [21] 15 []) setupSpec [] selK []

end SigGolfCandidate.T3M.Verify
