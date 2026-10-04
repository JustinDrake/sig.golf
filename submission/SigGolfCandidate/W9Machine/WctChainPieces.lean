import SigGolfCandidate.W9Machine.WctPackedRuns

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def leafSetupRel : Result :=
  ⟨⟨((RegFile.init.set .x25 (.ld (addC (.reg .x28) (-1592)))).set
      .x10 (addC (.reg .x8) 880)).set .x11 (.c 128),
    [(kAt .x8 880 24, .reg .x4),
      (kAt .x8 880 16, .ld (addC (.reg .x28) (-1592)))],
    [.valid (kAt .x8 880 24) 8, .valid (kAt .x8 880 16) 8,
      .valid ⟨some (.reg .x28), -1592⟩ 8]⟩,
    .bin .and (.reg .x23) (.c (~~~1#64)), .jump, 6, 6⟩
inductive ChainPieceKind where
  | head (off dst chain digit : Nat)
  | rung (digit : Nat) (dst : Option Nat)
  | copy (off dst : Nat)
  | jump (target : Nat)
  | leaf
  deriving BEq, DecidableEq, Repr
structure ChainPiece where
  pc : Nat
  words : List (BitVec 32)
  kind : ChainPieceKind
  deriving Repr
def ChainPiece.result (p : ChainPiece) : Result :=
  match p.kind with
  | .head off dst chain digit =>
      headRHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p.pc chain digit
  | .rung digit dst => rungRRel .x8 digit (dst.map (BitVec.ofNat 64)) p.pc
  | .copy off dst => copyFHRel .x8 (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p.pc
  | .jump target => ⟨SymState.init, .c (pcOf target), .jump, 1, 1⟩
  | .leaf => leafSetupRel
def ChainPiece.checked (p : ChainPiece) : Bool :=
  rOK (symRun {} p.words (pcOf p.pc) p.words.length) p.result
end W9Machine
