import SigGolfCandidate.W9Machine.WctChainPieces
import SigGolfCandidate.W9Machine.WctJTData
import SigGolfCandidate.ClaudeWCT.WCT9.Basic

namespace W9Machine
open SigGolfCandidate.T3M
def expectedChainKinds (digits : List Nat) (t : Nat) : List ChainPieceKind :=
  let d := digits.getD t 0
  if d = 0 then [] else
    let off := 832 - 64 * t
    let slot := if t = 0 then 880 else 896 + 16 * t
    let own := 0 < t ∧ t < 6 ∧ digits.getD (t + 1) 0 = 0
    let dst := if own then off + 48 else slot
    [.head off (if d = 1 then dst else off + 48) t (3 - d)] ++
      ((List.range' (4 - d) (d - 1)).map fun step ↦
        .rung step (if step = 2 ∧ dst ≠ off + 48 then some dst else none)) ++
      (if own then [.copy off slot] else [])
def expectedKinds (digits : List Nat) : List ChainPieceKind :=
  (List.range 7).flatMap (expectedChainKinds digits) ++ [.leaf]
def ChainPiece.isHash (p : ChainPiece) : Bool :=
  match p.kind with
  | .head .. | .rung .. => true
  | _ => false
def ChainPiece.totalCycles (p : ChainPiece) : Nat :=
  p.result.cycles + if p.isHash then 8 else 0
def ChainPiece.nextPc (p : ChainPiece) : Nat :=
  match p.kind with
  | .jump target => target
  | _ => p.pc + p.words.length
structure ChainRoutine where
  rank : Nat
  digits : List Nat
  pieces : List ChainPiece
def ChainRoutine.cycles (r : ChainRoutine) : Nat := (r.pieces.map ChainPiece.totalCycles).sum
def ChainRoutine.fuel (r : ChainRoutine) : Nat := (r.pieces.map fun p ↦ p.words.length).sum
def ChainRoutine.checked (r : ChainRoutine) : Bool :=
  decide (r.rank < 728) &&
  (r.digits == (ClaudeWCT.WCT9.compositions 4 7 6).getD r.rank []) &&
  (r.pieces.head?.map ChainPiece.pc == some (chainEntries.getD r.rank 0)) &&
  (r.pieces.filterMap (fun p ↦ match p.kind with | .jump _ => none | k => some k)
    == expectedKinds r.digits) &&
  ((r.pieces.zip r.pieces.tail).all fun pq ↦ pq.2.pc == pq.1.nextPc) &&
  ((r.pieces.filter ChainPiece.isHash).length == 6) &&
  decide (r.cycles ≤ 84) && decide (r.fuel ≤ 47)
end W9Machine
