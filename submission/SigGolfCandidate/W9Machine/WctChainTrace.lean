import SigGolfCandidate.W9Machine.WctRoutineModel

namespace W9Machine
inductive ChainWord where
  | original (offset : Nat)
  | header (chain step : Nat)
  | route
  | answer (query word : Nat)
  | leafHeader
  deriving BEq, DecidableEq, Repr
structure ChainTrace where
  mem : List (Nat × ChainWord) := []
  input : Nat := 0
  output : Nat := 0
  chain : Nat := 0
  queries : List (List ChainWord) := []
  valid : Bool := true
  deriving Repr
def ChainTrace.read (s : ChainTrace) (off : Nat) : ChainWord :=
  ((s.mem.find? fun p => p.1 == off).map Prod.snd).getD (.original off)
def ChainTrace.put (s : ChainTrace) (off : Nat) (v : ChainWord) : ChainTrace :=
  { s with mem := (off, v) :: s.mem }
def ChainTrace.hash (s : ChainTrace) : ChainTrace :=
  let q := s.queries.length
  let input := (List.range 8).map fun i => s.read (s.input + 8 * i)
  let s := { s with queries := s.queries ++ [input] }
  (List.range 4).foldl (fun s i => s.put (s.output + 8 * i) (.answer q i)) s
def ChainTrace.step (s : ChainTrace) : ChainPieceKind → ChainTrace
  | .head off dst chain digit =>
      let s := (s.put (off + 16) (.header chain digit)).put (off + 24) .route
      ({ s with input := off, output := dst, chain := chain }).hash
  | .rung digit dst =>
      let headerOk := match s.read (s.input + 16) with
        | .header chain _ => chain == s.chain
        | _ => false
      let s := s.put (s.input + 16) (.header s.chain digit)
      ({ s with output := dst.getD s.output, valid := s.valid && headerOk }).hash
  | .copy off dst =>
      let lo := s.read (off + 48)
      let hi := s.read (off + 56)
      (s.put dst lo).put (dst + 8) hi
  | .jump _ => s
  | .leaf => ((s.put 896 .leafHeader).put 904 .route)
def chainTrace (r : ChainRoutine) : ChainTrace :=
  r.pieces.foldl (fun s p => s.step p.kind) {}
def traceLeafSlot (t : Nat) : Nat := if t = 0 then 880 else 896 + 16 * t
def chainQueryWords (digits : List Nat) (t j : Nat) : List ChainWord :=
  let off := 832 - 64 * t
  let q := (digits.take t).sum + j
  [.original off, .original (off + 8), .header t (3 - digits.getD t 0 + j), .route,
    .original (off + 32), .original (off + 40),
    if j = 0 then .original (off + 48) else .answer (q - 1) 0,
    if j = 0 then .original (off + 56) else .answer (q - 1) 1]
def expectedQueries (digits : List Nat) : List (List ChainWord) :=
  (List.range 7).flatMap fun t => (List.range (digits.getD t 0)).map (chainQueryWords digits t)
def expectedEndpoint (digits : List Nat) (t word : Nat) : ChainWord :=
  if digits.getD t 0 = 0 then .original (traceLeafSlot t + 8 * word)
  else .answer ((digits.take (t + 1)).sum - 1) word
def ChainRoutine.traceChecked (r : ChainRoutine) : Bool :=
  let s := chainTrace r
  s.valid && (s.queries == expectedQueries r.digits) &&
    ((List.range 7).all fun t => (List.range 2).all fun word =>
      s.read (traceLeafSlot t + 8 * word) == expectedEndpoint r.digits t word) &&
    (s.read 896 == .leafHeader) && (s.read 904 == .route) &&
    (s.mem.all fun p => decide (p.1 % 8 = 0 ∧ p.1 + 8 ≤ 1024))
end W9Machine
