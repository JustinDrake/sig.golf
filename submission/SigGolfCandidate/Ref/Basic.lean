import SigGolfCandidate.Legacy
import Mathlib.Data.List.Sort

section

namespace SigGolfCandidate
def CACHE_BYTES : Nat := 2 ^ 17
abbrev Cache := SigGolfCandidate.Legacy.Bytes CACHE_BYTES
end SigGolfCandidate
end

section



namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy OracleComp OracleSpec
abbrev Val := List Byte
def byte (n : Nat) : Byte := BitVec.ofNat 8 n
def leBytes (k v : Nat) : List Byte := (List.range k).map fun i => byte (v / 256 ^ i)
def le32 (v : Nat) : List Byte := leBytes 4 v
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs
def zeros (k : Nat) : List Byte := List.replicate k 0
def toList {n : Nat} (x : Bytes n) : List Byte := SigGolfCandidate.Legacy.bytes x
def ofList (n : Nat) (l : List Byte) : Bytes n := BitVec.ofNat (8 * n) (leNat l)
def answerBytes (k : Nat) (a : BitVec 256) : List Byte :=
  (List.range k).map fun i => a.extractLsb' (8 * i) 8
def slice (l : List Byte) (off len : Nat) : List Byte := (l.drop off).take len
def nChains : Nat := 42
def targetSum : Nat := 181
abbrev target : Nat := targetSum
def nLayers : Nat := 5
def heights : List Nat := [11,6,6,6,5]
def totalH : Nat := 34
def porsH : Nat := 14
def porsK : Nat := 15
def porsT : Nat := 2 ^ porsH
def porsM : Nat := 118
def porsSegs : Nat := 2 * porsK - 1
def aMax : Nat := 2 ^ 20
def cMax : Nat := 2 ^ 22
def sigBytes : Nat := 6048
def witBytes : Nat := 6348
def height (lay : Nat) : Nat := heights.getD lay 0
def shiftBelow (lay : Nat) : Nat := ((List.range nLayers).filter (lay < ·)).foldr (height · + ·) 0
def route (idx lay : Nat) : Nat × Nat :=
  (idx / 2 ^ shiftBelow lay % 2 ^ height lay, idx / 2 ^ (shiftBelow lay + height lay))
abbrev topH : Nat := height 0
def topN (l : Nat) : Nat := ((List.range l).map fun k => 2 ^ (topH - k)).sum
def regionBytes : Nat := 16 * topN topH
def cacheBytes : Nat := CACHE_BYTES
def cacheNodeOff (l j : Nat) : Nat := 32 + 16 * (topN l + j)
def cacheNode (cache : List Byte) (l j : Nat) : Val := slice cache (cacheNodeOff l j) 16
def cacheTag (cache : List Byte) : List Byte := slice cache 0 32
def cacheRegion (cache : List Byte) : List Byte := slice cache 32 regionBytes
def xorBytes (a b : List Byte) : List Byte := List.zipWith (· ^^^ ·) a b
def tweak (t lay tau p j : Nat) : List Byte :=
  [byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ le32 p ++ le32 (tau % 2 ^ 32) ++ le32 j
def P : List Byte := zeros 16
def thInput (tw payload : List Byte) : List Byte := tw ++ P ++ payload
def padBlocks (len : Nat) : Nat := (len + 63) / 64 - 1
def padTo64 (x : List Byte) : List Byte :=
  x ++ zeros (64 * (padBlocks x.length + 1) - x.length)
def pad64 (x : List Byte) : Query := ⟨padBlocks x.length, ofList _ (padTo64 x)⟩
def IsChainFmt (x : List Byte) : Prop := x.length = 48 ∧ x.getD 1 0 = byte 1
instance (x : List Byte) : Decidable (IsChainFmt x) :=
  inferInstanceAs (Decidable (x.length = 48 ∧ x.getD 1 0 = byte 1))
def IsNodeFmt (x : List Byte) : Prop := x.length = 64 ∧ x.getD 1 0 = byte 3
instance (x : List Byte) : Decidable (IsNodeFmt x) :=
  inferInstanceAs (Decidable (x.length = 64 ∧ x.getD 1 0 = byte 3))
def IsDigestFmt (x : List Byte) : Prop := x.length = 96 ∧ x.getD 1 0 = byte 12
instance (x : List Byte) : Decidable (IsDigestFmt x) :=
  inferInstanceAs (Decidable (x.length = 96 ∧ x.getD 1 0 = byte 12))
def splitP (p : Nat) : Nat := p % 8 + 256 * (p / 8)
def heapIndex (h lam j : Nat) : Nat := 2 ^ (h - lam) + j
def nodeHeight (x : List Byte) : Nat := height (x.getD 2 0).toNat
def chainBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 (splitP (leNat (slice x 4 4))) ++ slice x 8 8 ++ zeros 32 ++ x.drop 32
def nodeBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 0 ++ slice x 8 4 ++
    le32 (heapIndex (nodeHeight x) (leNat (slice x 4 4)) (leNat (slice x 12 4))) ++ x.drop 16
def digestBlock (x : List Byte) : List Byte := x.take 16 ++ slice x 32 16 ++ x.drop 64
def fmt (x : List Byte) : Query :=
  if IsChainFmt x then ⟨0, ofList _ (chainBlock x)⟩
  else if IsNodeFmt x then ⟨0, ofList _ (nodeBlock x)⟩
  else if IsDigestFmt x then ⟨0, ofList _ (digestBlock x)⟩
  else pad64 x
def fmtList (x : List Byte) : List Byte :=
  if IsChainFmt x then chainBlock x
  else if IsNodeFmt x then nodeBlock x
  else if IsDigestFmt x then digestBlock x
  else padTo64 x
def H (x : List Byte) : OracleComp HashSpec (BitVec 256) := HashSpec.query (fmt x)
def prf2 (x : List Byte) : OracleComp HashSpec (Val × Val) := do
  let a ← H x
  pure ((answerBytes 32 a).take 16, (answerBytes 32 a).drop 16)
def hash16 (x : List Byte) : OracleComp HashSpec Val := do
  let a ← H x
  pure (answerBytes 16 a)
def th (tw payload : List Byte) : OracleComp HashSpec Val := hash16 (thInput tw payload)
def prfInput (S : List Byte) (lay tau e i : Nat) : List Byte := thInput (tweak 0 lay tau i e) S
def chainInput (lay tau e i mu : Nat) (v : Val) : List Byte :=
  thInput (tweak 1 lay tau (8 * i + mu - 1) e) v
def leafInput (lay tau e : Nat) (ends : List Val) : List Byte :=
  thInput (tweak 2 lay tau 0 e) ends.flatten
def nodeInput (lay tau lam j : Nat) (l r : Val) : List Byte :=
  thInput (tweak 3 lay tau lam j) (l ++ r)
def encInput (lay tau e : Nat) (M : Val) (c : Nat) : List Byte :=
  thInput (tweak 4 lay tau 0 e) (M ++ le32 c)
def rndInput (S m : List Byte) (a : Nat) : List Byte :=
  [byte 1, byte 7] ++ S.take 26 ++ m ++ le32 a
def porsPrfInput (S : List Byte) (idx q : Nat) : List Byte := thInput (tweak 8 0 idx 0 q) S
def porsLeafInput (idx j : Nat) (s : Val) : List Byte := thInput (tweak 9 0 idx 0 j) s
def porsNodeInput (idx H : Nat) (l r : Val) : List Byte := thInput (tweak 10 0 idx 0 H) (l ++ r)
def digestInput (rho m : List Byte) : List Byte := thInput (tweak 12 0 0 0 0) (rho ++ zeros 16 ++ m)
def maskInput (S : List Byte) (l j : Nat) : List Byte := thInput (tweak 13 0 0 l j) S
def macInput (S region : List Byte) : List Byte := thInput (tweak 14 0 0 0 0) (S ++ region)
def digest (rho m : List Byte) : OracleComp HashSpec Nat := do
  let a ← H (digestInput rho m)
  pure a.toNat
def idxOf (N : Nat) : Nat := N % 2 ^ totalH
def leafOf (N r : Nat) : Nat := N / 2 ^ (totalH + porsH * r) % 2 ^ porsH
def leavesOf (N : Nat) : List Nat := (List.range porsK).map (leafOf N)
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1
def octopusSize (vs : List Nat) : Nat :=
  porsH + 2 + (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum - 2 * vs.length
def sortLeaves (v : List Nat) : List Nat := v.insertionSort (· ≤ ·)
def admissible (N : Nat) : Bool :=
  decide (leavesOf N).Nodup && decide (octopusSize (sortLeaves (leavesOf N)) ≤ porsM)
structure SchedState where
  segs : List Nat
  reads : List (Nat × Nat)
  stack : List Nat
deriving DecidableEq, Repr
def schedStep (x : SchedState × Nat × Nat × Nat) (h : Nat) : SchedState × Nat × Nat × Nat :=
  let (st, E, cnt, t) := x
  match st.stack with
  | Q :: rest =>
    if Q = E then ({ st with segs := st.segs ++ [cnt ||| 16 ||| 32 * t], stack := rest },
      E / 2, 0, E / 2 % 2)
    else ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, t)
  | [] => ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, t)
def schedLeaf (vs : List Nat) (st : SchedState) (s : Nat) : SchedState :=
  let k := vs.length
  let E := porsT ||| vs.getD s 0
  let top := if s + 1 < k then bitLen (vs.getD s 0 ^^^ vs.getD (s + 1) 0) - 1 else porsH
  let (st, E, cnt, t) := (List.range top).foldl schedStep (st, E, 0, E % 2)
  let st := { st with segs := st.segs ++ [cnt ||| 32 * t] }
  if s + 1 < k then { st with stack := (E ^^^ 1) :: st.stack } else st
def schedule (vs : List Nat) : List Nat × List (Nat × Nat) :=
  let st := (List.range vs.length).foldl (schedLeaf vs) ⟨[], [], []⟩
  (st.segs, st.reads)
def digitsOfWord (d : Nat) : List Nat := (List.range 21).map fun r => d / 8 ^ r % 8
def decodeDigits (v : Val) : Option (List Nat) :=
  let d0 := leNat (slice v 0 8)
  let d1 := leNat (slice v 8 8)
  if d0 < 2 ^ 63 ∧ d1 < 2 ^ 63 then
    let x := digitsOfWord d0 ++ digitsOfWord d1
    if x.sum = targetSum then some x else none
  else none
end SigGolfCandidate.Ref
end
