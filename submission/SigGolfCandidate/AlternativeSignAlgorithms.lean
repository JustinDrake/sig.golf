import SigGolfCandidate.AlternativeTreeAlgorithms

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

structure Opening where
  secret : Val
  siblings : List Val
deriving Inhabited

structure LayerOpening where
  values : List Val
  siblings : List Val
deriving Inhabited

structure Signature where
  randomness : Val
  forest : List Opening
  layers : List LayerOpening

structure Witness where
  signature : Signature
  counters : List Nat
  padding : List Val

def forestSign (sk : List Byte) (d : Nat) :
    OracleComp HashSpec (Val × List Opening) := do
  let idx := instanceIndex d
  let st ← (List.range 17).foldlM (fun (st : List Val × List Opening) tree => do
    let selected := forestIndex d tree
    let leaves ← (List.range 256).foldlM (fun (st : List Val × Val) q => do
      let (a, b) ← pair (input 8 tree idx 0 q sk)
      let va ← h16 (input 9 tree idx 0 (2*q) a)
      let vb ← h16 (input 9 tree idx 0 (2*q+1) b)
      pure (st.1 ++ [va, vb], if selected = 2*q then a
        else if selected = 2*q+1 then b else st.2)) ([], [])
    let table ← levels (forestNode idx tree) 9 leaves.1
    pure (st.1 ++ [(table.getD 9 []).getD 0 []],
      st.2 ++ [⟨leaves.2, path table 9 selected⟩])) ([], [])
  let root ← h16 (input 11 0 idx 0 0 st.1.flatten)
  pure (root, st.2)

def forestRecover (d : Nat) (opens : List Opening) : OracleComp HashSpec Val := do
  let idx := instanceIndex d
  let roots ← (List.range 17).foldlM (fun roots tree => do
    let op := opens.getD tree default
    let selected := forestIndex d tree
    let leaf ← h16 (input 9 tree idx 0 selected op.secret)
    let root ← foldPath (forestNode idx tree) selected leaf op.siblings
    pure (roots ++ [root])) []
  h16 (input 11 0 idx 0 0 roots.flatten)

def xorVal (a b : Val) : Val := List.zipWith (· ^^^ ·) a b
def maskInput (sk : List Byte) (heap : Nat) : List Byte := input 13 0 0 0 heap sk
def cacheRegion (cache : List Byte) : List Byte := slice cache 32 131040
def macInput (sk region : List Byte) : List Byte := input 14 0 0 0 0 (sk ++ region)

def heapValue (table : List (List Val)) (heap : Nat) : Val :=
  let depth := Nat.log2 heap
  (table.getD (12 - depth) []).getD (heap - 2 ^ depth) []

def keygen (sk : List Byte) : OracleComp HashSpec (Val × List Byte) := do
  let (table, _) ← fullTree sk 0 0 0 []
  let masked ← (List.range' 2 8190).foldlM (fun out heap => do
    let mask ← h16 (maskInput sk heap)
    pure (out ++ xorVal (heapValue table heap) mask)) []
  let tag ← hash (macInput sk masked)
  pure ((table.getD 12 []).getD 0 [], answerBytes 32 tag ++ masked)

def topSign (sk cache : List Byte) (idx : Nat) (digits : List Nat) :
    OracleComp HashSpec LayerOpening := do
  let (e, _) := route idx 0
  let vals ← (List.range 31).foldlM (fun out q => do
    let (a, b) ← pair (input 0 0 0 q e sk)
    let va ← walk 0 0 e (2*q) 1 (digits.getD (2*q) 0) a
    let vb ← walk 0 0 e (2*q+1) 1 (digits.getD (2*q+1) 0) b
    pure (out ++ [va, vb])) []
  let siblings ← (List.range 12).foldlM (fun out level => do
    let heap := (2 ^ (12 - level) + e / 2 ^ level) ^^^ 1
    let mask ← h16 (maskInput sk heap)
    pure (out ++ [xorVal (slice cache (32 + 16 * (heap - 2)) 16) mask])) []
  pure ⟨vals, siblings⟩

def signLayers (sk cache : List Byte) (idx : Nat) :
    Nat → Val → OracleComp HashSpec (Option (List LayerOpening))
  | 0, m => do
    let (e, tree) := route idx 0
    match ← findCounter 0 tree e m 0 (2 ^ 22) with
    | none => pure none
    | some (_, digits) => do
      let op ← topSign sk cache idx digits
      pure (some [op])
  | lay + 1, m => do
    let (e, tree) := route idx (lay+1)
    match ← findCounter (lay+1) tree e m 0 (2 ^ 22) with
    | none => pure none
    | some (_, digits) => do
      let (table, vals) ← fullTree sk (lay+1) tree e digits
      match ← signLayers sk cache idx lay ((table.getD (height (lay+1)) []).getD 0 []) with
      | none => pure none
      | some rest => pure (some (rest ++ [⟨vals, path table (height (lay+1)) e⟩]))

def sign (sk cache m : List Byte) : OracleComp HashSpec (Option Signature) := do
  let tag ← hash (macInput sk (cacheRegion cache))
  if answerBytes 32 tag != slice cache 0 32 then pure none else do
    match ← findDigest sk m 0 (2 ^ 20) with
    | none => pure none
    | some (rho, d) => do
      let (root, forest) ← forestSign sk d
      match ← signLayers sk cache (instanceIndex d) 3 root with
      | none => pure none
      | some layers => pure (some ⟨rho, forest, layers⟩)

theorem checkField_card :
    (Finset.univ.filter fun u : BitVec 256 => checkField u = 0).card = 2 ^ 244 := by
  have hhigh := SphincsSecurity.Completeness.card_filter_high
    (n := 256) (w := 186) (by decide) (fun v => v.extractLsb' 0 12 = 0)
  have hlow := SphincsSecurity.Completeness.card_filter_low
    (n := 70) (w := 12) (by decide) (fun v => v = 0)
  have hzset : (Finset.univ.filter fun d : BitVec 12 => d = 0) = {0} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  have hz : (Finset.univ.filter fun d : BitVec 12 => d = 0).card = 1 := by
    rw [hzset, Finset.card_singleton]
  have hset : (Finset.univ.filter fun u : BitVec 256 => checkField u = 0) =
      (Finset.univ.filter fun u : BitVec 256 =>
        (u.extractLsb' 186 (256 - 186)).extractLsb' 0 12 = 0) := by
    apply Finset.filter_congr
    intro u _
    rfl
  calc
    (Finset.univ.filter fun u : BitVec 256 => checkField u = 0).card =
        2^186 * (Finset.univ.filter fun v : BitVec 70 => v.extractLsb' 0 12 = 0).card := by
      rw [hset]
      exact hhigh
    _ = 2^186 * ((Finset.univ.filter fun v : BitVec 12 => v = 0).card * 2^(70-12)) :=
      congrArg (fun count : Nat => 2^186 * count) hlow
    _ = 2^244 := by rw [hz]; norm_num



end SigGolfCandidate.Base4Candidate.Reference
