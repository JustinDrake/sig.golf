import SigGolfCandidate.AlternativeChainAlgorithms

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

def fullLeaf (sk : List Byte) (lay tree leaf : Nat) (digits : List Nat) :
    OracleComp HashSpec (Val × List Val) := do
  let st ← (List.range 31).foldlM (fun (st : List Val × List Val) q => do
    let (a, b) ← pair (input 0 lay tree q leaf sk)
    let (ea, va) ← chainWithCapture lay tree leaf (2*q) (digits.getD (2*q) 0) a
    let (eb, vb) ← chainWithCapture lay tree leaf (2*q+1) (digits.getD (2*q+1) 0) b
    pure (st.1 ++ [ea, eb], st.2 ++ [va, vb])) ([], [])
  let root ← h16 (input 2 lay tree 0 leaf st.1.flatten)
  pure (root, st.2)

abbrev Node := Nat → Nat → Val → Val → List Byte

def treeNode (lay tree : Nat) : Node := fun level j a b =>
  input 3 lay tree 0 (2 ^ (height lay - level) + j) (a ++ b)

def forestNode (idx tree : Nat) : Node := fun level j a b =>
  input 10 tree idx 0 (2 ^ (9 - level) + j) (a ++ b)

def levels (node : Node) (h : Nat) (leaves : List Val) :
    OracleComp HashSpec (List (List Val)) :=
  (List.range' 1 h).foldlM (fun acc level => do
    let prev := acc.getD (level - 1) []
    let next ← (List.range (prev.length / 2)).foldlM (fun out j => do
      let v ← h16 (node level j (prev.getD (2*j) []) (prev.getD (2*j+1) []))
      pure (out ++ [v])) []
    pure (acc ++ [next])) [leaves]

def path (table : List (List Val)) (h leaf : Nat) : List Val :=
  (List.range h).map fun level =>
    (table.getD level []).getD ((leaf / 2 ^ level) ^^^ 1) []

def fullTree (sk : List Byte) (lay tree selected : Nat) (digits : List Nat) :
    OracleComp HashSpec (List (List Val) × List Val) := do
  let st ← (List.range (2 ^ height lay)).foldlM
    (fun (st : List Val × List Val) leaf => do
      let (v, vals) ← fullLeaf sk lay tree leaf digits
      pure (st.1 ++ [v], if leaf = selected then vals else st.2)) ([], [])
  let table ← levels (treeNode lay tree) (height lay) st.1
  pure (table, st.2)

def foldPath (node : Node) (leaf : Nat) (v : Val) (siblings : List Val) :
    OracleComp HashSpec Val :=
  (List.range siblings.length).foldlM (fun cur level =>
    let sib := siblings.getD level []
    let j := leaf / 2 ^ (level + 1)
    if leaf / 2 ^ level % 2 = 0 then h16 (node (level+1) j cur sib)
    else h16 (node (level+1) j sib cur)) v

def digest (rho m : List Byte) : OracleComp HashSpec Nat := do
  let out ← hash ([byte 2, byte 12] ++ zeros 14 ++ rho ++ m)
  pure out.toNat

def instanceIndex (d : Nat) : Nat := d % 2 ^ 33
def forestIndex (d tree : Nat) : Nat := d / 2 ^ (33 + 9 * tree) % 512
def digestOK (d : Nat) : Bool := decide (d / 2 ^ 186 % 4096 = 0)

def findDigest (sk m : List Byte) (trial : Nat) :
    Nat → OracleComp HashSpec (Option (Val × Nat))
  | 0 => pure none
  | fuel + 1 => do
    let (a, b) ← pair ([byte 2, byte 7] ++ sk.take 26 ++ m ++ le32 trial)
    let da ← digest a m
    if digestOK da then pure (some (a, da)) else do
      let db ← digest b m
      if digestOK db then pure (some (b, db))
      else findDigest sk m (trial+1) fuel

def encoding (lay tree leaf : Nat) (m : Val) (counter : Nat) :
    OracleComp HashSpec (Option (List Nat)) := do
  let out ← hash (input 4 lay tree 0 leaf (m ++ le32 counter))
  pure ((Base4Candidate.decode (out.extractLsb' 0 128)).map fun x =>
    List.ofFn fun i : Fin 62 => (x i).val)

def findCounter (lay tree leaf : Nat) (m : Val) (counter : Nat) :
    Nat → OracleComp HashSpec (Option (Nat × List Nat))
  | 0 => pure none
  | fuel + 1 => do
    match ← encoding lay tree leaf m counter with
    | some digits => pure (some (counter, digits))
    | none => findCounter lay tree leaf m (counter+1) fuel

theorem digestOK_checkField (u : BitVec 256) :
    digestOK u.toNat = true ↔ checkField u = 0 := by
  simp only [digestOK, decide_eq_true_eq]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    change (checkField u).toNat = 0
    rw [checkField_toNat]
    exact h
  · intro h
    have he := congrArg BitVec.toNat h
    change (checkField u).toNat = 0 at he
    rwa [checkField_toNat] at he


end SigGolfCandidate.Base4Candidate.Reference
