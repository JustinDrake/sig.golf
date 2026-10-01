import SigGolfCandidate.Transfer.Final
import SigGolfCandidate.Equiv.Basic
import SigGolfCandidate.Legacy.Programs
import SigGolfCandidate.Sign.Words
import SigGolfCandidate.Verify.Swar
import SigGolfCandidate.Rv.Hash
import SigGolfCandidate.Rv.Steps
import VCVio.OracleComp.QueryTracking.WriterCost
import Mathlib.Tactic.IrreducibleDef
import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.Ref.Basic
import SigGolfCandidate.Ref.Scheme
import SigGolfCandidate.Ref.Count
import SigGolfCandidate.Ref.Lemmas

import SigGolfCandidate.Ref.AddressQueries
import SigGolfCandidate.Rv.Tactic
import SigGolfCandidate.Equiv.Tree
import SigGolfCandidate.SphincsSecurity.Completeness.Decay
import SigGolfCandidate.SphincsSecurity.Completeness.Code
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform

/-!
Reference implementation under development: four-layer radix-four/FORS.

This file is not the production submission and does not assert a certificate.
It defines the proposed oracle algorithms before their RISC-V refinement. All
loops are explicitly finite. Its protocol byte is 2. An independently proved
address-header involution prepares its chain queries for an in-place verifier.
-/

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference

open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

def height (lay : Nat) : Nat := if lay = 0 then 12 else 7
def route (idx lay : Nat) : Nat × Nat :=
  let cut := if lay = 0 then 21 else 7 * (3 - lay)
  (idx / 2 ^ cut % 2 ^ height lay, idx / 2 ^ (cut + height lay))

def header (tag lay tree pos index : Nat) : List Byte :=
  [byte 2, byte tag, byte lay, byte (tree / 2 ^ 32)] ++
    le32 pos ++ le32 tree ++ le32 index

def input (tag lay tree pos index : Nat) (payload : List Byte) : List Byte :=
  header tag lay tree pos index ++ zeros 16 ++ payload

def hash (bs : List Byte) : OracleComp HashSpec (BitVec 256) :=
  HashSpec.query (Base4Candidate.AddressFormat.queryPerm (SigGolfCandidate.Ref.pad64 bs))

def h16 (bs : List Byte) : OracleComp HashSpec Val := do
  let out ← hash bs
  pure (answerBytes 16 out)

def pair (bs : List Byte) : OracleComp HashSpec (Val × Val) := do
  let out ← hash bs
  pure ((answerBytes 32 out).take 16, (answerBytes 32 out).drop 16)

def chainInput (lay tree leaf i step : Nat) (v : Val) : List Byte :=
  header 1 lay tree (256 * i + step - 1) leaf ++ zeros 32 ++ v

def chainInputP (lay tree leaf i step : Nat) (pad v : Val) : List Byte :=
  header 1 lay tree (256 * i + step - 1) leaf ++ pad ++ v

def walk (lay tree leaf i start count : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' start count).foldlM
    (fun v step => h16 (chainInput lay tree leaf i step v)) v

def walkP (lay tree leaf i start count : Nat) (pad v : Val) : OracleComp HashSpec Val :=
  (List.range' start count).foldlM
    (fun v step => h16 (chainInputP lay tree leaf i step pad v)) v

theorem walkP_zero (lay tree leaf i start count : Nat) (v : Val) :
    walkP lay tree leaf i start count (zeros 32) v = walk lay tree leaf i start count v := rfl

theorem ranges_split (s a b : Nat) :
    List.range' s (a+b) = List.range' s a ++ List.range' (s+a) b := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
    simp only [Nat.succ_add, List.range'_succ, List.cons_append]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 a]

theorem walk_add (lay tree leaf i start a b : Nat) (v : Val) :
    walk lay tree leaf i start (a+b) v = (do
      let mid ← walk lay tree leaf i start a v
      walk lay tree leaf i (start+a) b mid) := by
  unfold walk
  rw [ranges_split, List.foldlM_append]

/-- A disclosed initialPart and the verifier's remaining steps compose exactly. -/
theorem walk_recover (lay tree leaf i digit : Nat) (hd : digit ≤ 3) (v : Val) :
    (do
      let mid ← walk lay tree leaf i 1 digit v
      walk lay tree leaf i (digit+1) (3-digit) mid) = walk lay tree leaf i 1 3 v := by
  simpa only [Nat.add_comm 1 digit, Nat.add_sub_of_le hd] using
    (walk_add lay tree leaf i 1 digit (3-digit) v).symm

def chainWithCapture (lay tree leaf i digit : Nat) (v : Val) :
    OracleComp HashSpec (Val × Val) :=
  (List.range' 1 3).foldlM (fun (st : Val × Val) step => do
    let next ← h16 (chainInput lay tree leaf i step st.1)
    pure (next, if step = digit then next else st.2)) (v, v)

/-- The captured value is precisely a initialPart, including the zero-step case. -/
theorem chainWithCapture_split (lay tree leaf i digit : Nat) (hd : digit ≤ 3) (v : Val) :
    chainWithCapture lay tree leaf i digit v = (do
      let initialPart ← walk lay tree leaf i 1 digit v
      let endpoint ← walk lay tree leaf i (digit+1) (3-digit) initialPart
      pure (endpoint, initialPart)) := by
  unfold chainWithCapture walk
  have hc := fun x l hx a c => SigGolfCandidate.Equiv.capFold_notin
    (fun step v => h16 (chainInput lay tree leaf i step v)) x l hx a c
  cases digit with
  | zero =>
    rw [hc 0 _ (by simp)]
    simp
  | succ k =>
    have hs : List.range' 1 3 =
        List.range' 1 k ++ (1+k) :: List.range' (1+k+1) (2-k) := by
      rw [← List.range'_succ, show 2-k+1 = 3-k by omega, List.range'_append_1]
      congr 1
      omega
    rw [hs, List.foldlM_append, hc (k+1) _ (by simp; omega)]
    simp only [map_bind, bind_map_left, List.foldlM_cons, bind_assoc, pure_bind]
    rw [show List.range' 1 (k+1) = List.range' 1 k ++ [1+k] by
      rw [List.range'_concat]; simp]
    simp only [List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_assoc, bind_pure]
    congr 1
    funext w
    congr 1
    funext z
    rw [if_pos (by omega), hc (k+1) _ (by simp),
      show k+1+1 = 1+k+1 by omega, show 3-(k+1) = 2-k by omega]
    simp only [map_eq_bind_pure_comp]

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

def recoverLayerP (idx lay : Nat) (digits : List Nat) (op : LayerOpening) (padding : List Val) :
    OracleComp HashSpec Val := do
  let (e, tree) := route idx lay
  let ends ← (List.range 62).foldlM (fun out i => do
    let digit := digits.getD i 0
    let v ← walkP lay tree e i (digit+1) (3-digit)
      (padding.getD (62 * lay + i) (zeros 32)) (op.values.getD i [])
    pure (out ++ [v])) []
  let leaf ← h16 (input 2 lay tree 0 e ends.flatten)
  foldPath (treeNode lay tree) e leaf op.siblings

def recoverLayer (idx lay : Nat) (digits : List Nat) (op : LayerOpening) :
    OracleComp HashSpec Val := recoverLayerP idx lay digits op []

def shapeOK (sig : Signature) : Bool :=
  sig.randomness.length == 16 && sig.forest.length == 17 && sig.layers.length == 4 &&
    sig.forest.all (fun op => op.secret.length == 16 && op.siblings.length == 9 &&
      op.siblings.all (fun v => v.length == 16)) &&
    (List.range 4).all (fun lay =>
      let op := sig.layers.getD lay default
      op.values.length == 62 && op.values.all (fun v => v.length == 16) &&
        op.siblings.length == height lay && op.siblings.all (fun v => v.length == 16))

def recoverLayers (idx : Nat) (sig : Signature) (counters : List Nat) (padding : List Val) :
    Nat → Val → OracleComp HashSpec (Option Val)
  | 0, root => pure (some root)
  | n+1, root => do
    let (e, tree) := route idx n
    let counter := counters.getD n (2 ^ 22)
    if counter ≥ 2 ^ 22 then pure none else do
      match ← encoding n tree e root counter with
      | none => pure none
      | some digits => do
        let next ← recoverLayerP idx n digits (sig.layers.getD n default) padding
        recoverLayers idx sig counters padding n next

def verify (pk m : List Byte) (w : Witness) : OracleComp HashSpec Bool := do
  if !shapeOK w.signature || w.counters.length != 4 || w.padding.length != 248 ||
      !(w.padding.all fun p => p.length == 32) then pure false else do
    let d ← digest w.signature.randomness m
    if !digestOK d then pure false else do
      let root ← forestRecover d w.signature.forest
      let result ← recoverLayers (instanceIndex d) w.signature w.counters w.padding 4 root
      pure (result == some pk)

def expandLayers (idx : Nat) (sig : Signature) :
    Nat → Val → OracleComp HashSpec (Option (Val × List Nat))
  | 0, root => pure (some (root, []))
  | n+1, root => do
    let (e, tree) := route idx n
    match ← findCounter n tree e root 0 (2 ^ 22) with
    | none => pure none
    | some (counter, digits) => do
      let next ← recoverLayer idx n digits (sig.layers.getD n default)
      match ← expandLayers idx sig n next with
      | none => pure none
      | some (top, rest) => pure (some (top, rest ++ [counter]))

def expand (pk m : List Byte) (sig : Signature) : OracleComp HashSpec (Option Witness) := do
  if !shapeOK sig then pure none else do
    let d ← digest sig.randomness m
    if !digestOK d then pure none else do
      let root ← forestRecover d sig.forest
      match ← expandLayers (instanceIndex d) sig 4 root with
      | none => pure none
      | some (top, counters) =>
        pure (if top == pk then some ⟨sig, counters, List.replicate 248 (zeros 32)⟩ else none)

def serialize (sig : Signature) : List Byte :=
  sig.randomness ++ (sig.forest.map fun op => op.secret ++ op.siblings.flatten).flatten ++
    (sig.layers.map fun op => op.values.flatten ++ op.siblings.flatten).flatten

/-- Compact layer offsets; the signature never transmits search counters. -/
def layerOffset (lay : Nat) : Nat := [2736, 3920, 5024, 6128].getD lay 0

def parseForest (bs : List Byte) : List Opening :=
  (List.range 17).map fun tree =>
    ⟨slice bs (16 + 160 * tree) 16,
      (List.range 9).map fun level => slice bs (32 + 160 * tree + 16 * level) 16⟩

def parse (bs : List Byte) : Option Signature :=
  if bs.length = 7232 then
    some ⟨slice bs 0 16, parseForest bs,
      (List.range 4).map fun lay =>
        ⟨(List.range 62).map (fun i => slice bs (layerOffset lay + 16 * i) 16),
          (List.range (height lay)).map
            (fun level => slice bs (layerOffset lay + 992 + 16 * level) 16)⟩⟩
  else none

/-- Witness: forest initialPart, four counters, all paths, 48 spare bytes, then 248
in-place chain blocks. The 19200-byte witness costs 75 cycles. -/
def witnessPathOffset (lay : Nat) : Nat := [2752, 2944, 3056, 3168].getD lay 0
def witnessChainOffset (lay i : Nat) : Nat := 3328 + 64 * (62 * lay + i)

def serializeWitness (w : Witness) : List Byte :=
  w.signature.randomness ++
    (w.signature.forest.map fun op => op.secret ++ op.siblings.flatten).flatten ++
    (w.counters.map le32).flatten ++
    (w.signature.layers.map fun op => op.siblings.flatten).flatten ++ zeros 48 ++
    ((List.range 4).map fun lay =>
      ((List.range 62).map fun i =>
        zeros 16 ++ w.padding.getD (62 * lay + i) (zeros 32) ++
          (w.signature.layers.getD lay default).values.getD i []).flatten).flatten

def parseWitness (bs : List Byte) : Option Witness :=
  if bs.length = 19200 then
    some ⟨⟨slice bs 0 16, parseForest bs,
      (List.range 4).map fun lay =>
        ⟨(List.range 62).map
            (fun i => slice bs (witnessChainOffset lay i + 48) 16),
          (List.range (height lay)).map
            (fun level => slice bs (witnessPathOffset lay + 16 * level) 16)⟩⟩,
      (List.range 4).map (fun lay => SigGolfCandidate.Ref.leNat (slice bs (2736 + 4 * lay) 4)),
      ((List.range 4).map fun lay =>
        (List.range 62).map fun i => slice bs (witnessChainOffset lay i + 16) 32).flatten⟩
  else none

def signBytes (sk cache m : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  let sig ← sign sk cache m
  pure (sig.map serialize)

def expandBytes (pk m sigBytes : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  match parse sigBytes with
  | none => pure none
  | some sig =>
    let w ← expand pk m sig
    pure (w.map serializeWitness)

def verifyBytes (pk m witnessBytes : List Byte) : OracleComp HashSpec Bool :=
  match parseWitness witnessBytes with
  | none => pure false
  | some w => verify pk m w

theorem witness_charge : (19200 + 255) / 256 = 75 := by decide
theorem witness_end : 2048 + 19200 = 21248 := by decide
theorem layout_room : 21248 ≤ 32768 ∧ 32768 + 131072 ≤ 196608 ∧
    196608 + 7232 < 2 ^ 24 := by decide

/-- The full non-root top-tree cache exactly fills the cache allowance. -/
theorem full_cache_bytes : 32 + 8190*16 = 131072 := by decide
theorem full_cache_mac : (32+32+131040+63)/64 = 2049 := by decide
theorem full_cache_keygen : 4096*234-1+8190+2049 = 968702 := by decide
theorem full_cache_keygen_room : 968702 < 2^20 := by decide
theorem full_cache_sign : 3*(128*234-1)+17*1279+5+2049+31+110+12 = 113803 := by decide

/-! The acceptance condition reads twelve bits disjoint from the 33 instance
bits and the 153 forest-index bits. This counts a fresh uniform output only;
adaptive freshness and finite-search failures require separate proofs. -/
def checkField (u : BitVec 256) : BitVec 12 :=
  (u.extractLsb' 186 70).extractLsb' 0 12

theorem checkField_toNat (u : BitVec 256) :
    (checkField u).toNat = u.toNat / 2 ^ 186 % 4096 := by
  have hi : u.toNat / 2 ^ 186 < 2 ^ 70 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [← Nat.pow_add] using u.isLt
  simp [checkField, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hi]

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

theorem checkField_card :
    (Finset.univ.filter fun u : BitVec 256 => checkField u = 0).card = 2 ^ 244 := by
  change (Finset.univ.filter fun u : BitVec 256 =>
    (fun v : BitVec (256-186) => v.extractLsb' 0 12 = 0) (u.extractLsb' 186 (256-186))).card = _
  rw [SphincsSecurity.Completeness.card_filter_high (n := 256) (w := 186) (by decide)
    (fun v => v.extractLsb' 0 12 = 0),
    SphincsSecurity.Completeness.card_filter_low (n := 70) (w := 12) (by decide) (fun v => v = 0)]
  have hz : (Finset.univ.filter fun d : BitVec 12 => d = 0).card = 1 := by simp
  rw [hz]
  norm_num

theorem fresh_digest_share :
    Pr[fun u : BitVec 256 => checkField u = 0 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = (4096 : ENNReal)⁻¹ := by
  rw [probEvent_uniformSample, checkField_card, Fintype.card_bitVec]
  norm_num

/-! These are search-tail arithmetic lemmas. The adaptive random-oracle proof
must supply their rejection-share premises; independence is not assumed here. -/
theorem digest_tail_arithmetic (x : ENNReal)
    (hx : x + (4097 : ENNReal)⁻¹ ≤ 1) :
    x ^ (2 ^ 21) ≤ (2⁻¹ : ENNReal) ^ 511 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hh := SphincsSecurity.Completeness.pow_le_half_ennreal 4097 (by decide) x hx
  calc
    x ^ (2 ^ 21) ≤ x ^ (4097 * 511) :=
      pow_le_pow_right_of_le_one' hx1 (by decide)
    _ = (x ^ 4097) ^ 511 := by rw [pow_mul]
    _ ≤ (2⁻¹ : ENNReal) ^ 511 := pow_le_pow_left' hh _

theorem counter_tail_arithmetic (x : ENNReal)
    (hx : x + (2268 : ENNReal)⁻¹ ≤ 1) :
    x ^ (2 ^ 22) ≤ (2⁻¹ : ENNReal) ^ 1024 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hh := SphincsSecurity.Completeness.pow_le_half_ennreal 2268 (by decide) x hx
  calc
    x ^ (2 ^ 22) ≤ x ^ (2268 * 1024) :=
      pow_le_pow_right_of_le_one' hx1 (by decide)
    _ = (x ^ 2268) ^ 1024 := by rw [pow_mul]
    _ ≤ (2⁻¹ : ENNReal) ^ 1024 := pow_le_pow_left' hh _

/-- The proposed finite searches leave room for a union over every message. -/
theorem all_message_tail_arithmetic :
    (2 : ENNReal) ^ 256 * ((2⁻¹ : ENNReal) ^ 511 +
      4 * (2⁻¹ : ENNReal) ^ 1024) ≤ ((2 : ENNReal) ^ 128)⁻¹ := by
  rw [← ENNReal.inv_pow, ← ENNReal.inv_pow]
  norm_num


end SigGolfCandidate.Base4Candidate.Reference
