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

namespace VerifyImage
open ChainCode FrontCode

/-- Branch targets use absolute positions in the core, including its rejection stub. -/
def appendLayer (initialPart : List Instruction) (lay : Nat) : List Instruction :=
  initialPart ++ LayerCode.caller lay (4*initialPart.length) ++ LayerCode.leafStart lay ++
    LayerFoldCode.dispatch lay 0 ++ (if lay = 0 then LayerFoldCode.dispatch lay 1 else [])

def compare (pc : Nat) : List Instruction :=
  [ld 3 0 384, ld 14 0 160, opR 4 3 3 14,
    ld 24 0 392, ld 26 0 168, opR 4 24 24 26, bor 3 3 24,
    branch 1 3 0 ((4 : Int)-(pc+28 : Nat)), addi 10 0 0, addi 5 0 1, hashInstruction]

def corePrefix : List Instruction :=
  [3,2,1,0].foldl appendLayer (FrontCode.code ++ LayerCode.setup)

def core : List Instruction := corePrefix ++ compare (4*corePrefix.length)

/-- Every fragment's placement requires a separate no-overlap proof. -/
def place (initialPart : List Instruction) (address : Nat) (fragment : List Instruction) : List Instruction :=
  initialPart ++ List.replicate (address/4-initialPart.length) nop ++ fragment

def dispatches : List Instruction :=
  (List.range 16).flatMap fun group => ChainCode.dispatch group ++ List.replicate 4 nop

def code : List Instruction :=
  let a := place core 4096 dispatches
  let b := place a 65536 ChainCode.bodies
  let c := place b 196608 ForestCode.shapes
  let d := place c 524288 ChainCode.entries
  place d 655360 LayerFoldCode.tables

/-- A complete proposed verifier image, not yet refined to the alternate reference.
The scored submission remains the original certified four-program suite. -/
def image : SigGolfCandidate.Legacy.Riscv.Image := ⟨code, LayerCode.maskData⟩

/-! Structural checks are kernel proofs about assembled list sizes; they do not
execute or benchmark the verifier. The execution/refinement theorem is separate. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem core_room : core.length ≤ 1024 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem dispatches_length : dispatches.length = 128 := by
  unfold dispatches
  rw [flatMap_length_constant (List.range 16) _ 8]
  · decide
  · intro group hg
    simp [ChainCode.dispatch_length]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem bodies_length : ChainCode.bodies.length = 26693 := by
  have hg (group : Nat) (h : group < 15) :
      ((List.range 64).flatMap (ChainCode.body group)).length = 1776 := by
    simpa only [List.length_flatMap,Function.comp_def,ChainCode.body_length]
      using ChainCode.group_words group h
  have ht : ((List.range 4).flatMap (ChainCode.body 15)).length = 53 := by
    simpa only [List.length_flatMap,Function.comp_def,ChainCode.body_length]
      using ChainCode.tail_words
  unfold ChainCode.bodies
  rw [show (16 : Nat) = 15+1 from rfl,List.range_succ,List.flatMap_append]
  simp only [List.length_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [if_pos rfl,ht]
  have hmain : ((List.range 15).flatMap fun group =>
      (List.range (if group = 15 then 4 else 64)).flatMap (ChainCode.body group)).length = 15*1776 := by
    apply flatMap_length_constant
    intro group hgroup
    have hb := List.mem_range.mp hgroup
    rw [if_neg (by omega)]
    exact hg group hb
  rw [hmain]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem forest_length : ForestCode.shapes.length = 65536 := by
  unfold ForestCode.shapes
  rw [flatMap_length_constant (List.range 512) _ 128]
  · decide
  · intro leaf hleaf
    exact ForestCode.shape_length leaf (List.mem_range.mp hleaf)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem entries_length : ChainCode.entries.length = 32768 := by
  unfold ChainCode.entries
  rw [flatMap_length_constant (List.range 256) _ 128]
  · decide
  · intro row hrow
    rw [flatMap_length_constant (List.range 16) _ 8]
    · decide
    · intro group hgroup
      exact ChainCode.entry_length group row

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem folds_length : LayerFoldCode.tables.length = 32768 := by decide +kernel

theorem image_bytes : image.byteSize = 786448 := by
  have hc := core_room
  simp only [image, SigGolfCandidate.Legacy.Riscv.Image.byteSize, code, place,
    List.length_append, List.length_replicate, dispatches_length, bodies_length,
    forest_length, entries_length, folds_length, LayerCode.maskData_length]
  norm_num only [Nat.reduceDiv]
  omega

theorem image_room : image.byteSize < 2^20 := by rw [image_bytes]; decide

end VerifyImage

/-! Initial symbolic block checks for official-kernel validation. These certify
opcode decoding and symbolic transitions up to the next HASH or branch; their
memory obligations still require the image-level framing/refinement proof. -/
namespace AsmChecks
open SigGolfCandidate.Rv

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

sym_block chain_zero := symRun { noAlias := true } (ChainCode.code 0 0) 65536 64
sym_block chain_one := symRun { noAlias := true } (ChainCode.code 0 1) 65536 64
sym_block chain_two := symRun { noAlias := true } (ChainCode.code 0 2) 65536 64
sym_block chain_three := symRun { noAlias := true } (ChainCode.code 0 3) 65536 64
sym_block last_chain_two := symRun { noAlias := true } (ChainCode.code 61 2) 65536 64
sym_block digest_prefix := symRun { noAlias := true } FrontCode.digestPrefix 16 64
sym_block digit_sum := symRun { noAlias := true } LayerCode.digitSum 0 64
sym_block quad_dispatch := symRun { noAlias := true } (ChainCode.dispatch 0) 4096 16
sym_block tail_dispatch := symRun { noAlias := true } (ChainCode.dispatch 15) 4576 16

end AsmChecks

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem image_room : image.byteSize < 2^20 := by decide +kernel

/-- Scratch slots remain inside the pinned memory even with their full HASH outputs. -/
theorem scratch_room : 720896+8192*32 < 2^24 ∧ 163840+32 < 196608 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem code_room : 4*code.length < 65536 := by decide +kernel

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem image_room : image.byteSize < 2^20 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem core_room : core.length ≤ 1024 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem image_bytes : image.byteSize = 786448 := by
  have hc := core_room
  simp only [image, SigGolfCandidate.Legacy.Riscv.Image.byteSize, code, VerifyImage.place,
    List.length_append, List.length_replicate, VerifyImage.dispatches_length,
    VerifyImage.bodies_length, VerifyImage.forest_length, VerifyImage.entries_length,
    VerifyImage.folds_length, LayerCode.maskData_length]
  norm_num only [Nat.reduceDiv]
  omega

theorem image_room : image.byteSize < 2^20 := by rw [image_bytes]; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem assembly_wellFormed : Assembler.WellFormed program := by decide +kernel

end ExpandCode

end SigGolfCandidate.Base4Candidate.Reference


