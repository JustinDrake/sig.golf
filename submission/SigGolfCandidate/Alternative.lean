import SigGolfCandidate.Legacy.Programs
import SigGolfCandidate.Sign.Words
import SigGolfCandidate.Verify.Swar
import SigGolfCandidate.Rv.Hash
import SigGolfCandidate.Rv.Steps
import VCVio.OracleComp.QueryTracking.WriterCost
import Mathlib.Tactic.IrreducibleDef
import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.Ref
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
theorem dispatches_length : dispatches.length = 128 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem bodies_length : ChainCode.bodies.length = 26693 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem forest_length : ForestCode.shapes.length = 65536 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem entries_length : ChainCode.entries.length = 32768 := by decide +kernel

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
theorem image_room : image.byteSize < 2^20 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem assembly_wellFormed : Assembler.WellFormed program := by decide +kernel

end ExpandCode

end SigGolfCandidate.Base4Candidate.Reference


/-! Typed ideal FORS model being ported from the verified baseline. This is
not yet linked to the alternate raw reference or RISC-V images. It supplies the
four-layer/radix-four types and the full top-tree cache for the forthcoming
security and correctness reductions. The digest search has 2^21 individual
candidates; relating these to 2^20 paired private-randomizer queries is separate.
-/

open OracleComp OracleSpec ENNReal

namespace SigGolfCandidate.Base4Candidate.Ideal

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 62
def targetSum : Nat := 110
def numLayers : Nat := 4
def totalHeight : Nat := 33
/-- The tallest layer, the top one, `h_0 = 12`, which bounds every layer's leaf index. -/
def maxLayerHeight : Nat := 12
def ftsTreeHeight : Nat := 9
/-- The `k` index groups a digest carries. The forest holds `k - 1` trees, the last group being pinned to zero. -/
def ftsTrees : Nat := 18
/-- Signatures allowed per key pair, `q_s`. -/
def signatureLimit : Nat := 2 ^ 32
/-- Digest attempts per signature, `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 21
/-- Encoding counters tried per layer, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 22

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := Digest
abbrev Counter := BitVec counterBits
abbrev Layer := Fin numLayers
/-- `idx`, which few-time key signs. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- `tau`, a tree of any layer. Layer `lay` only uses the values below `2^(sum_{j < lay} h_j)`. -/
abbrev TreeIndex := Fin (2 ^ totalHeight)
/-- `e`, a leaf of any layer. Layer `lay` only uses the values below `2^h_lay`. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
/-- A tree of the few-time forest, `kappa < k - 1`. -/
abbrev FtsTree := Fin (ftsTrees - 1)
/-- An index group of the message digest, `kappa < k`. The first `k - 1` select a tree's leaf; the last is pinned to zero. -/
abbrev IndexGroup := Fin ftsTrees
abbrev FtsLeaf := Fin (2 ^ ftsTreeHeight)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8
/-- A pair of chains `(2k, 2k + 1)` of a one-time key, whose secrets one derivation query yields. -/
abbrev ChainPair := Fin (numChains / 2)
/-- A pair of leaves `(2k, 2k + 1)` of a few-time tree, whose secrets one derivation query yields. -/
abbrev FtsPair := Fin (2 ^ (ftsTreeHeight - 1))

/-- Chain `2k`. -/
def evenChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val, by have := pair.isLt; unfold numChains at *; omega⟩
/-- Chain `2k + 1`. -/
def oddChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val + 1, by have := pair.isLt; unfold numChains at *; omega⟩
/-- The pair of a chain. -/
def chainPairOf (chainIdx : ChainIndex) : ChainPair := ⟨chainIdx.val / 2, by have := chainIdx.isLt; unfold numChains at *; omega⟩

/-- Leaf `2k`. -/
def evenFtsLeaf (pair : FtsPair) : FtsLeaf := ⟨2 * pair.val, by have := pair.isLt; unfold ftsTreeHeight at *; omega⟩
/-- Leaf `2k + 1`. -/
def oddFtsLeaf (pair : FtsPair) : FtsLeaf := ⟨2 * pair.val + 1, by have := pair.isLt; unfold ftsTreeHeight at *; omega⟩
/-- The pair of a leaf. -/
def ftsPairOf (leaf : FtsLeaf) : FtsPair := ⟨leaf.val / 2, by have := leaf.isLt; unfold ftsTreeHeight at *; omega⟩

/-- Spread per-pair values back to the members: even members take the first component. -/
def unpairChains {α : Type} (pairs : ChainPair → α × α) (chainIdx : ChainIndex) : α :=
  if chainIdx.val % 2 = 0 then (pairs (chainPairOf chainIdx)).1 else (pairs (chainPairOf chainIdx)).2

/-- Spread per-pair values back to the members: even leaves take the first component. -/
def unpairFtsLeaves {α : Type} (pairs : FtsPair → α × α) (leaf : FtsLeaf) : α :=
  if leaf.val % 2 = 0 then (pairs (ftsPairOf leaf)).1 else (pairs (ftsPairOf leaf)).2

/-- The four Merkle heights are `(12,7,7,7)`. Layer `0` carries the public key; its
tree is built by key generation and cached. -/
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else 7

def topLayer : Layer := ⟨0, by decide⟩
def bottomLayer : Layer := ⟨numLayers - 1, by decide⟩

/-- `sum_{j < lay} h_j`, the index bits above layer `lay`. -/
def heightAbove (lay : Layer) : Nat := ∑ j : Layer, if j.val < lay.val then layerHeight j else 0

/-- `sum_{j > lay} h_j`, the index bits below layer `lay`. -/
def heightBelow (lay : Layer) : Nat := totalHeight - heightAbove lay - layerHeight lay

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The message digest has 198 bits: the instance, eighteen nine-bit groups and three extra check bits. -/
def messageDigestBits : Nat := totalHeight + ftsTrees * ftsTreeHeight + 3

abbrev MessageDigest := BitVec messageDigestBits

/-- Keep the first `h + k * a` output bits. -/
def truncateMessageDigest (output : HashOutput) : MessageDigest :=
  output.extractLsb' 0 messageDigestBits

/-- `pk = (root, P)`. The parameter is always `P = 0`, so the published key is the root alone. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- One layer's WOTS signature and authentication path. -/
structure LayerSignature (lay : Layer) where
  counter : Counter
  chainValues : ChainIndex → Digest
  path : Fin (layerHeight lay) → Digest
deriving DecidableEq

/-- The randomizer, seventeen FORS openings, and four layer signatures. -/
structure Signature where
  randomness : Randomness
  ftsSecret : FtsTree → Digest
  ftsPath : FtsTree → Fin ftsTreeHeight → Digest
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The five fields of the specification's `enc(t, lay, tau, p, j)`. The tree field is 40 bits wide: few-time tweaks carry the 34-bit index there. -/
structure TweakFields where
  tag : BitVec 8
  layer : BitVec 8
  tree : BitVec 40
  position : BitVec 32
  index : BitVec 32
deriving DecidableEq

/-- The protocol domain separator. -/
def protocolDomainSep : UInt8 := 2

/-- The specification's 16 tweak bytes `protocol_domain_sep || tag || layer || tree >> 32 || position || tree mod 2^32 || index`, each field serialized least significant byte first: byte 3 carries bits 32..39 of the tree field. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  [protocolDomainSep] ++ bytesLE 1 fields.tag ++ bytesLE 1 fields.layer ++
    bytesLE 1 (fields.tree.extractLsb' 32 8) ++
    bytesLE 4 fields.position ++ bytesLE 4 (fields.tree.extractLsb' 0 32) ++ bytesLE 4 fields.index

/-- Convert the specification's five integer fields to their fixed widths. -/
def tweakFields (tag layer tree position index : Nat) : TweakFields :=
  ⟨BitVec.ofNat 8 tag, BitVec.ofNat 8 layer, BitVec.ofNat 40 tree,
    BitVec.ofNat 32 position, BitVec.ofNat 32 index⟩

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (level : Nat) (nodeIdx : Nat)
  | ftsRoots (index : Index)
  | message
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. Inside the hypertree the layer field is the layer and the tree field the tree; inside a few-time key they are the tree of the forest and the index that selects the instance. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => tweakFields 1 lay tree (chainLength * chainIdx + step) leaf
  | .leaf lay tree leaf => tweakFields 2 lay tree 0 leaf
  | .node lay tree level nodeIdx => tweakFields 3 lay tree level nodeIdx
  | .encoding lay tree leaf => tweakFields 4 lay tree 0 leaf
  | .ftsLeaf index tree leaf => tweakFields 9 tree index 0 leaf
  | .ftsNode index tree level nodeIdx => tweakFields 10 tree index level nodeIdx
  | .ftsRoots index => tweakFields 11 0 index 0 0
  | .message => tweakFields 12 0 0 0 0

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call and by the message digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

/-- `tweak(7, 0, 0, trial, 0) || P || S || m`. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) : HashInput :=
  fieldBytes ⟨7#8, 0#8, 0#40, trial, 0#32⟩ ++
    bytesLE 16 parameter ++ bytesLE 32 seed ++ bytesLE 32 message

inductive KeygenDomain where
  /-- The secrets of chains `2k` and `2k + 1` of a one-time key. -/
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair)
  /-- The secrets of leaves `2k` and `2k + 1` of a few-time tree. -/
  | fts (index : Index) (tree : FtsTree) (pair : FtsPair)
  /-- The mask of the cached top-tree node `(level, nodeIdx)`. -/
  | mask (level : Fin maxLayerHeight) (nodeIdx : Fin (2 ^ maxLayerHeight))
deriving DecidableEq

def keygenDomainFields : KeygenDomain → TweakFields
  | .ots lay tree leaf pair => tweakFields 0 lay tree pair leaf
  | .fts index tree pair => tweakFields 8 tree index 0 pair
  | .mask level nodeIdx => tweakFields 13 0 0 level nodeIdx

/-- `tweak || P || S`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  fieldBytes (keygenDomainFields domain) ++ bytesLE 16 parameter ++ bytesLE 32 seed

/-! ### The cache

Key generation publishes a 128 KiB cache: the 32-byte MAC tag, then the masked nodes of the top tree at
levels `0, ..., 10` (level ascending, index ascending within a level). The root is not stored; it is the
public key. The signer reads the top layer's authentication path from the cache after checking the tag. -/

/-- The masked nodes of the top tree below its root: level `l < 11` holds `2^(11 - l)` nodes. -/
abbrev TopRegion := (level : Fin maxLayerHeight) → Fin (2 ^ (maxLayerHeight - level.val)) → Digest

/-- The cache: the MAC tag (the full 256-bit hash answer) and the masked-node region. Unused bytes of the
128 KiB buffer are zero and not part of the abstract cache. -/
structure TopCache where
  tag : HashOutput
  region : TopRegion
deriving DecidableEq

/-- The masked node `(level, nodeIdx)`, or zero outside the region. -/
def TopCache.node (cache : TopCache) (level nodeIdx : Nat) : Digest :=
  if hlevel : level < maxLayerHeight then
    if hnode : nodeIdx < 2 ^ (maxLayerHeight - level) then cache.region ⟨level, hlevel⟩ ⟨nodeIdx, hnode⟩
    else 0
  else 0

/-- The region's bytes: level by level, each node as 16 bytes, `65504` bytes in all. -/
def regionBytes (region : TopRegion) : HashInput :=
  (List.ofFn fun level : Fin maxLayerHeight => (List.ofFn (region level)).flatMap (bytesLE 16)).flatten

/-- `tweak(14, 0, 0, 0, 0) || P || S || region`: the MAC over the region, keyed by the master seed. -/
def macHashInput (parameter : PublicParameter) (seed : MasterSeed) (region : TopRegion) : HashInput :=
  fieldBytes ⟨14#8, 0#8, 0#40, 0#32, 0#32⟩ ++ bytesLE 16 parameter ++ bytesLE 32 seed ++ regionBytes region

/-! ### The target-sum code

`v = 62` chunks of `w = 2` bits, with four upper padding bits, and the code is the words of digit sum `T = 110`. Two distinct words of equal sum are incomparable, which is what removes the Winternitz checksum and the reason why we need the counter. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- The retained pair count is `v / 2 = 31`; the new digits are contiguous. -/
def digitsPerHalf : Nat := numChains / 2

/-- Offset of a contiguous two-bit digit. -/
def digitOffset (i : ChainIndex) : Nat := winternitzBits * i.val

/-- `x_i`, the two bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode the concrete little-endian layout: 62 two-bit digits followed by four padding bits. A digest decodes exactly when the padding is clear and the digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.toNat < 2^124 ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and signing. Hashing routines work in any monad with access to `HashSpec`. The experiment samples the master seed and charges every hash call, including repeated calls. Out-of-range branches only make the definitions total; honest algorithms never reach them. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Concrete

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, tw, M) = Truncate_n(H(tw || P || M))`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! ### The index -/

/-- `tau_lay = floor(idx / 2^(sum_{j >= lay} h_j))`. -/
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (totalHeight - heightAbove lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

/-- `e_lay = floor(idx / 2^(sum_{j > lay} h_j)) mod 2^h_lay`. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by
      unfold layerHeight maxLayerHeight; split <;> (try split) <;> omega))⟩

/-! ### The one-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `Chain_{lay,tau,e,i}(P, start, steps, value)`: the step onto position `start + steps + 1` carries tweak position `2^w * i + start + steps`. -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- `X^{lay,tau}_{0,e}`, the one-time leaf: the hash of the `v` public values. -/
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)

/-- `Enc(P, lay, tau, e, M, c)`: hash the message with the counter under the leaf's encoding tweak, and decode. -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (bytesLE 16 message ++ bytesLE 4 counter)
  return TargetSum.decodeDigest digest

/-- `OtsLeaf`: the verifier's leaf, or nothing if the counter does not encode the message. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-! ### A layer -/

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- `TreeFold`: fold a leaf and a path into the layer's root. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)

/-! ### The few-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def ftsLeafOfNat (value : Nat) : FtsLeaf :=
  ⟨value % 2 ^ ftsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The index group of the digest that selects this tree's leaf. -/
def ftsIndexOf (tree : FtsTree) : IndexGroup :=
  tree.castLE (Nat.sub_le ftsTrees 1)

/-- The last index group, the one the digest is resampled to zero and the verifier checks. Its tree is the dropped one. -/
def lastIndexGroup : IndexGroup := ⟨ftsTrees - 1, by decide⟩

/-- `Y^{idx,kappa}_{0,j}`, the hash of one few-time secret. -/
def ftsLeafHash (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.ftsLeaf index tree leaf) (bytesLE 16 secret)

/-- The `k - 1` roots of the forest. -/
def ftsRootsPayload (roots : FtsTree → Digest) : HashInput :=
  (List.ofFn roots).flatMap (bytesLE 16)

/-- The verifier's half of one few-time tree. -/
def ftsFold (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (path : Fin ftsTreeHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← ftsFold parameter index tree leaf path levels value
      let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload sibling current)
      else
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload current sibling)

/-- `FtsRec`: recover the few-time public key from the opened secrets and paths. -/
def ftsRecover (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) : m Digest := do
  let roots ← sequenceFin fun tree => do
    let leaf := leaves (ftsIndexOf tree)
    let value ← ftsLeafHash parameter index tree leaf (secrets tree)
    ftsFold parameter index tree leaf (paths tree) ftsTreeHeight value
  tweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

/-! ### The message digest -/

/-- `rho || 0^16 || m`, what the message digest hashes after the tweak and the parameter. The root slot is zero, so the digest does not bind the root and the signer does not need it; the argument is kept for the shape of the statement and ignored. -/
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 16 randomness ++ bytesLE 16 (0 : Digest) ++ bytesLE 32 message

/-- `Digest(P, m, rho)`, truncated to `h + k * a` bits. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let output ← oracleHash
    (tweakableHashInput parameter .message (messageDigestPayload root message randomness))
  return truncateMessageDigest output

/-- `idx = N mod 2^h`. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- `u_kappa = floor(N / 2^(h + kappa * a)) mod 2^a`. -/
def digestLeaves (digest : MessageDigest) : IndexGroup → FtsLeaf :=
  fun tree => (digest.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight).toFin

/-- The last nine-bit index group and the next three bits must all be zero. -/
def Admissible (digest : MessageDigest) : Prop := digest.extractLsb' 186 12 = 0

instance (digest : MessageDigest) : Decidable (Admissible digest) :=
  inferInstanceAs (Decidable (digest.extractLsb' 186 12 = 0))

/-! ### Verification -/

/-- Read a layer's path, returning zero outside its height. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0

/-- The hypertree walk, from the bottom layer up: `remaining + 1` enters at layer `remaining`, and layer `0`'s fold returns the value compared against the public root. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        verifyLayers parameter index signature remaining root
      else
        pure none

/-- Every layer's counter is below `C_max`. The verifier checks this first, without a query. -/
def CountersInRange (signature : Signature) : Prop :=
  ∀ lay, (signature.layers lay).counter.toNat < encodingAttemptLimit

instance (signature : Signature) : Decidable (CountersInRange signature) :=
  inferInstanceAs (Decidable (∀ lay, (signature.layers lay).counter.toNat < encodingAttemptLimit))

/-- `Ver` after the counter check: recompute the digest, recover the few-time key, walk the layers and compare with the root. -/
def verifyCore (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  if ¬ Admissible digest then return false
  else
    let index := digestIndex digest
    let ftsPublicKey ← ftsRecover publicKey.parameter index (digestLeaves digest)
      signature.ftsSecret signature.ftsPath
    let some root ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey | return false
    return decide (root = publicKey.root)

/-- `Ver(pk, m, sigma)`: reject any counter at or above `C_max`, then verify. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool :=
  if CountersInRange signature then verifyCore publicKey message signature else pure false

/-! ### Building trees

The signer builds every tree it touches exactly once: all leaves in order, then the levels bottom-up,
each left to right. The builders take the secret derivation as an argument, so that the seeded signer
and the proof's table signer share them. -/

/-- Layer `0` holds one tree, at index `0`. -/
def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩

/-- One level of a Merkle tree, `width` nodes left to right, from the level below. Indices outside
the level read zero. -/
def buildLevel (hashNode : Nat → Digest → Digest → m Digest) (width : Nat) (below : Nat → Digest) :
    m (Nat → Digest) := do
  let row ← sequenceFin (n := width) fun nodeIdx =>
    hashNode nodeIdx.val (below (2 * nodeIdx.val)) (below (2 * nodeIdx.val + 1))
  return fun nodeIdx => if h : nodeIdx < width then row ⟨nodeIdx, h⟩ else 0

/-- Levels `1, ..., levels` of a tree of height `height` over `leaves`, bottom-up. The result maps a
level and a node index to the node; level `0` is the leaves. -/
def buildLevels (hashNode : Nat → Nat → Digest → Digest → m Digest) (height : Nat)
    (leaves : Nat → Digest) : Nat → m (Nat → Nat → Digest)
  | 0 => pure fun _ nodeIdx => leaves nodeIdx
  | levels + 1 => do
      let table ← buildLevels hashNode height leaves levels
      let row ← buildLevel (hashNode (levels + 1)) (2 ^ (height - (levels + 1))) (table levels)
      return fun level nodeIdx => if level = levels + 1 then row nodeIdx else table level nodeIdx

/-- The word of all-zero digits: a leaf built with it keeps its secrets. -/
def zeroEncoding : Encoding := fun _ => ⟨0, by decide⟩

/-- One chain of a one-time key: its secret, then all `2^w - 1` steps. Returns the value after
`digit` steps and the endpoint. -/
def buildChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (secret : m Digest) (digit : Nat) : m (Digest × Digest) := do
  let start ← secret
  let value ← chainWalk parameter lay tree leaf chainIdx 0 digit start
  let endpoint ← chainWalk parameter lay tree leaf chainIdx digit (chainLength - 1 - digit) value
  return (value, endpoint)

/-- One leaf of a layer tree: chains `0, ..., v - 1` in order, then the leaf hash. Returns the chain
values at `digits` and the leaf. -/
def buildLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → m Digest) (digits : Encoding) : m ((ChainIndex → Digest) × Digest) := do
  let chains ← sequenceFin fun chainIdx =>
    buildChain parameter lay tree leaf chainIdx (secret chainIdx) (digits chainIdx).val
  let value ← leafHash parameter lay tree leaf fun chainIdx => (chains chainIdx).2
  return (fun chainIdx => (chains chainIdx).1, value)

/-- Build the tree `(lay, tau)` once, keeping everything: the leaves (each with the chain values at
its digits: `digits` for `leaf`, zero elsewhere) and the node table. `buildLayerTree` reads its result off
this table; key generation keeps the top tree's whole table for the cache. -/
def buildLayerTable (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    m ((Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  return (leaves, table)

/-- Build the tree `(lay, tau)` once. Returns the chain values of leaf `leaf` at `digits`, the
authentication path of `leaf` (level `l` holds `X_{l, floor(e / 2^l) xor 1}`) and the root. -/
def buildLayerTree (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    m ((ChainIndex → Digest) × (Nat → Digest) × Digest) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  let values := if h : leaf.val < 2 ^ layerHeight lay then (leaves ⟨leaf.val, h⟩).1 else fun _ => 0
  return (values, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table (layerHeight lay) 0)

/-- Build one few-time tree once: leaves `j = 0, ..., 2^a - 1` (secret, then leaf hash), then the
levels. Returns the secret of `leaf`, its authentication path, and the root. -/
def buildFtsTree (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → m Digest) (leaf : FtsLeaf) : m (Digest × (Nat → Digest) × Digest) := do
  let leaves ← sequenceFin fun leafIdx : FtsLeaf => do
    let value ← secret leafIdx
    let hashed ← ftsLeafHash parameter index tree leafIdx value
    return (value, hashed)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index tree level nodeIdx) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return ((leaves leaf).1, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table ftsTreeHeight 0)

/-- Build the forest `kappa = 0, ..., k - 2` in order, then hash the roots into the few-time public
key. Returns the opened secrets, the paths and the key. -/
def buildForest (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → m Digest) (leaves : IndexGroup → FtsLeaf) :
    m ((FtsTree → Digest) × (FtsTree → Fin ftsTreeHeight → Digest) × Digest) := do
  let trees ← sequenceFin fun tree =>
    buildFtsTree parameter index tree (secret tree) (leaves (ftsIndexOf tree))
  let key ← tweakableHash parameter (.ftsRoots index) (ftsRootsPayload fun tree => (trees tree).2.2)
  return (fun tree => (trees tree).1, fun tree level => (trees tree).2.1 level.val, key)

/-- `OtsSign`'s counter search: the least counter from `counter` on whose encoding decodes, trying at
most `attempts` counters. -/
def encodingSearch (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) : Nat → Nat → m (Option (Counter × Encoding))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => return some (BitVec.ofNat counterBits counter, encoding)
      | none => encodingSearch parameter lay tree leaf message attempts (counter + 1)

/-- One layer's signature before its path is cut to the layer's height: counter, chain values, path. -/
abbrev LayerOutput := Counter × (ChainIndex → Digest) × (Nat → Digest)

/-- The top layer's signature, from the cache: the counter search on `message`, the chain values of
leaf `leaf` (per chain, its secret and then its first `x_i` steps), and the authentication path read
through `topNode` (level `l` holds node `(l, floor(e / 2^l) xor 1)`). The top tree is not rebuilt. -/
def signTopLayer (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → m Digest) (topNode : Nat → Nat → m Digest) (message : Digest) :
    m (Option LayerOutput) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let some (counter, encoding) ←
      encodingSearch parameter topLayer tree leaf message encodingAttemptLimit 0
    | return none
  let values ← sequenceFin fun chainIdx => do
    let start ← secret leaf chainIdx
    chainWalk parameter topLayer tree leaf chainIdx 0 (encoding chainIdx).val start
  let path ← sequenceFin (n := maxLayerHeight) fun level =>
    topNode level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return some (counter, values, fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0)

/-- The hypertree, from the bottom layer up: `remaining + 1` signs `message` at layer `remaining`
(counter search, then the tree built once), and its root is the message of layer `remaining - 1`. The
top layer (`remaining = 0`) is signed from the cache by `signTopLayer`. -/
def signLayers (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) (topNode : Nat → Nat → m Digest) :
    Nat → Digest → m (Option (Layer → LayerOutput))
  | 0, _ => pure (some fun _ => (0, fun _ => 0, fun _ => 0))
  | remaining + 1, message =>
      if hlayer : remaining < numLayers then
        if remaining = 0 then do
          let some output ← signTopLayer parameter index (secret topLayer (treeIndexAt index topLayer))
              topNode message
            | return none
          return some fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)
        else do
          let lay : Layer := ⟨remaining, hlayer⟩
          let tree := treeIndexAt index lay
          let leaf := leafIndexAt index lay
          let some (counter, encoding) ←
              encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
            | return none
          let (values, path, root) ← buildLayerTree parameter lay tree (secret lay tree) leaf encoding
          let some rest ← signLayers parameter index secret topNode remaining root | return none
          return some fun other => if other = lay then (counter, values, path) else rest other
      else
        pure none

/-- Cut a layer's output to the layer's height. -/
def LayerOutput.toSignature (lay : Layer) (output : LayerOutput) : LayerSignature lay :=
  ⟨output.1, output.2.1, fun level => output.2.2 level.val⟩

/-- `Sig` after the digest loop, with the secret derivations and the top tree's nodes as arguments:
build the forest once, then sign the layers from the bottom up. -/
def signFrom (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsLeaf → m Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest)
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, ftsPath, ftsPublicKey) ← buildForest parameter index ftsSecret leaves
  let some parts ← signLayers parameter index otsSecret topNode numLayers ftsPublicKey
    | return none
  return some ⟨randomness, secrets, ftsPath, fun lay => LayerOutput.toSignature lay (parts lay)⟩

attribute [irreducible] verify

/-! ### The builders with paired secrets

The seeded signer derives the secrets of a pair of chains (or of few-time leaves) with one query. These
builders take a getter per pair and walk the pair's two members after it; with table secrets they make
exactly the queries of the per-secret builders above (`Proof/Scheme/PairedEval.lean`). -/

/-- One leaf of a layer tree, with pair getters: per pair, its secrets, chain `2k`, chain `2k + 1`; then the
leaf hash. -/
def buildLeafPaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainPair → m (Digest × Digest)) (digits : Encoding) : m ((ChainIndex → Digest) × Digest) := do
  let pairs ← sequenceFin fun pair : ChainPair => do
    let secrets ← secret pair
    let first ← buildChain parameter lay tree leaf (evenChain pair) (pure secrets.1) (digits (evenChain pair)).val
    let second ← buildChain parameter lay tree leaf (oddChain pair) (pure secrets.2) (digits (oddChain pair)).val
    return (first, second)
  let chains := unpairChains pairs
  let value ← leafHash parameter lay tree leaf fun chainIdx => (chains chainIdx).2
  return (fun chainIdx => (chains chainIdx).1, value)

/-- `buildLayerTable` with pair getters. -/
def buildLayerTablePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    m ((Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeafPaired parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  return (leaves, table)

/-- `buildLayerTree` with pair getters. -/
def buildLayerTreePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    m ((ChainIndex → Digest) × (Nat → Digest) × Digest) := do
  let (leaves, table) ← buildLayerTablePaired parameter lay tree secret leaf digits
  let values := if h : leaf.val < 2 ^ layerHeight lay then (leaves ⟨leaf.val, h⟩).1 else fun _ => 0
  return (values, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table (layerHeight lay) 0)

/-- `buildFtsTree` with pair getters: per pair, its secrets, the leaf hash of `2k`, of `2k + 1`; then the
levels. -/
def buildFtsTreePaired (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsPair → m (Digest × Digest)) (leaf : FtsLeaf) : m (Digest × (Nat → Digest) × Digest) := do
  let pairs ← sequenceFin fun pair : FtsPair => do
    let secrets ← secret pair
    let first ← ftsLeafHash parameter index tree (evenFtsLeaf pair) secrets.1
    let second ← ftsLeafHash parameter index tree (oddFtsLeaf pair) secrets.2
    return ((secrets.1, first), (secrets.2, second))
  let leaves := unpairFtsLeaves pairs
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index tree level nodeIdx) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return ((leaves leaf).1, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table ftsTreeHeight 0)

/-- `buildForest` with pair getters. -/
def buildForestPaired (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsPair → m (Digest × Digest)) (leaves : IndexGroup → FtsLeaf) :
    m ((FtsTree → Digest) × (FtsTree → Fin ftsTreeHeight → Digest) × Digest) := do
  let trees ← sequenceFin fun tree =>
    buildFtsTreePaired parameter index tree (secret tree) (leaves (ftsIndexOf tree))
  let key ← tweakableHash parameter (.ftsRoots index) (ftsRootsPayload fun tree => (trees tree).2.2)
  return (fun tree => (trees tree).1, fun tree level => (trees tree).2.1 level.val, key)

/-- `signTopLayer` with pair getters: per pair, its secrets, the first `x_{2k}` steps of chain `2k`, the
first `x_{2k+1}` steps of chain `2k + 1`. -/
def signTopLayerPaired (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (topNode : Nat → Nat → m Digest) (message : Digest) :
    m (Option LayerOutput) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let some (counter, encoding) ←
      encodingSearch parameter topLayer tree leaf message encodingAttemptLimit 0
    | return none
  let pairs ← sequenceFin fun pair : ChainPair => do
    let secrets ← secret leaf pair
    let first ← chainWalk parameter topLayer tree leaf (evenChain pair) 0 (encoding (evenChain pair)).val secrets.1
    let second ← chainWalk parameter topLayer tree leaf (oddChain pair) 0 (encoding (oddChain pair)).val secrets.2
    return (first, second)
  let values := unpairChains pairs
  let path ← sequenceFin (n := maxLayerHeight) fun level =>
    topNode level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return some (counter, values, fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0)

/-- `signLayers` with pair getters. -/
def signLayersPaired (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainPair → m (Digest × Digest)) (topNode : Nat → Nat → m Digest) :
    Nat → Digest → m (Option (Layer → LayerOutput))
  | 0, _ => pure (some fun _ => (0, fun _ => 0, fun _ => 0))
  | remaining + 1, message =>
      if hlayer : remaining < numLayers then
        if remaining = 0 then do
          let some output ← signTopLayerPaired parameter index (secret topLayer (treeIndexAt index topLayer))
              topNode message
            | return none
          return some fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)
        else do
          let lay : Layer := ⟨remaining, hlayer⟩
          let tree := treeIndexAt index lay
          let leaf := leafIndexAt index lay
          let some (counter, encoding) ←
              encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
            | return none
          let (values, path, root) ← buildLayerTreePaired parameter lay tree (secret lay tree) leaf encoding
          let some rest ← signLayersPaired parameter index secret topNode remaining root | return none
          return some fun other => if other = lay then (counter, values, path) else rest other
      else
        pure none

/-- `signFrom` with pair getters. -/
def signFromPaired (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsPair → m (Digest × Digest))
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainPair → m (Digest × Digest))
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, ftsPath, ftsPublicKey) ← buildForestPaired parameter index ftsSecret leaves
  let some parts ← signLayersPaired parameter index otsSecret topNode numLayers ftsPublicKey
    | return none
  return some ⟨randomness, secrets, ftsPath, fun lay => LayerOutput.toSignature lay (parts lay)⟩

end Concrete

def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) : m Randomness := do
  return truncateHash (← Concrete.oracleHash (randomizerHashInput parameter seed message trial))

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter
  root : Digest

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The two secrets of one derivation answer: its low and its high 16 bytes. -/
def splitSecrets (output : HashOutput) : Digest × Digest :=
  (truncateHash output, output.extractLsb' digestBits digestBits)

/-- `sk_{lay,tau,e,2k}` and `sk_{lay,tau,e,2k+1}`, derived from the seed with one query. -/
def otsSecret (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (pair : ChainPair) : m (Digest × Digest) := do
  return splitSecrets (← Concrete.oracleHash (keygenHashInput parameter (.ots lay tree leaf pair) seed))

/-- `s^{idx,kappa}_{2k}` and `s^{idx,kappa}_{2k+1}`, derived from the seed with one query. -/
def ftsSecret (parameter : PublicParameter) (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (pair : FtsPair) : m (Digest × Digest) := do
  return splitSecrets (← Concrete.oracleHash (keygenHashInput parameter (.fts index tree pair) seed))

/-- The mask domain of node `(l, j)`. The signer only asks for nodes of the cached region, where the
reductions are the identity. -/
def maskDomain (level nodeIdx : Nat) : KeygenDomain :=
  .mask ⟨level % maxLayerHeight, Nat.mod_lt _ (by decide)⟩ ⟨nodeIdx % 2 ^ maxLayerHeight, Nat.mod_lt _ (by decide)⟩

/-- `mask(l, j)`, the mask of the cached top-tree node `(l, j)`, derived from the seed. -/
def maskSecret (parameter : PublicParameter) (seed : MasterSeed) (level nodeIdx : Nat) : m Digest :=
  deriveKey parameter (maskDomain level nodeIdx) seed

/-- Mask the top tree's node table below the root, level by level and left to right, deriving each mask
in turn. -/
def maskRegion (parameter : PublicParameter) (seed : MasterSeed) (table : Nat → Nat → Digest) :
    m TopRegion :=
  do
  let rows ← sequenceFin fun level : Fin maxLayerHeight => do
    let row ← sequenceFin fun nodeIdx : Fin (2 ^ (maxLayerHeight - level.val)) => do
      let mask ← maskSecret parameter seed level.val nodeIdx.val
      return table level.val nodeIdx.val ^^^ mask
    return fun nodeIdx : Nat => if h : nodeIdx < 2 ^ (maxLayerHeight - level.val) then row ⟨nodeIdx, h⟩ else 0
  return fun level nodeIdx => rows level nodeIdx.val

/-- The top tree's node `(l, j)` as the signer reads it: the cached masked node, unmasked with a freshly
derived mask. -/
def cachedTopNode (parameter : PublicParameter) (seed : MasterSeed) (cache : TopCache) (level nodeIdx : Nat) :
    m Digest := do
  let mask ← maskSecret parameter seed level nodeIdx
  return cache.node level nodeIdx ^^^ mask

/-- Build the top tree from the supplied seed (its root is the public key), mask its nodes below the root,
and authenticate the masked region with the MAC. There is no parameter derivation: `P = 0`. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × TopCache × SecretKey) := do
  let (_, table) ← buildLayerTablePaired 0 topLayer rootTree (otsSecret 0 seed topLayer rootTree)
    ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  let root := table (layerHeight topLayer) 0
  let region ← maskRegion 0 seed table
  let tag ← oracleHash (macHashInput 0 seed region)
  return (⟨root, 0⟩, ⟨tag, region⟩, ⟨seed, 0, root⟩)

def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none

/-- Derive trials in increasing order, stopping at the first admissible digest. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) : Nat → Nat →
    m (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.parameter secretKey.seed message (BitVec.ofNat 32 trial)
      match ← signAttempt secretKey message randomness with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => signDigestLoop secretKey message attempts (trial + 1)

/-- `Sig(sk, m)` after the MAC check: the digest loop, the forest built once, then the layers from the
bottom up, each a counter search followed by its tree built once, and the top layer from the cache. -/
def signChecked (secretKey : SecretKey) (cache : TopCache) (message : Message) : m (Option Signature) := do
  let some (randomness, index, leaves) ← signDigestLoop secretKey message digestAttemptLimit 0
    | return none
  signFromPaired secretKey.parameter index (ftsSecret secretKey.parameter secretKey.seed index)
    (otsSecret secretKey.parameter secretKey.seed)
    (cachedTopNode secretKey.parameter secretKey.seed cache) randomness leaves

/-- `Sig(sk, cache, m)`: check the cache's MAC first (one query; a mismatch fails), then sign. -/
def sign (secretKey : SecretKey) (cache : TopCache) (message : Message) : m (Option Signature) := do
  let tag ← oracleHash (macHashInput secretKey.parameter secretKey.seed cache.region)
  if tag = cache.tag then signChecked secretKey cache message else return none

end Seeded

end SigGolfCandidate.Base4Candidate.Ideal

namespace SigGolfCandidate.Base4Candidate

/-- The typed ideal model uses exactly the counted decoder, not a looser code. -/
theorem ideal_decoder_eq : Ideal.TargetSum.decodeDigest = decode := rfl

end SigGolfCandidate.Base4Candidate

namespace SigGolfCandidate.Base4Candidate.Ideal.OtsCode

abbrev Valid := Base4Candidate.Valid
abbrev decode := Base4Candidate.decode

theorem Valid_def (x : Encoding) : Valid x = TargetSum.Valid x := rfl
theorem decode_def (d : Digest) : decode d = TargetSum.decodeDigest d := rfl

theorem decode_valid {d : Digest} {x : Encoding} (h : decode d = some x) : Valid x :=
  Base4Candidate.decode_valid h

theorem decode_injective {a b : Digest} {x : Encoding}
    (ha : decode a = some x) (hb : decode b = some x) : a = b :=
  Base4Candidate.decode_injective ha hb

theorem eq_of_le_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y :=
  Base4Candidate.eq_of_le_of_valid hx hy hle

def defaultWord : Encoding :=
  fun i => if i.val < 36 then ⟨3, by decide⟩ else if i.val = 36 then ⟨2, by decide⟩ else ⟨0, by decide⟩

theorem defaultWord_valid : Valid defaultWord := by
  change (∑ i : Fin 62, (defaultWord i).val) = 110
  simp only [defaultWord, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

def signingSteps (x : Encoding) : Nat := ∑ i, (x i).val

abbrev UnitNeighborAt := Base4Candidate.UnitNeighborAt
noncomputable abbrev unitNeighbors := Base4Candidate.unitNeighbors
noncomputable abbrev allUnitNeighbors := Base4Candidate.allUnitNeighbors
abbrev unitNeighborBound := Base4Candidate.unitNeighborBound
abbrev neighborBound := Base4Candidate.neighborBound

theorem UnitNeighborAt.ne {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) : candidate ≠ reference :=
  Base4Candidate.UnitNeighborAt.ne h

theorem UnitNeighborAt.lowered_unique {reference candidate : Encoding} {left right : ChainIndex}
    (hl : UnitNeighborAt reference candidate left) (hr : UnitNeighborAt reference candidate right) : left = right :=
  Base4Candidate.UnitNeighborAt.lowered_unique hl hr

theorem mem_unitNeighbors {reference candidate : Encoding} {lowered : ChainIndex} :
    candidate ∈ unitNeighbors reference lowered ↔ UnitNeighborAt reference candidate lowered :=
  Base4Candidate.mem_unitNeighbors

theorem mem_allUnitNeighbors {reference candidate : Encoding} :
    candidate ∈ allUnitNeighbors reference ↔ ∃ lowered, UnitNeighborAt reference candidate lowered :=
  Base4Candidate.mem_allUnitNeighbors

theorem unitNeighbors_card_le (reference : Encoding) (lowered : ChainIndex) :
    (unitNeighbors reference lowered).card ≤ unitNeighborBound :=
  Base4Candidate.unitNeighbors_card_le reference lowered

theorem allUnitNeighbors_card_le (reference : Encoding) :
    (allUnitNeighbors reference).card ≤ neighborBound :=
  Base4Candidate.allUnitNeighbors_card_le reference

theorem unitNeighborBound_eq : unitNeighborBound = 61 := rfl
theorem neighborBound_eq : neighborBound = 3782 := rfl

theorem two_le_chainLength : 2 ≤ chainLength := by decide
theorem two_le_numChains : 2 ≤ numChains := by decide

theorem chainTweakPosition_lt (i : ChainIndex) (step : ChainStep) :
    chainLength*i.val+step.val < 2^32 := by
  have hi := i.isLt
  have hs := step.isLt
  simp only [numChains, chainLength, winternitzBits] at *
  omega

theorem chainTweakPosition_injective {a b : ChainIndex} {sa sb : ChainStep}
    (h : chainLength*a.val+sa.val = chainLength*b.val+sb.val) : a = b ∧ sa = sb := by
  have ha := sa.isLt
  have hb := sb.isLt
  simp only [chainLength, winternitzBits] at *
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

end SigGolfCandidate.Base4Candidate.Ideal.OtsCode

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete
abbrev digestBytes (value : Digest) : HashInput := bytesLE 16 value
end SigGolfCandidate.Base4Candidate.Ideal.Concrete

/-! Alternate proof port from the original promoted FORS baseline: Proof/Scheme/Arith.lean -/
section AlternateProofPort0
/-!
# Index arithmetic

The facts every Merkle argument needs: a node's index one level up is half of it, the sibling of an
index is that index with its low bit flipped, and the bit the fold tests is that low bit.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal

/-- The statement writes `Nat.xor`, the bit library `^^^`; rewriting needs them bridged. -/
theorem nat_xor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl

theorem div_pow_succ (x k : Nat) : x / 2 ^ (k + 1) = x / 2 ^ k / 2 := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem xor_one_div_two (j : Nat) : Nat.xor (2 * j) 1 / 2 = j := by
  rw [nat_xor_eq, show (2 : Nat) = 2 ^ 1 from rfl, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib, Nat.shiftRight_eq_div_pow]
  simp

theorem xor_one_two_mul (j : Nat) : Nat.xor (2 * j) 1 = 2 * j + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => rw [nat_xor_eq]; simp [Nat.testBit_zero]
  | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, xor_one_div_two, Nat.mul_add_div (by omega)]
      simp

theorem xor_one_two_mul_add_one (j : Nat) : Nat.xor (2 * j + 1) 1 = 2 * j := by
  rw [← xor_one_two_mul j, nat_xor_eq, nat_xor_eq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- An index and its sibling are the two children of the index one level up; the low bit says which
of them is the left one. -/
theorem index_sibling_cases (c : Nat) :
    ∃ j, (c = 2 * j ∧ Nat.xor c 1 = 2 * j + 1 ∧ c % 2 = 0)
      ∨ (c = 2 * j + 1 ∧ Nat.xor c 1 = 2 * j ∧ c % 2 = 1) := by
  obtain ⟨j, hj⟩ : ∃ j, c / 2 = j := ⟨c / 2, rfl⟩
  have hdm := Nat.div_add_mod c 2
  rcases Nat.mod_two_eq_zero_or_one c with hmod | hmod
  · have hc : c = 2 * j := by omega
    exact ⟨j, Or.inl ⟨hc, by rw [hc]; exact xor_one_two_mul j, hmod⟩⟩
  · have hc : c = 2 * j + 1 := by omega
    exact ⟨j, Or.inr ⟨hc, by rw [hc]; exact xor_one_two_mul_add_one j, hmod⟩⟩

theorem testBit_iff_div_mod (x k : Nat) : x.testBit k = true ↔ x / 2 ^ k % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

end SigGolfCandidate.Base4Candidate.Ideal

end AlternateProofPort0

/-! Alternate proof port from the original promoted FORS baseline: Proof/Scheme/Bytes.lean -/
section AlternateProofPort1

/-!
# The byte encoding is injective

Domain separation is what keeps a query from bearing on two structural positions at once, and it
rests on the tweak bytes determining the position. That in turn rests on the fixed-width
little-endian encoding being injective, which is what this module proves.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal

theorem bytesLE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by
  simp [bytesLE]

/-- A bit vector determines the natural it encodes, below the wrap. -/
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

/-- A 40-bit tree field is determined by its two serialized pieces. -/
theorem tree_eq_of_pieces {x y : BitVec 40} (hhigh : x.extractLsb' 32 8 = y.extractLsb' 32 8)
    (hlow : x.extractLsb' 0 32 = y.extractLsb' 0 32) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hsmall : i < 32
  · have h := congrArg (fun b : BitVec 32 => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hsmall] using h
  · have h := congrArg (fun b : BitVec 8 => b.getLsbD (i - 32)) hhigh
    have hlt : i - 32 < 8 := by omega
    have hsum : 32 + (i - 32) = i := by omega
    simpa [BitVec.getLsbD_extractLsb', hlt, hsum] using h

theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) : t1 = t2 := by
  obtain ⟨tag1, layer1, tree1, position1, index1⟩ := t1
  obtain ⟨tag2, layer2, tree2, position2, index2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, hindex⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, htree⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hposition⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hhigh⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨htag, hlayer⟩ := List.append_inj' h (by simp [bytesLE_length])
  have htag := List.append_right_injective [protocolDomainSep] htag
  simp only [bytesLE_injective htag, bytesLE_injective hlayer,
    tree_eq_of_pieces (bytesLE_injective hhigh) (bytesLE_injective htree),
    bytesLE_injective hposition, bytesLE_injective hindex]

theorem tweakBytes_eq_iff {d1 d2 : HashDomain} :
    tweakBytes d1 = tweakBytes d2 ↔ hashDomainFields d1 = hashDomainFields d2 :=
  ⟨fun h => fieldBytes_injective h, fun h => by rw [tweakBytes, tweakBytes, h]⟩

private theorem layer_le : numLayers ≤ 2 ^ 8 := by decide
private theorem tree_le : 2 ^ totalHeight ≤ 2 ^ 40 := Nat.pow_le_pow_right (by omega) (by decide)
private theorem index_le : 2 ^ totalHeight ≤ 2 ^ 40 := tree_le
private theorem leaf_le : 2 ^ maxLayerHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by decide)
private theorem ftsTree_le : ftsTrees - 1 ≤ 2 ^ 8 := by decide
private theorem ftsLeaf_le : 2 ^ ftsTreeHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by decide)

/-- Every field a tweak carries is below the width that encodes it. The `Fin`-valued ones are by
construction; the two tree recursions take their level and node as naturals, so those are the only
positions that need saying, and honest use keeps them far below `2^32`. -/
def HashDomain.InRange : HashDomain → Prop
  | .node _ _ level nodeIdx => level < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
  | .ftsNode _ _ level nodeIdx => level < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
  | _ => True

theorem fin_of_ofNat_eq {w n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ w)
    (h : BitVec.ofNat w a.val = BitVec.ofNat w b.val) : a = b :=
  Fin.ext (ofNat_inj_of_lt (Nat.lt_of_lt_of_le a.isLt hn) (Nat.lt_of_lt_of_le b.isLt hn) h)

/-- **Domain separation.** A tweak names one structural position: two in-range domains with the same
tweak bytes are the same domain. This is what stops one query from bearing on two positions, and so
what keeps an inversion at `2^-n` per query with no multi-target factor. -/
theorem tweakBytes_injective {d1 d2 : HashDomain} (h1 : d1.InRange) (h2 : d2.InRange)
    (h : tweakBytes d1 = tweakBytes d2) : d1 = d2 := by
  rw [tweakBytes_eq_iff] at h
  cases d1 <;> cases d2 <;>
    simp_all [hashDomainFields, tweakFields, HashDomain.InRange, TweakFields.mk.injEq]
  case chain.chain lay1 tree1 leaf1 i1 s1 lay2 tree2 leaf2 i2 s2 =>
    obtain ⟨hl, ht, hp, hlf⟩ := h
    have hpos := ofNat_inj_of_lt (OtsCode.chainTweakPosition_lt i1 s1) (OtsCode.chainTweakPosition_lt i2 s2) hp
    obtain ⟨hi, hs⟩ := OtsCode.chainTweakPosition_injective hpos
    exact ⟨fin_of_ofNat_eq layer_le hl, fin_of_ofNat_eq tree_le ht, fin_of_ofNat_eq leaf_le hlf, hi, hs⟩
  case leaf.leaf => exact ⟨fin_of_ofNat_eq layer_le h.1, fin_of_ofNat_eq tree_le h.2.1,
      fin_of_ofNat_eq leaf_le h.2.2⟩
  case node.node lay1 tree1 level1 nodeIdx1 lay2 tree2 level2 nodeIdx2 =>
    exact ⟨fin_of_ofNat_eq layer_le h.1, fin_of_ofNat_eq tree_le h.2.1,
      ofNat_inj_of_lt h1.1 h2.1 h.2.2.1, ofNat_inj_of_lt h1.2 h2.2 h.2.2.2⟩
  case encoding.encoding => exact ⟨fin_of_ofNat_eq layer_le h.1, fin_of_ofNat_eq tree_le h.2.1,
      fin_of_ofNat_eq leaf_le h.2.2⟩
  case ftsLeaf.ftsLeaf => exact ⟨fin_of_ofNat_eq index_le h.2.1, fin_of_ofNat_eq ftsTree_le h.1,
      fin_of_ofNat_eq ftsLeaf_le h.2.2⟩
  case ftsNode.ftsNode =>
    exact ⟨fin_of_ofNat_eq index_le h.2.1, fin_of_ofNat_eq ftsTree_le h.1,
      ofNat_inj_of_lt h1.1 h2.1 h.2.2.1, ofNat_inj_of_lt h1.2 h2.2 h.2.2.2⟩
  case ftsRoots.ftsRoots => exact fin_of_ofNat_eq index_le h

theorem tweakBytes_length (domain : HashDomain) : (tweakBytes domain).length = 16 := by
  simp [tweakBytes, fieldBytes, bytesLE_length]

/-- What the reduction reads off a query: the tweak is a fixed-length initialPart of the hashed input, so
the input determines both the position it names and the payload. -/
theorem tweakableHashInput_injective (parameter : PublicParameter) {d1 d2 : HashDomain}
    (h1 : d1.InRange) (h2 : d2.InRange) {payload1 payload2 : HashInput}
    (h : tweakableHashInput parameter d1 payload1 = tweakableHashInput parameter d2 payload2) :
    d1 = d2 ∧ payload1 = payload2 := by
  simp only [tweakableHashInput] at h
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact ⟨tweakBytes_injective h1 h2 htweak, hpayload⟩

theorem tweakableHashInput_ne_message (parameter : PublicParameter) (domain : HashDomain)
    (hdomain : domain ≠ .message) (payload messagePayload : HashInput) :
    tweakableHashInput parameter domain payload ≠
      tweakableHashInput parameter .message messagePayload := by
  intro hinput
  simp only [tweakableHashInput] at hinput
  obtain ⟨hprefix, _⟩ := List.append_inj hinput
    (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  apply hdomain
  cases domain <;>
    simp_all [tweakBytes_eq_iff, hashDomainFields, tweakFields, TweakFields.mk.injEq]

/-! ### Payloads

A node's payload is its two children, a leaf's is its `v` chain endpoints, and a few-time key's is
its `k-1` roots. Each is injective, which is what lets the extraction argument descend: if an
adversary's payload hashes to an honest value, either it *is* the honest payload, and then its parts
are the honest parts, or the hash was hit. -/

theorem digestBytes_injective {x y : Digest} (h : Concrete.digestBytes x = Concrete.digestBytes y) :
    x = y :=
  bytesLE_injective h

theorem digestBytes_length (x : Digest) : (Concrete.digestBytes x).length = 16 :=
  bytesLE_length 16 x

theorem nodePayload_injective {left right left' right' : Digest}
    (h : Concrete.nodePayload left right = Concrete.nodePayload left' right') :
    left = left' ∧ right = right' := by
  obtain ⟨hleft, hright⟩ := List.append_inj h (by rw [digestBytes_length, digestBytes_length])
  exact ⟨digestBytes_injective hleft, digestBytes_injective hright⟩

/-- A concatenation of fixed-length blocks determines the blocks. -/
theorem flatMap_ofFn_injective {α β : Type} (g : α → List β) (len : Nat)
    (hlen : ∀ a, (g a).length = len) (hinj : ∀ a b, g a = g b → a = b) :
    ∀ {n : Nat} {f f' : Fin n → α},
      (List.ofFn f).flatMap g = (List.ofFn f').flatMap g → f = f' := by
  intro n
  induction n with
  | zero => intro f f' _; funext i; exact i.elim0
  | succ n ih =>
      intro f f' h
      simp only [List.ofFn_succ, List.flatMap_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (by rw [hlen, hlen])
      have hzero := hinj _ _ hhead
      have hsucc := ih htail
      funext i
      cases i using Fin.cases with
      | zero => exact hzero
      | succ j => exact congrFun hsucc j

/-- A one-time signature's payload is its `v` endpoints, and the concatenation determines them. -/
theorem leafPayload_injective {endpoints endpoints' : ChainIndex → Digest}
    (h : Concrete.leafPayload endpoints = Concrete.leafPayload endpoints') :
    endpoints = endpoints' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h

/-- A few-time public key's payload is its `k - 1` roots. -/
theorem ftsRootsPayload_injective {roots roots' : FtsTree → Digest}
    (h : Concrete.ftsRootsPayload roots = Concrete.ftsRootsPayload roots') : roots = roots' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h

end SigGolfCandidate.Base4Candidate.Ideal

end AlternateProofPort1

/-! Alternate proof port from the original promoted FORS baseline: Proof/Scheme/PairedEquations.lean -/
section AlternateProofPort2

/-!
# The paired builders with table secrets

With table secrets, the paired builders make exactly the queries of the per-secret builders: a pair's
getter is a pure read, and walking member `2k` then member `2k + 1` for `k = 0, 1, …` walks every member in
order (`sequenceFin_pairs`). These equalities let the seeded signer, which derives a pair of secrets with
one query, erase to the proof's table signer, which uses the per-secret builders.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

open OracleComp

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Spread pairs indexed by `Fin n` over `Fin N`, `N = 2n`: even members take the first component. -/
def unpairFin {α : Type} {n N : Nat} (hN : N = 2 * n) (p : Fin n → α × α) (i : Fin N) : α :=
  if i.val % 2 = 0 then (p ⟨i.val / 2, by have := i.isLt; omega⟩).1 else (p ⟨i.val / 2, by have := i.isLt; omega⟩).2

/-- The pair computation of a member computation. -/
def pairStep {α : Type} {n N : Nat} (hN : N = 2 * n) (f : Fin N → m α) (k : Fin n) : m (α × α) := do
  let a ← f ⟨2 * k.val, by have := k.isLt; omega⟩
  let b ← f ⟨2 * k.val + 1, by have := k.isLt; omega⟩
  pure (a, b)

theorem sequenceFin_pairs {α : Type} (n : Nat) :
    ∀ (N : Nat) (hN : N = 2 * n) (f : Fin N → m α),
      sequenceFin f = unpairFin hN <$> sequenceFin (pairStep hN f) := by
  induction n with
  | zero =>
      intro N hN f
      subst hN
      simp only [Nat.mul_zero, sequenceFin, map_pure]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      intro N hN f
      obtain rfl : N = (2 * n + 1) + 1 := by omega
      have htail := ih (2 * n) rfl (fun i => f i.succ.succ)
      conv_lhs => simp only [sequenceFin]
      rw [htail]
      conv_rhs => simp only [sequenceFin]
      simp only [pairStep, map_bind, bind_assoc, map_pure, pure_bind, bind_map_left]
      have e0 : (⟨2 * (0 : Fin (n + 1)).val, by omega⟩ : Fin (2 * n + 1 + 1)) = 0 := rfl
      have e1 : (⟨2 * (0 : Fin (n + 1)).val + 1, by omega⟩ : Fin (2 * n + 1 + 1)) = (0 : Fin (2 * n + 1)).succ := rfl
      rw [e0, e1]
      apply bind_congr
      intro a
      apply bind_congr
      intro b
      have hpairs : (pairStep (n := n) (N := 2 * n) rfl fun i => f i.succ.succ) =
          (fun k : Fin n => do
            let a ← f ⟨2 * (k.succ).val, by have := k.isLt; omega⟩
            let b ← f ⟨2 * (k.succ).val + 1, by have := k.isLt; omega⟩
            pure (a, b)) := by
        funext k
        simp only [pairStep]
        congr 2
      rw [hpairs]
      apply bind_congr
      intro rest
      congr 1
      funext i
      obtain ⟨i, hi⟩ := i
      match i, hi with
      | 0, _ =>
          rw [show (⟨0, by omega⟩ : Fin (2 * n + 1 + 1)) = 0 from rfl, Fin.cases_zero]
          simp [unpairFin]
      | 1, _ =>
          rw [show (⟨1, by omega⟩ : Fin (2 * n + 1 + 1)) = (0 : Fin (2 * n + 1)).succ from rfl, Fin.cases_succ,
            Fin.cases_zero]
          simp [unpairFin]
      | j + 2, hj =>
          rw [show (⟨j + 2, hj⟩ : Fin (2 * n + 1 + 1)) = (⟨j, by omega⟩ : Fin (2 * n)).succ.succ from rfl,
            Fin.cases_succ, Fin.cases_succ]
          have hidx : (⟨(j + 2) / 2, by omega⟩ : Fin (n + 1)) = (⟨j / 2, by omega⟩ : Fin n).succ :=
            Fin.ext (by simp only [Fin.val_succ]; omega)
          unfold unpairFin
          simp only [Fin.val_succ, show j + 1 + 1 = j + 2 from rfl, show (j + 2) % 2 = j % 2 by omega, hidx,
            Fin.cases_succ]

theorem numChains_eq_two_mul : numChains = 2 * (numChains / 2) := rfl

theorem ftsLeaves_eq_two_mul : 2 ^ ftsTreeHeight = 2 * (2 ^ (ftsTreeHeight - 1)) := rfl

theorem unpairChains_eq {α : Type} (pairs : ChainPair → α × α) :
    unpairChains pairs = unpairFin numChains_eq_two_mul pairs := by
  funext i
  rfl

theorem unpairFtsLeaves_eq {α : Type} (pairs : FtsPair → α × α) :
    unpairFtsLeaves pairs = unpairFin ftsLeaves_eq_two_mul pairs := by
  funext i
  rfl

variable [HasQuery HashSpec m]

/-- Chain secrets of a table, read per pair. -/
def pairOf (secret : ChainIndex → Digest) (pair : ChainPair) : Digest × Digest :=
  (secret (evenChain pair), secret (oddChain pair))

/-- Few-time secrets of a table, read per pair. -/
def ftsPairOf (secret : FtsLeaf → Digest) (pair : FtsPair) : Digest × Digest :=
  (secret (evenFtsLeaf pair), secret (oddFtsLeaf pair))

theorem buildLeafPaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (digits : Encoding) :
    (buildLeafPaired parameter lay tree leaf (fun pair => pure (pairOf secret pair)) digits : m _) =
      buildLeaf parameter lay tree leaf (fun chainIdx => pure (secret chainIdx)) digits := by
  unfold buildLeafPaired buildLeaf
  rw [sequenceFin_pairs (numChains / 2) numChains numChains_eq_two_mul, bind_map_left]
  simp only [pure_bind, unpairChains_eq]
  rfl

theorem buildLayerTablePaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (digits : Encoding) :
    (buildLayerTablePaired parameter lay tree (fun leaf pair => pure (pairOf (secret leaf) pair)) leaf digits : m _) =
      buildLayerTable parameter lay tree (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits := by
  unfold buildLayerTablePaired buildLayerTable
  simp only [buildLeafPaired_pure]

theorem buildLayerTreePaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (digits : Encoding) :
    (buildLayerTreePaired parameter lay tree (fun leaf pair => pure (pairOf (secret leaf) pair)) leaf digits : m _) =
      buildLayerTree parameter lay tree (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits := by
  unfold buildLayerTreePaired
  rw [buildLayerTablePaired_pure]
  unfold buildLayerTree buildLayerTable
  simp only [bind_assoc, pure_bind]

theorem buildFtsTreePaired_pure (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (leaf : FtsLeaf) :
    (buildFtsTreePaired parameter index tree (fun pair => pure (ftsPairOf secret pair)) leaf : m _) =
      buildFtsTree parameter index tree (fun leaf => pure (secret leaf)) leaf := by
  unfold buildFtsTreePaired buildFtsTree
  rw [sequenceFin_pairs (2 ^ (ftsTreeHeight - 1)) (2 ^ ftsTreeHeight) ftsLeaves_eq_two_mul, bind_map_left]
  simp only [pure_bind]
  have hstep : (fun pair : FtsPair => (do
      let first ← ftsLeafHash parameter index tree (evenFtsLeaf pair) (ftsPairOf secret pair).1
      let second ← ftsLeafHash parameter index tree (oddFtsLeaf pair) (ftsPairOf secret pair).2
      return (((ftsPairOf secret pair).1, first), ((ftsPairOf secret pair).2, second)) : m _)) =
      pairStep ftsLeaves_eq_two_mul (fun leafIdx : FtsLeaf => (do
        let hashed ← ftsLeafHash parameter index tree leafIdx (secret leafIdx)
        return (secret leafIdx, hashed) : m _)) := by
    funext pair
    simp only [pairStep, pure_bind, bind_assoc]
    rfl
  rw [hstep]
  simp only [unpairFtsLeaves_eq]

theorem buildForestPaired_pure (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) (leaves : IndexGroup → FtsLeaf) :
    (buildForestPaired parameter index (fun tree pair => pure (ftsPairOf (secret tree) pair)) leaves : m _) =
      buildForest parameter index (fun tree leaf => pure (secret tree leaf)) leaves := by
  unfold buildForestPaired buildForest
  simp only [buildFtsTreePaired_pure]

theorem signTopLayerPaired_pure (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → Digest) (topNode : Nat → Nat → m Digest) (message : Digest) :
    signTopLayerPaired parameter index (fun leaf pair => pure (pairOf (secret leaf) pair)) topNode message =
      signTopLayer parameter index (fun leaf chainIdx => pure (secret leaf chainIdx)) topNode message := by
  unfold signTopLayerPaired signTopLayer
  apply bind_congr
  intro search
  rcases search with _ | ⟨counter, encoding⟩
  · rfl
  · dsimp only
    simp only [pure_bind]
    rw [sequenceFin_pairs (numChains / 2) numChains numChains_eq_two_mul, bind_map_left]
    simp only [unpairChains_eq]
    rfl

theorem signLayersPaired_pure (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (topNode : Nat → Nat → m Digest)
    (remaining : Nat) (message : Digest) :
    signLayersPaired parameter index (fun lay tree leaf pair => pure (pairOf (secret lay tree leaf) pair)) topNode
        remaining message =
      signLayers parameter index (fun lay tree leaf chainIdx => pure (secret lay tree leaf chainIdx)) topNode
        remaining message := by
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
      simp only [signLayersPaired, signLayers]
      split
      · split
        · rw [signTopLayerPaired_pure]
        · apply bind_congr
          intro search
          rcases search with _ | ⟨counter, encoding⟩
          · rfl
          · dsimp only
            rw [buildLayerTreePaired_pure (secret := secret _ _)]
            apply bind_congr
            intro built
            rw [ih]
      · rfl

theorem signFromPaired_pure (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsLeaf → Digest) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (topNode : Nat → Nat → m Digest) (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    signFromPaired parameter index (fun tree pair => pure (ftsPairOf (ftsSecret tree) pair))
        (fun lay tree leaf pair => pure (pairOf (otsSecret lay tree leaf) pair)) topNode randomness leaves =
      signFrom parameter index (fun tree leaf => pure (ftsSecret tree leaf))
        (fun lay tree leaf chainIdx => pure (otsSecret lay tree leaf chainIdx)) topNode randomness leaves := by
  unfold signFromPaired signFrom
  rw [buildForestPaired_pure]
  apply bind_congr
  rintro ⟨secrets, path, key⟩
  dsimp only
  rw [signLayersPaired_pure]

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateProofPort2

/-! Alternate proof port from the original promoted FORS baseline: Proof/Ots/Chain.lean -/
section AlternateProofPort3

/-!
# The hash chain

Walking `a` steps from `start` and then `b` more is walking `a + b` steps. Everything the one-time
signature needs follows: the verifier's half of a chain, `recoverChain`, composes with the signer's
half to reach the public value the leaf is built from.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]

/-- Steps compose. Positions past the last chain step are the constant `0` on both sides, so no
range hypothesis is needed. -/
theorem chainWalk_add (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    chainWalk (m := m) parameter lay tree leaf chainIdx start (a + b) value
      = (do
          let mid ← chainWalk (m := m) parameter lay tree leaf chainIdx start a value
          chainWalk parameter lay tree leaf chainIdx (start + a) b mid) := by
  induction b with
  | zero => simp [chainWalk]
  | succ b ih =>
      show chainWalk (m := m) parameter lay tree leaf chainIdx start (a + b + 1) value = _
      simp only [chainWalk, ih, bind_assoc, Nat.add_assoc]

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateProofPort3

/-! Alternate proof port from the original promoted FORS baseline: Statement.lean -/
section AlternateRecoveryPort0

/-!
# SPHINCS+ security statement

Strong unforgeability under chosen-message attacks (SUF-CMA) in the classical random-oracle model, with a 127-bit security target for the scheme in `Scheme.lean`.
-/

open OracleComp OracleSpec ENNReal

namespace SigGolfCandidate.Base4Candidate.Ideal

/-! ## The security experiment -/

/-- A claimed forgery: a message and a signature. -/
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

/-- A signing request of the proof's ideal games is a message alone, and the answer is a signature or `none` if the signer fails. -/
abbrev SigningSpec := Message →ₒ Option Signature

/-- A signing request of the experiment: a message and a cache, both chosen by the adversary. The signer
checks the cache's MAC and reads the top layer's path from it. -/
structure SigningRequest where
  message : Message
  cache : TopCache
deriving DecidableEq

/-- The experiment's signing oracle: a request is answered by a signature or `none` if the signer fails
(including a cache that fails its MAC check). -/
abbrev RequestSpec := SigningRequest →ₒ Option Signature

namespace SigningTranscript

/-- A signing transcript is valid exactly when the key signed at most `q_s` messages. Repeated messages receive the same signature or failure. -/
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The signer returned the claimed forgery exactly when the transcript contains the same message answered by the same signature. A different signature for a signed message is therefore a valid strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

namespace RequestTranscript

/-- A transcript is valid exactly when the key answered at most `q_s` requests, failed ones included. -/
def Valid (log : QueryLog RequestSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog RequestSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The signer returned the claimed forgery exactly when some request for the same message, with any
cache, was answered by the same signature. A different signature for a signed message is a valid strong
forgery. -/
def Contains (log : QueryLog RequestSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog RequestSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature))

end RequestTranscript

namespace Security

/-- A probabilistic adaptive adversary with private randomness and access to hashing and signing. It
receives the public key and the published cache, and chooses the cache of every signing request. -/
structure Adversary where
  main : PublicKey → TopCache → OracleComp (OracleWorld + RequestSpec) Forgery

/-- Record each signing request and its answer. -/
def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl RequestSpec (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request.cache request.message : OracleComp HashSpec _)

/-- Sample the master seed, then run all parties with one shared hash oracle. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, cache, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog RequestSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) + signingOracle sk) (adversary.main pk cache)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (RequestTranscript.Valid log ∧ ¬RequestTranscript.Contains log forgery) && verified

/-- Forward private sampling for free; answer hash queries consistently and count every call, including cache hits. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Run the game from an empty random-oracle cache, recording success and the total number of hash calls. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability of a successful forgery. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]

/-- Every execution uses at most `q` hash calls, including key generation, signing, and verification. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- Every adversary with nonzero query budget `q` wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

/-- The security claim. -/
abbrev SigGolfCandidate.Base4Candidate.IdealStatement : Prop := Security.HasClassicalSecurityBits 127

end SigGolfCandidate.Base4Candidate.Ideal

end AlternateRecoveryPort0

/-! Alternate proof port from the original promoted FORS baseline: Proof/SignatureLayout.lean -/
section AlternateRecoveryPort1

namespace SigGolfCandidate.Base4Candidate.Ideal

theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight maxLayerHeight
  split <;> (try split) <;> omega

abbrev Signature.counter (signature : Signature) (lay : Layer) : Counter :=
  (signature.layers lay).counter

abbrev Signature.chainValue (signature : Signature) (lay : Layer) : ChainIndex → Digest :=
  (signature.layers lay).chainValues

abbrev PaddedLayer := Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)

/-- Restrict an intermediate proof's padded path to the layer's actual height. -/
abbrev LayerSignature.ofPadded (lay : Layer) (part : PaddedLayer) : LayerSignature lay :=
  ⟨part.1, part.2.1, fun level => part.2.2 (level.castLE (layerHeight_le lay))⟩

@[ext]
theorem LayerSignature.ext {lay : Layer} {left right : LayerSignature lay}
    (hcounter : left.counter = right.counter) (hvalues : left.chainValues = right.chainValues)
    (hpath : left.path = right.path) : left = right := by
  cases left
  cases right
  simp_all

end SigGolfCandidate.Base4Candidate.Ideal

end AlternateRecoveryPort1

/-! Alternate proof port from the original promoted FORS baseline: Proof/RandomizedStatement.lean -/
section AlternateRecoveryPort2

open OracleComp OracleSpec ENNReal

namespace SigGolfCandidate.Base4Candidate.Ideal

namespace Concrete


abbrev messageBytes (message : Message) : HashInput := bytesLE 32 message

abbrev randomnessBytes (randomness : Randomness) : HashInput := bytesLE 16 randomness

end Concrete


/-- The random-oracle semantics: hash queries are answered lazily and consistently by uniform sampling and cached; uniform-sampling queries are forwarded unchanged. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

/-- The interface of a stateless signature scheme in the random-oracle experiment. Signing may fail, so it returns an option. -/
structure Scheme (Key : Type := Seeded.SecretKey) where
  keygen : OracleComp OracleWorld (PublicKey × Key)
  sign : Key → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp OracleWorld Bool

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle {Key : Type} (scheme : Scheme Key) (sk : Key) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request

/-- Forward the shared random oracle and uniform sampling to the adversary unchanged, alongside the logged signing oracle. -/
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

noncomputable def Seeded.gameRest {Key : Type} (randomizedScheme : Scheme Key) (adversary : Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle randomizedScheme sk) (adversary.main pk)).run
  let verified ← randomizedScheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- Key generation, followed by the adversary and final verification. -/
noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  Seeded.gameRest scheme adversary pk sk

/-- Success probability from an empty random-oracle cache. -/
noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]

/-- Count one per hash call, including cache hits, and zero per uniform sample. -/
noncomputable def countedRomImpl :=
  romImpl.withAddCost (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Every execution of the consistent random oracle uses at most `q` hash calls, including key generation, adversarial hashing, signing, and final verification. -/
def HasHashQueryBound {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ countedRomImpl (gameCore scheme adversary)).run.run' ∅),
    result.2 ≤ q

/-- The security bound for an intermediate scheme. -/
def HasClassicalSecurityBits {Key : Type} (scheme : Scheme Key) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end SigGolfCandidate.Base4Candidate.Ideal

end AlternateRecoveryPort2

/-! Alternate proof port from the original promoted FORS baseline: Proof/IdealStatement.lean -/
section AlternateRecoveryPort3

open OracleComp OracleSpec ENNReal

namespace SigGolfCandidate.Base4Candidate.Ideal

/-- The key of the specification: the public parameter (always `0`), the layer-`0` root, and every sampled secret. `Gen` samples them independently and uniformly, at every position of the index types, so positions a layer does not have hold secrets nothing reads; the seed derivation of the specification is an implementation of this key, not this key. -/
structure SecretKey where
  parameter : PublicParameter
  root : Digest
  otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest
  ftsSecret : Index → FtsTree → FtsLeaf → Digest
  /-- The top tree's node table `(level, nodeIdx) ↦ X_{level, nodeIdx}`, built by key generation. The
  signer reads the top layer's authentication path from it instead of rebuilding the top tree. -/
  top : Nat → Nat → Digest

namespace Concrete

noncomputable opaque randomnessSampleableType : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable local instance : SampleableType Randomness := randomnessSampleableType

noncomputable def sampleRandomness : ProbComp Randomness :=
  $ᵗ Randomness

attribute [irreducible] sampleRandomness


variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable opaque otsSecretsSampleableType :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)

noncomputable local instance :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  otsSecretsSampleableType

noncomputable opaque ftsSecretsSampleableType :
    SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  SampleableType.ofFintype (Index → FtsTree → FtsLeaf → Digest)

noncomputable local instance : SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  ftsSecretsSampleableType

/-- `pk_i = Chain(P, 0, 2^w - 1, sk_i)` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)

/-- `OtsSign`: the least admissible counter, and the chain values it dictates. The search starts at `0` and stops after `encodingAttemptLimit` counters. -/
def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secret chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf secret message attempts (counter + 1)

def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf secret message encodingAttemptLimit 0

/-- `X^{lay,tau}_{level,nodeIdx}`, the Merkle tree over the layer's one-time leaves. -/
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf (secret leaf)
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
      let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

/-- `TreeRoot(P, lay, tau) = X^{lay,tau}_{h_lay, 0}`. -/
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : m Digest :=
  treeNode parameter lay tree secret (layerHeight lay) 0

/-- `TreePath`: `A_level = X^{lay,tau}_{level, floor(e / 2^level) xor 1}` for the layer's own `h_lay` levels, and nothing above them. -/
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) : m (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      treeNode parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      pure 0

/-- `Y^{idx,kappa}_{level,nodeIdx}`, one tree of the forest. -/
def ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := ftsLeafOfNat nodeIdx
      ftsLeafHash parameter index tree leaf (secret leaf)
  | level + 1, nodeIdx => do
      let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
      let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)

/-- `FtsKey(P, idx)`, the hash of the forest's `k - 1` roots. -/
def ftsKey (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) : m Digest := do
  let roots ← sequenceFin fun tree =>
    ftsNode parameter index tree (secret tree) ftsTreeHeight 0
  tweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

/-- `FtsOpen`: the opened secrets and, per tree, the `a` siblings of the opened leaf. -/
def ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) : m (FtsTree → Fin ftsTreeHeight → Digest) :=
  sequenceFin fun tree =>
    sequenceFin fun level =>
      ftsNode parameter index tree (secret tree) level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

/-- The public parameter is the constant `P = 0`. -/
noncomputable def sampleParameter : ProbComp PublicParameter :=
  pure 0

noncomputable def sampleOtsSecrets :
    ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  $ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)

noncomputable def sampleFtsSecrets : ProbComp (Index → FtsTree → FtsLeaf → Digest) :=
  $ᵗ (Index → FtsTree → FtsLeaf → Digest)

/-- Key generation's tree: layer `0`'s tree built once from table secrets, exactly as the seeded key generation builds it. -/
def keygenRoot (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) : m Digest := do
  let (_, _, root) ← buildLayerTree parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  return root

/-- Key generation's tree kept whole: layer `0`'s node table, built once from table secrets with exactly
the queries of `keygenRoot`. -/
def keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    m (Nat → Nat → Digest) := do
  let (_, table) ← buildLayerTable parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  return table

/-- `Gen`: take the parameter `P = 0`, sample every secret, and build layer `0`'s tree, keeping its node
table for the signer and its root for the public key. The trees below it are built when a signature needs
them, so nothing else is computed here. -/
noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  let top ← liftM
    (keygenTable parameter (otsSecret topLayer rootTree) : OracleComp HashSpec (Nat → Nat → Digest))
  let root := top (layerHeight topLayer) 0
  return (⟨root, parameter⟩, ⟨parameter, root, otsSecret, ftsSecret, top⟩)

/-- One digest attempt: one hash, keeping the index and the leaf indices if the digest is admissible. -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none

/-- The digest loop: at most `digestAttemptLimit` attempts, each sampling a fresh randomizer, stopping at the first admissible digest. It takes `2^a` attempts on average. -/
noncomputable def signDigestLoop : Nat → SecretKey → Message →
    OracleComp OracleWorld (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _secretKey, _message => pure none
  | attempts + 1, secretKey, message => do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM
        (signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))
      match attempt with
      | some (index, leaves) => pure (some (randomness, index, leaves))
      | none => signDigestLoop attempts secretKey message

/-- The message layer `lay` signs: the root of the tree below it, or the few-time public key at the bottom. Every layer's message is fixed by the index alone, which is what makes the layers independent. -/
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    treeRoot secretKey.parameter below (treeIndexAt index below)
      (secretKey.otsSecret below (treeIndexAt index below))
  else
    ftsKey secretKey.parameter index (secretKey.ftsSecret index)

/-- One layer's contribution: its counter, its chain values, and its authentication path. -/
def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  match ← otsSign secretKey.parameter lay tree leaf (secretKey.otsSecret lay tree leaf) message with
  | none => return none
  | some (counter, values) => do
      let path ← treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leaf
      return some (counter, values, path)

/-- `Sig` after the digest loop, from table secrets: the forest built once, then the layers from the bottom up, each a counter search and its tree built once, and the top layer's path read from the key's node table. This mirrors `Seeded.signChecked` query for query, except for the secret and mask derivations. -/
def signAfterDigest (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : OracleComp HashSpec (Option Signature) :=
  signFrom secretKey.parameter index (fun tree leaf => pure (secretKey.ftsSecret index tree leaf))
    (fun lay tree leaf chainIdx => pure (secretKey.otsSecret lay tree leaf chainIdx))
    (fun level nodeIdx => pure (secretKey.top level nodeIdx)) randomness leaves

/-- `Sig(sk, m)`: the digest loop, then the forest and the layers, or nothing as soon as one search fails. -/
noncomputable def sign (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => return none
  | some (randomness, index, leaves) =>
      liftM (signAfterDigest secretKey randomness index leaves : OracleComp HashSpec (Option Signature))

attribute [irreducible] treeNode ftsNode sampleParameter sampleOtsSecrets sampleFtsSecrets keygen sign
  keygenRoot keygenTable signAfterDigest

end Concrete

/-- The concrete SPHINCS scheme: key generation, the stateless randomized signer, and the verifier defined above. -/
noncomputable def Concrete.scheme : Scheme SecretKey where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey message signature =>
    liftM (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)

/-- The security claim: `127` bits of classical strong unforgeability in the random-oracle model, at `2^32` signing requests per key pair. -/
abbrev IndependentSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127

end SigGolfCandidate.Base4Candidate.Ideal

end AlternateRecoveryPort3

/-! Alternate proof port from the original promoted FORS baseline: Proof/Scheme/StatementLemmas.lean -/
section AlternateRecoveryPort4

/-!
# Facts about the statement

`Scheme.lean` seals the two tree recursions against accidental unfolding, which also stops Lean from generating their equational theorems. Unsealing them locally makes the equations hold by `rfl`, so this module states them once as ordinary theorems and the rest of the development rewrites with those instead of unfolding anything. It also checks the arithmetic the concrete parameters fix: the layer heights, the index decomposition and the authentication path offsets.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

attribute [local semireducible] treeNode ftsNode verify sign sampleRandomness

noncomputable local instance instSampleableTypeRandomness_1 : SampleableType Randomness :=
  randomnessSampleableType

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

@[simp]
theorem treeNode_zero_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (nodeIdx : Nat) :
    treeNode (m := m) parameter lay tree secret 0 nodeIdx
      = (do
          let endpoints ← oneTimePublicKey parameter lay tree (leafOfNat nodeIdx)
            (secret (leafOfNat nodeIdx))
          leafHash parameter lay tree (leafOfNat nodeIdx) endpoints) := rfl

theorem treeNode_succ_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    treeNode (m := m) parameter lay tree secret (level + 1) nodeIdx
      = (do
          let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
          let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
          tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)) := rfl

@[simp]
theorem ftsNode_zero_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (nodeIdx : Nat) :
    ftsNode (m := m) parameter index tree secret 0 nodeIdx
      = ftsLeafHash parameter index tree (ftsLeafOfNat nodeIdx) (secret (ftsLeafOfNat nodeIdx)) := rfl

theorem ftsNode_succ_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    ftsNode (m := m) parameter index tree secret (level + 1) nodeIdx
      = (do
          let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
          let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
          tweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx)
            (nodePayload left right)) := rfl

@[simp]
theorem treeFold_zero_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) (value : Digest) :
    treeFold (m := m) parameter lay tree leaf path 0 value = pure value := rfl

theorem treeFold_succ_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) (levels : Nat) (value : Digest) :
    treeFold (m := m) parameter lay tree leaf path (levels + 1) value
      = (do
          let current ← treeFold parameter lay tree leaf path levels value
          if leaf.val.testBit levels then
            tweakableHash parameter (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload (path levels) current)
          else
            tweakableHash parameter (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload current (path levels))) := rfl

@[simp]
theorem ftsFold_zero_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) (value : Digest) :
    ftsFold (m := m) parameter index tree leaf path 0 value = pure value := rfl

theorem ftsFold_succ_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) (levels : Nat) (value : Digest) :
    ftsFold (m := m) parameter index tree leaf path (levels + 1) value
      = (do
          let current ← ftsFold parameter index tree leaf path levels value
          let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
          if leaf.val.testBit levels then
            tweakableHash parameter (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload sibling current)
          else
            tweakableHash parameter (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload current sibling)) := rfl

@[simp]
theorem verifyLayers_zero_eq (parameter : PublicParameter) (index : Index) (signature : Signature)
    (message : Digest) :
    verifyLayers (m := m) parameter index signature 0 message = pure (some message) := rfl

theorem verifyLayers_succ_eq (parameter : PublicParameter) (index : Index) (signature : Signature)
    (remaining : Nat) (message : Digest) :
    verifyLayers (m := m) parameter index signature (remaining + 1) message
      = (if hlayer : remaining < numLayers then
          (do
            match ← otsLeafAttempt parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
                (leafIndexAt index ⟨remaining, hlayer⟩) message
                (signature.counter ⟨remaining, hlayer⟩)
                (signature.chainValue ⟨remaining, hlayer⟩) with
            | none => pure none
            | some value => do
                let root ← treeFold parameter ⟨remaining, hlayer⟩
                  (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩)
                  (signaturePath signature ⟨remaining, hlayer⟩) (layerHeight ⟨remaining, hlayer⟩)
                  value
                verifyLayers parameter index signature remaining root)
        else pure none) := by
  rw [verifyLayers]
  split
  · simp only [otsLeaf_eq]
    apply bind_congr
    intro result
    cases result <;> rfl
  · rfl

attribute [local irreducible] verifyLayers

theorem verifyCore_eq (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verifyCore (m := m) publicKey message signature
      = (do
          let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
          if ¬ Admissible digest then
            return false
          else
            let ftsPublicKey ← ftsRecover publicKey.parameter (digestIndex digest)
              (digestLeaves digest) signature.ftsSecret signature.ftsPath
            match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
                ftsPublicKey with
            | none => return false
            | some root => return decide (root = publicKey.root)) := by
  unfold verifyCore
  apply bind_congr
  intro digest
  split
  · rfl
  · apply bind_congr
    intro key
    apply bind_congr
    intro result
    cases result <;> rfl

theorem verify_eq_ite (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verify (m := m) publicKey message signature
      = if CountersInRange signature then verifyCore publicKey message signature else pure false := rfl

theorem verify_eq (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hcounters : CountersInRange signature) :
    verify (m := m) publicKey message signature
      = (do
          let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
          if ¬ Admissible digest then
            return false
          else
            let ftsPublicKey ← ftsRecover publicKey.parameter (digestIndex digest)
              (digestLeaves digest) signature.ftsSecret signature.ftsPath
            match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
                ftsPublicKey with
            | none => return false
            | some root => return decide (root = publicKey.root)) := by
  rw [verify_eq_ite, if_pos hcounters, verifyCore_eq]

theorem verify_eq_of_not_counters (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hcounters : ¬ CountersInRange signature) :
    verify (m := m) publicKey message signature = pure false := by
  rw [verify_eq_ite, if_neg hcounters]

theorem sign_eq (secretKey : SecretKey) (message : Message) :
    sign secretKey message
      = (do
          match ← signDigestLoop digestAttemptLimit secretKey message with
          | none => return none
          | some (randomness, index, leaves) =>
              liftM (signAfterDigest secretKey randomness index leaves :
                OracleComp HashSpec (Option Signature))) := rfl

theorem sampleRandomness_eq :
    sampleRandomness = ($ᵗ Randomness : ProbComp Randomness) := rfl

/-! ## Parameter arithmetic -/

example : ∑ lay : Layer, layerHeight lay = totalHeight := by decide

example : (List.ofFn fun lay : Layer => layerHeight lay) = [12, 7, 7, 7] := by decide

example : (List.ofFn fun lay : Layer => heightAbove lay) = [0, 12, 19, 26] := by decide

example : (List.ofFn fun lay : Layer => heightBelow lay) = [21, 14, 7, 0] := by decide

/-- The digest is `h + k * a = 184` bits and has to fit in one oracle output. -/
example : messageDigestBits = 198 ∧ messageDigestBits ≤ hashOutputBits := by decide

theorem treeIndexAt_val (index : Index) (lay : Layer) :
    (treeIndexAt index lay).val = index.val / 2 ^ (totalHeight - heightAbove lay) := rfl

theorem leafIndexAt_val (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val = index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay := rfl

theorem leafIndexAt_lt (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val < 2 ^ layerHeight lay := by
  rw [leafIndexAt_val]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem heightAbove_top : heightAbove topLayer = 0 := by decide

/-- The layer below `lay` sits `h_lay` bits lower in the index. -/
theorem heightAbove_succ (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    heightAbove ⟨lay.val + 1, hbelow⟩ = heightAbove lay + layerHeight lay := by
  revert lay; decide

theorem heightAbove_add_le (lay : Layer) : heightAbove lay + layerHeight lay ≤ totalHeight := by
  revert lay; decide

theorem heightBelow_eq (lay : Layer) :
    heightBelow lay + layerHeight lay + heightAbove lay = totalHeight := by
  revert lay; decide

/-- Layer `0` holds a single tree, the public key's. -/
theorem treeIndexAt_topLayer (index : Index) : (treeIndexAt index topLayer).val = 0 := by
  have hlt : index.val < 2 ^ totalHeight := index.isLt
  rw [treeIndexAt_val, heightAbove_top, Nat.sub_zero]
  exact Nat.div_eq_of_lt hlt

/-- The layers link: the tree used on the layer below `lay` is the one whose root sits at leaf
`e_lay` of the tree used on `lay`. -/
theorem layers_link (index : Index) (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    (treeIndexAt index ⟨lay.val + 1, hbelow⟩).val
      = (treeIndexAt index lay).val * 2 ^ layerHeight lay + (leafIndexAt index lay).val := by
  have hsum := heightBelow_eq lay
  have habove := heightAbove_succ lay hbelow
  rw [treeIndexAt_val, treeIndexAt_val, leafIndexAt_val, habove]
  have hb : totalHeight - (heightAbove lay + layerHeight lay) = heightBelow lay := by omega
  have ht : totalHeight - heightAbove lay = heightBelow lay + layerHeight lay := by omega
  rw [hb, ht, pow_add, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' _ _).symm

/-- The bottom layer's leaves are the `2^h` indices themselves. -/
theorem leafIndexAt_bottomLayer (index : Index) :
    (leafIndexAt index bottomLayer).val = index.val % 2 ^ layerHeight bottomLayer := by
  have hb : heightBelow bottomLayer = 0 := by decide
  simp [leafIndexAt_val, hb]

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateRecoveryPort4

/-! Alternate proof port from the original promoted FORS baseline: Proof/Hypertree/Extract.lean -/
section AlternateRecoveryPort5
/-!
# Extracting the first divergence

The deterministic half of the reduction, for one layer's tree. If a fold on values an adversary
supplies reaches the honest node above the leaf, then either every value it supplied was the honest
one, or at some level it hashed something other than the honest payload to the honest value. The
second is what the union bound charges; the first is what makes the adversary's signature the honest
one, and so no forgery.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (path : Nat → Digest)

/-- The value the honest tree carries at a position. -/
def honestNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx)

/-- What the fold has reached after `levels` steps. -/
def foldValue (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (treeFold parameter lay tree leaf path levels value)

/-- Two children in the order the bit dictates. Written with `Bool.rec` rather than `if`, so that
both cases hold by `rfl` and rewriting the bit needs no reasoning about `Decidable` instances. -/
def orderedPayload (bit : Bool) (current sibling : Digest) : HashInput :=
  bit.rec (nodePayload current sibling) (nodePayload sibling current)

@[simp] theorem orderedPayload_false (current sibling : Digest) :
    orderedPayload false current sibling = nodePayload current sibling := rfl

@[simp] theorem orderedPayload_true (current sibling : Digest) :
    orderedPayload true current sibling = nodePayload sibling current := rfl

/-- The payload the fold hashes on its way from `level` to `level + 1`. -/
def foldPayload (value : Digest) (level : Nat) : HashInput :=
  orderedPayload (leaf.val.testBit level)
    (foldValue f parameter lay tree leaf path value level) (path level)

theorem eval_tweakableHash (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn f (tweakableHash parameter domain payload)
      = truncateHash (f (tweakableHashInput parameter domain payload)) := by
  simp only [tweakableHash, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
    evalWithAnswerFn_pure]

theorem honestNode_succ (level nodeIdx : Nat) :
    honestNode f parameter lay tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
          (nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
            (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestNode, treeNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]

theorem foldValue_succ (value : Digest) (level : Nat) :
    foldValue f parameter lay tree leaf path value (level + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.node lay tree (level + 1) (leaf.val / 2 ^ (level + 1)))
          (foldPayload f parameter lay tree leaf path value level))) := by
  simp only [foldValue, foldPayload, treeFold_succ_eq, evalWithAnswerFn_bind, orderedPayload]
  cases leaf.val.testBit level <;> rfl

/-- A hit at a node position: something other than the honest payload hashing to the honest value
there. Domain separation makes the target a function of the position alone, which is what lets the
union bound charge it. -/
def NodeHit (level nodeIdx : Nat) (payload : HashInput) : Prop :=
  payload ≠ nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
      (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))
    ∧ truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload))
      = honestNode f parameter lay tree secret (level + 1) nodeIdx

/-- **The first divergence.** A fold that reaches the honest node above the leaf either used the
honest leaf and the honest siblings throughout, or hit a node value somewhere along the way. -/
theorem treeFold_extract (value : Digest) (levels : Nat)
    (hfold : foldValue f parameter lay tree leaf path value levels
      = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels)) :
    (value = honestNode f parameter lay tree secret 0 leaf.val
        ∧ ∀ level, level < levels → path level
            = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∨ ∃ level, level < levels
          ∧ NodeHit f parameter lay tree secret level (leaf.val / 2 ^ (level + 1))
              (foldPayload f parameter lay tree leaf path value level) := by
  induction levels with
  | zero =>
      left
      refine ⟨?_, fun level hlevel => absurd hlevel (by omega)⟩
      simpa [foldValue] using hfold
  | succ levels ih =>
      obtain ⟨j, hcase⟩ := index_sibling_cases (leaf.val / 2 ^ levels)
      have hj : leaf.val / 2 ^ (levels + 1) = j := by
        rw [div_pow_succ]
        rcases hcase with ⟨hc, _, _⟩ | ⟨hc, _, _⟩ <;> omega
      have hhash : truncateHash (f (tweakableHashInput parameter
            (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
            (foldPayload f parameter lay tree leaf path value levels)))
          = honestNode f parameter lay tree secret (levels + 1) (leaf.val / 2 ^ (levels + 1)) := by
        rw [← foldValue_succ]
        exact hfold
      by_cases hagree : foldPayload f parameter lay tree leaf path value levels
          = nodePayload (honestNode f parameter lay tree secret levels (2 * j))
              (honestNode f parameter lay tree secret levels (2 * j + 1))
      · have hstep : foldValue f parameter lay tree leaf path value levels
              = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels)
            ∧ path levels = honestNode f parameter lay tree secret levels
              (Nat.xor (leaf.val / 2 ^ levels) 1) := by
          rw [foldPayload] at hagree
          rcases hcase with ⟨hc, hsibling, hmod⟩ | ⟨hc, hsibling, hmod⟩
          · rw [show leaf.val.testBit levels = false by
              rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hcur, hsib⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
          · rw [show leaf.val.testBit levels = true by
              rw [testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hsib, hcur⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
        rcases ih hstep.1 with ⟨hvalue, hpaths⟩ | ⟨level, hlevel, hnode⟩
        · left
          refine ⟨hvalue, fun level hlevel => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | heq
          · exact hpaths level hlt
          · subst heq; exact hstep.2
        · exact Or.inr ⟨level, by omega, hnode⟩
      · right
        exact ⟨levels, by omega, by rw [hj]; exact hagree, hhash⟩

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateRecoveryPort5

/-! Alternate proof port from the original promoted FORS baseline: Proof/Ots/ExtractChain.lean -/
section AlternateRecoveryPort6
/-!
# Extracting the first divergence in a chain

The same argument as for a layer's tree, on a hash chain. If walking from a value the adversary
supplied reaches the honest endpoint, then either that value was the honest one at its position, or
somewhere along the walk it hashed something other than the honest predecessor to the honest
successor.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : Digest)

/-- The honest chain value at a position. -/
def honestChain (position : Nat) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 position secret)

/-- What the walk has reached after `steps` steps from `start`. -/
def walkValue (start : Nat) (value : Digest) (steps : Nat) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value)

theorem honestChain_succ (position : Nat) (hposition : position < chainLength - 1) :
    honestChain f parameter lay tree leaf chainIdx secret (position + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨position, hposition⟩)
          (digestBytes (honestChain f parameter lay tree leaf chainIdx secret position)))) := by
  simp only [honestChain, chainWalk, evalWithAnswerFn_bind, Nat.zero_add, dif_pos hposition,
    eval_tweakableHash]

theorem walkValue_succ (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps < chainLength - 1) :
    walkValue f parameter lay tree leaf chainIdx start value (steps + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨start + steps, hrange⟩)
          (digestBytes (walkValue f parameter lay tree leaf chainIdx start value steps)))) := by
  simp only [walkValue, chainWalk, evalWithAnswerFn_bind, dif_pos hrange, eval_tweakableHash]

/-- A hit at a chain step: something other than the honest value at `position` hashing to the honest
value at `position + 1`. -/
def ChainHit (position : Nat) (hposition : position < chainLength - 1) (payload : Digest) : Prop :=
  payload ≠ honestChain f parameter lay tree leaf chainIdx secret position
    ∧ truncateHash (f (tweakableHashInput parameter
        (.chain lay tree leaf chainIdx ⟨position, hposition⟩) (digestBytes payload)))
      = honestChain f parameter lay tree leaf chainIdx secret (position + 1)

/-- **The first divergence in a chain.** -/
theorem chainWalk_extract (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps ≤ chainLength - 1)
    (hwalk : walkValue f parameter lay tree leaf chainIdx start value steps
      = honestChain f parameter lay tree leaf chainIdx secret (start + steps)) :
    value = honestChain f parameter lay tree leaf chainIdx secret start
      ∨ ∃ (offset : Nat) (hoffset : start + offset < chainLength - 1), offset < steps
          ∧ ChainHit f parameter lay tree leaf chainIdx secret (start + offset) hoffset
              (walkValue f parameter lay tree leaf chainIdx start value offset) := by
  induction steps with
  | zero =>
      left
      simpa [walkValue, chainWalk] using hwalk
  | succ steps ih =>
      have hlt : start + steps < chainLength - 1 := by omega
      by_cases hagree : walkValue f parameter lay tree leaf chainIdx start value steps
          = honestChain f parameter lay tree leaf chainIdx secret (start + steps)
      · rcases ih (by omega) hagree with hvalue | ⟨offset, hoffset, hlt', hhit⟩
        · exact Or.inl hvalue
        · exact Or.inr ⟨offset, hoffset, by omega, hhit⟩
      · refine Or.inr ⟨steps, hlt, by omega, hagree, ?_⟩
        rw [← walkValue_succ f parameter lay tree leaf chainIdx start value steps hlt, hwalk,
          show start + (steps + 1) = start + steps + 1 by omega]

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateRecoveryPort6

/-! Alternate proof port from the original promoted FORS baseline: Proof/Scheme/Eval.lean -/
section AlternateRecoveryPort7

/-!
# Evaluating against a fixed answer function

The random oracle's support is characterized by total answer functions: a value comes out of the
lazy oracle exactly when some `f : QueryImpl HashSpec Id` agreeing with the cache evaluates the
computation to it (`exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support`). So every structural
fact this development needs is a fact about `evalWithAnswerFn f`, where `f` answers each input the
same way however often it is asked and in whatever order.

That is what makes the shape of the algorithms tractable: under `evalWithAnswerFn f` a family of
independent computations may be assembled in any order, which is false at the level of
computations, `sequenceFin` fixing one.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

open OracleComp

variable {α : Type} (f : QueryImpl HashSpec Id)

/-- Assembling a family commutes with evaluation. -/
@[simp]
theorem evalWithAnswerFn_sequenceFin {n : Nat} (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn f (sequenceFin computation) = fun index => evalWithAnswerFn f (computation index) := by
  induction n with
  | zero => funext index; exact index.elim0
  | succ n ih =>
      funext index
      simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      cases index using Fin.cases <;> rfl

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateRecoveryPort7

/-! Alternate proof port from the original promoted FORS baseline: Proof/Ots/OneTime.lean -/
section AlternateRecoveryPort8
/-!
# The one-time signature

`Ots.leaf` recovers the leaf `Ots.sign` committed to. The counter matters only through the codeword
it produces: correctness holds for *any* admissible counter, not just the least one the signer
takes, which is why a second admissible counter for the same codeword is a strong forgery rather
than a break.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

open OracleComp

variable {α : Type} (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
  (tree : TreeIndex) (leaf : LeafIndex)

/-- Steps compose under evaluation. -/
theorem eval_chainWalk_add (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start (a + b) value)
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + a) b
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start a value))) := by
  rw [chainWalk_add, evalWithAnswerFn_bind]

/-- Revealing a chain at its codeword digit and walking the rest reaches the public value. -/
theorem eval_recoverChain (chainIdx : ChainIndex) (digit : Digit) (value : Digest) :
    evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
        (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)))
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) value) := by
  have hdigit : digit.val + (chainLength - 1 - digit.val) = chainLength - 1 := by
    have hlt := digit.isLt
    simp only [chainLength, winternitzBits] at hlt
    simp only [chainLength, winternitzBits]
    omega
  calc evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)))
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx
          (0 + digit.val) (chainLength - 1 - digit.val)
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value))) := by
        rw [recoverChain, Nat.zero_add]
    _ = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0
          (digit.val + (chainLength - 1 - digit.val)) value) := (eval_chainWalk_add ..).symm
    _ = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) value) := by
        rw [hdigit]

/-- The honest one-time public value of one chain. -/
theorem eval_oneTimePublicKey (secret : ChainIndex → Digest) :
    evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret)
      = fun chainIdx => evalWithAnswerFn f
          (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)) := by
  simp [oneTimePublicKey]

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateRecoveryPort8

/-! Alternate proof port from the original promoted FORS baseline: Proof/Ots/ExtractOts.lean -/
section AlternateRecoveryPort9
/-!
# Extracting a one-time signature

If the verifier's half of a one-time signature returns the honest leaf, then either the chain values
the adversary supplied are the honest ones at its codeword's positions, or it hit the leaf value, or
it hit a chain value. The first alternative is what the incomparability of the code turns into "the
signature is the one the signer produced".
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)

theorem leafOfNat_val : leafOfNat leaf.val = leaf := by
  ext
  simp [leafOfNat, Nat.mod_eq_of_lt leaf.isLt]

/-- The honest one-time public values at a leaf. -/
def honestEndpoints (chainIdx : ChainIndex) : Digest :=
  honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx) (chainLength - 1)

theorem honestEndpoints_def : honestEndpoints f parameter lay tree secret leaf
    = fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret leaf chainIdx)) :=
  rfl

/-- A hit at a leaf: something other than the honest endpoints hashing to the honest leaf. -/
def LeafHit (payload : HashInput) : Prop :=
  payload ≠ leafPayload (honestEndpoints f parameter lay tree secret leaf)
    ∧ truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf) payload))
      = honestNode f parameter lay tree secret 0 leaf.val

theorem honestNode_zero_eq_leafHash :
    honestNode f parameter lay tree secret 0 leaf.val
      = truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf)
          (leafPayload (honestEndpoints f parameter lay tree secret leaf)))) := by
  simp only [honestNode, treeNode_zero_eq, leafOfNat_val, evalWithAnswerFn_bind, leafHash,
    eval_tweakableHash, eval_oneTimePublicKey, honestEndpoints_def]

/-- **The one-time signature.** -/
theorem otsLeaf_extract (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some codeword)
    (hleaf : evalWithAnswerFn f (otsLeafAttempt parameter lay tree leaf message counter values)
      = some (honestNode f parameter lay tree secret 0 leaf.val)) :
    (∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val)
      ∨ LeafHit f parameter lay tree secret leaf
          (leafPayload fun chainIdx => walkValue f parameter lay tree leaf chainIdx
            (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val))
      ∨ ∃ (chainIdx : ChainIndex) (offset : Nat)
          (hoffset : (codeword chainIdx).val + offset < chainLength - 1), offset < chainLength - 1
            - (codeword chainIdx).val
            ∧ ChainHit f parameter lay tree leaf chainIdx (secret leaf chainIdx)
                ((codeword chainIdx).val + offset) hoffset
                (walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
                  (values chainIdx) offset) := by
  classical
  have hrecovered : evalWithAnswerFn f (leafHash parameter lay tree leaf
        (fun chainIdx => walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
          (values chainIdx) (chainLength - 1 - (codeword chainIdx).val)))
      = honestNode f parameter lay tree secret 0 leaf.val := by
    simp only [otsLeafAttempt, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hencode,
      evalWithAnswerFn_sequenceFin] at hleaf
    simpa [walkValue, recoverChain] using hleaf
  by_cases hpayload : (leafPayload fun chainIdx => walkValue f parameter lay tree leaf chainIdx
      (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val))
      = leafPayload (honestEndpoints f parameter lay tree secret leaf)
  · have hendpoints := leafPayload_injective hpayload
    have hchains : ∀ chainIdx : ChainIndex,
        values chainIdx = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val
          ∨ ∃ (offset : Nat) (hoffset : (codeword chainIdx).val + offset < chainLength - 1),
              offset < chainLength - 1 - (codeword chainIdx).val
                ∧ ChainHit f parameter lay tree leaf chainIdx (secret leaf chainIdx)
                    ((codeword chainIdx).val + offset) hoffset
                    (walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
                      (values chainIdx) offset) := by
      intro chainIdx
      have hdigit : (codeword chainIdx).val ≤ chainLength - 1 := by
        have := (codeword chainIdx).isLt
        simp only [chainLength, winternitzBits] at this ⊢
        omega
      refine chainWalk_extract f parameter lay tree leaf chainIdx (secret leaf chainIdx)
        (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val)
        (by omega) ?_
      have := congrFun hendpoints chainIdx
      rw [show (codeword chainIdx).val + (chainLength - 1 - (codeword chainIdx).val)
        = chainLength - 1 by omega]
      exact this
    by_cases hall : ∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val
    · exact Or.inl hall
    · obtain ⟨chainIdx, hne⟩ := not_forall.mp hall
      rcases hchains chainIdx with hhonest | ⟨offset, hoffset, hlt, hhit⟩
      · exact absurd hhonest hne
      · exact Or.inr (Or.inr ⟨chainIdx, offset, hoffset, hlt, hhit⟩)
  · exact Or.inr (Or.inl ⟨hpayload, by
      rw [← hrecovered, leafHash, eval_tweakableHash]⟩)

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateRecoveryPort9

/-! Alternate proof port from the original promoted FORS baseline: Proof/Fts/ExtractFts.lean -/
section AlternateRecoveryPort10
/-!
# Extracting a few-time opening

The tree argument again, on one tree of the few-time forest, and then on the leaf below it. If a fold
on values an adversary supplied reaches the honest root, either it supplied the honest secret and the
honest siblings, or it hit a node, or it hit the leaf. Supplying the honest secret is the only
alternative that is not a hash break, and it means the secret was revealed by a signature: that is
the leak the parameters are chosen against.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (tree : FtsTree)
  (secret : FtsLeaf → Digest) (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest)

theorem ftsLeafOfNat_val : ftsLeafOfNat leaf.val = leaf := by
  ext
  simp [ftsLeafOfNat, Nat.mod_eq_of_lt leaf.isLt]

/-- The value the honest few-time tree carries at a position. -/
def honestFtsNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx)

/-- What the fold has reached after `levels` steps. -/
def ftsFoldValue (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (ftsFold parameter index tree leaf path levels value)

/-- The sibling the fold reads at a level, `0` past the tree's height. -/
def ftsSibling (level : Nat) : Digest :=
  if hlevel : level < ftsTreeHeight then path ⟨level, hlevel⟩ else 0

/-- The payload the fold hashes on its way from `level` to `level + 1`. -/
def ftsFoldPayload (value : Digest) (level : Nat) : HashInput :=
  orderedPayload (leaf.val.testBit level)
    (ftsFoldValue f parameter index tree leaf path value level) (ftsSibling path level)

theorem honestFtsNode_succ (level nodeIdx : Nat) :
    honestFtsNode f parameter index tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.ftsNode index tree (level + 1) nodeIdx)
          (nodePayload (honestFtsNode f parameter index tree secret level (2 * nodeIdx))
            (honestFtsNode f parameter index tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestFtsNode, ftsNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]

theorem honestFtsNode_zero (leafIdx : FtsLeaf) :
    honestFtsNode f parameter index tree secret 0 leafIdx.val
      = truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leafIdx)
          (digestBytes (secret leafIdx)))) := by
  simp only [honestFtsNode, ftsNode_zero_eq, ftsLeafOfNat_val, ftsLeafHash, eval_tweakableHash]

theorem ftsFoldValue_succ (value : Digest) (level : Nat) :
    ftsFoldValue f parameter index tree leaf path value (level + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.ftsNode index tree (level + 1) (leaf.val / 2 ^ (level + 1)))
          (ftsFoldPayload f parameter index tree leaf path value level))) := by
  simp only [ftsFoldValue, ftsFoldPayload, ftsSibling, ftsFold_succ_eq, evalWithAnswerFn_bind,
    orderedPayload]
  cases leaf.val.testBit level <;> rfl

/-- A hit at a few-time node. -/
def FtsNodeHit (level nodeIdx : Nat) (payload : HashInput) : Prop :=
  payload ≠ nodePayload (honestFtsNode f parameter index tree secret level (2 * nodeIdx))
      (honestFtsNode f parameter index tree secret level (2 * nodeIdx + 1))
    ∧ truncateHash (f (tweakableHashInput parameter (.ftsNode index tree (level + 1) nodeIdx)
        payload)) = honestFtsNode f parameter index tree secret (level + 1) nodeIdx

/-- A hit at a few-time leaf: something other than the honest secret hashing to the honest leaf. -/
def FtsLeafHit (leafIdx : FtsLeaf) (candidate : Digest) : Prop :=
  candidate ≠ secret leafIdx
    ∧ truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leafIdx)
        (digestBytes candidate))) = honestFtsNode f parameter index tree secret 0 leafIdx.val

/-- **The first divergence in a few-time tree.** -/
theorem ftsFold_extract (value : Digest) (levels : Nat) (hlevels : levels ≤ ftsTreeHeight)
    (hfold : ftsFoldValue f parameter index tree leaf path value levels
      = honestFtsNode f parameter index tree secret levels (leaf.val / 2 ^ levels)) :
    (value = honestFtsNode f parameter index tree secret 0 leaf.val
        ∧ ∀ level, level < levels → ftsSibling path level
            = honestFtsNode f parameter index tree secret level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∨ ∃ level, level < levels
          ∧ FtsNodeHit f parameter index tree secret level (leaf.val / 2 ^ (level + 1))
              (ftsFoldPayload f parameter index tree leaf path value level) := by
  induction levels with
  | zero =>
      left
      refine ⟨?_, fun level hlevel => absurd hlevel (by omega)⟩
      simpa [ftsFoldValue] using hfold
  | succ levels ih =>
      obtain ⟨j, hcase⟩ := index_sibling_cases (leaf.val / 2 ^ levels)
      have hj : leaf.val / 2 ^ (levels + 1) = j := by
        rw [div_pow_succ]
        rcases hcase with ⟨hc, _, _⟩ | ⟨hc, _, _⟩ <;> omega
      have hhash : truncateHash (f (tweakableHashInput parameter
            (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
            (ftsFoldPayload f parameter index tree leaf path value levels)))
          = honestFtsNode f parameter index tree secret (levels + 1)
              (leaf.val / 2 ^ (levels + 1)) := by
        rw [← ftsFoldValue_succ]
        exact hfold
      by_cases hagree : ftsFoldPayload f parameter index tree leaf path value levels
          = nodePayload (honestFtsNode f parameter index tree secret levels (2 * j))
              (honestFtsNode f parameter index tree secret levels (2 * j + 1))
      · have hstep : ftsFoldValue f parameter index tree leaf path value levels
              = honestFtsNode f parameter index tree secret levels (leaf.val / 2 ^ levels)
            ∧ ftsSibling path levels = honestFtsNode f parameter index tree secret levels
              (Nat.xor (leaf.val / 2 ^ levels) 1) := by
          rw [ftsFoldPayload] at hagree
          rcases hcase with ⟨hc, hsibling, hmod⟩ | ⟨hc, hsibling, hmod⟩
          · rw [show leaf.val.testBit levels = false by
              rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hcur, hsib⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
          · rw [show leaf.val.testBit levels = true by
              rw [testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hsib, hcur⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
        rcases ih (by omega) hstep.1 with ⟨hvalue, hpaths⟩ | ⟨level, hlevel, hnode⟩
        · left
          refine ⟨hvalue, fun level hlevel => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | heq
          · exact hpaths level hlt
          · subst heq; exact hstep.2
        · exact Or.inr ⟨level, by omega, hnode⟩
      · right
        exact ⟨levels, by omega, by rw [hj]; exact hagree, hhash⟩

/-- **The few-time leaf.** The value the fold starts from is the hash of a secret the adversary
supplied, so either that secret is the honest one or the leaf was hit. -/
theorem ftsLeaf_extract (candidate : Digest)
    (hleaf : truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leaf)
        (digestBytes candidate))) = honestFtsNode f parameter index tree secret 0 leaf.val) :
    candidate = secret leaf ∨ FtsLeafHit f parameter index tree secret leaf candidate := by
  by_cases hsecret : candidate = secret leaf
  · exact Or.inl hsecret
  · exact Or.inr ⟨hsecret, hleaf⟩

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateRecoveryPort10

/-! Alternate proof port from the original promoted FORS baseline: Proof/LayerAssembly.lean -/
section AlternateRecoveryPort11
open OracleComp OracleSpec
namespace SigGolfCandidate.Base4Candidate.Ideal
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit true
set_option maxRecDepth 4096

def restrictPath (lay : Layer) (path : Fin maxLayerHeight → α) : Fin (layerHeight lay) → α :=
  fun level => path (level.castLE (layerHeight_le lay))

end SigGolfCandidate.Base4Candidate.Ideal

end AlternateRecoveryPort11

/-! Alternate proof port from the original promoted FORS baseline: Proof/Scheme/BuildEval.lean -/
section AlternateRecoveryPort12
/-!
# The builders compute the specification

The signer builds each tree once, level by level. Under every answer function its values are the
values of the recursive specification of `IdealStatement.lean` (`treeNode`, `treePath`, `ftsNode`,
`ftsOpen`, `ftsKey`, `otsSign`, `signLayer`): the node at level `l` and index `j` of a built tree is
`treeNode l j`, the captured chain values are the one-time signature, and the root of layer `lay`'s
tree is the message layer `lay - 1` signs. The secrets are read through an arbitrary computation,
so the same statements cover the seeded signer and the table signer.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id)

/-! ### Options over a family -/

theorem sequenceFin_option_eq {α : Type} {n : Nat} (values : Fin n → Option α) :
    sequenceFin (m := Option) values =
      if h : ∀ i, (values i).isSome then some (fun i => (values i).get (h i)) else none := by
  induction n with
  | zero =>
      rw [dif_pos (fun i => i.elim0)]
      simp only [sequenceFin]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      cases h0 : values 0 with
      | none =>
          rw [dif_neg (fun h => by have := h 0; rw [h0] at this; simp at this)]
          rw [sequenceFin, h0]
          rfl
      | some head =>
          have hstep : sequenceFin (m := Option) values =
              sequenceFin (m := Option) (fun i : Fin n => values i.succ) >>= fun tail =>
                some (Fin.cases head tail) := by
            rw [sequenceFin, h0]
            rfl
          rw [hstep, ih]
          by_cases hall : ∀ i, (values i).isSome
          · rw [dif_pos (fun i : Fin n => hall i.succ), dif_pos hall]
            simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
            funext i
            cases i using Fin.cases with
            | zero => simp [h0]
            | succ i => rfl
          · rw [dif_neg hall]
            have htail : ¬ ∀ i : Fin n, (values i.succ).isSome := by
              intro htail
              apply hall
              intro i
              cases i using Fin.cases with
              | zero => simp [h0]
              | succ i => exact htail i
            rw [dif_neg htail]
            rfl

/-! ### Levels -/

theorem eval_buildLevel (hashNode : Nat → Digest → Digest → OracleComp HashSpec Digest)
    (width : Nat) (below : Nat → Digest) :
    evalWithAnswerFn f (buildLevel hashNode width below) = fun nodeIdx =>
      if h : nodeIdx < width then
        evalWithAnswerFn f (hashNode nodeIdx (below (2 * nodeIdx)) (below (2 * nodeIdx + 1)))
      else 0 := by
  simp only [buildLevel, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]

/-- A built tree carries the nodes of any recursion with the same leaves and the same node hash. -/
theorem eval_buildLevels (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (height : Nat) (leaves : Nat → Digest) (node : Nat → Nat → Digest)
    (hleaf : ∀ nodeIdx, nodeIdx < 2 ^ height → leaves nodeIdx = node 0 nodeIdx)
    (hnode : ∀ level nodeIdx, level < height → nodeIdx < 2 ^ (height - (level + 1)) →
      evalWithAnswerFn f (hashNode (level + 1) nodeIdx (node level (2 * nodeIdx))
        (node level (2 * nodeIdx + 1))) = node (level + 1) nodeIdx)
    (levels : Nat) (hlevels : levels ≤ height) :
    ∀ level, level ≤ levels → ∀ nodeIdx, nodeIdx < 2 ^ (height - level) →
      evalWithAnswerFn f (buildLevels hashNode height leaves levels) level nodeIdx
        = node level nodeIdx := by
  induction levels with
  | zero =>
      intro level hlevel nodeIdx hnodeIdx
      have hl : level = 0 := by omega
      subst hl
      simp only [buildLevels, evalWithAnswerFn_pure]
      exact hleaf nodeIdx (by simpa using hnodeIdx)
  | succ levels ih =>
      intro level hlevel nodeIdx hnodeIdx
      simp only [buildLevels, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_buildLevel]
      by_cases hl : level = levels + 1
      · subst hl
        rw [if_pos rfl, dif_pos hnodeIdx]
        have hpow : 2 ^ (height - levels) = 2 * 2 ^ (height - (levels + 1)) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [ih (by omega) levels le_rfl (2 * nodeIdx) (by omega),
          ih (by omega) levels le_rfl (2 * nodeIdx + 1) (by omega)]
        exact hnode levels nodeIdx (by omega) hnodeIdx
      · rw [if_neg hl]
        exact ih (by omega) level (by omega) nodeIdx hnodeIdx

/-! ### Chains and leaves -/

theorem eval_buildChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : OracleComp HashSpec Digest) (digit : Digit) :
    evalWithAnswerFn f (buildChain parameter lay tree leaf chainIdx secret digit.val) =
      (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val
          (evalWithAnswerFn f secret)),
        evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1)
          (evalWithAnswerFn f secret))) := by
  simp only [buildChain, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  congr 1
  have h := eval_recoverChain f parameter lay tree leaf chainIdx digit (evalWithAnswerFn f secret)
  simpa only [recoverChain] using h

/-- A built leaf: the chain values at the digits, and the specification's leaf. -/
theorem eval_buildLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    evalWithAnswerFn f (buildLeaf parameter lay tree leaf (secret leaf) digits) =
      (fun chainIdx => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0
          (digits chainIdx).val (evalWithAnswerFn f (secret leaf chainIdx))),
        honestNode f parameter lay tree (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx))
          0 leaf.val) := by
  rw [honestNode_zero_eq_leafHash]
  simp only [buildLeaf, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_buildChain,
    evalWithAnswerFn_pure, leafHash, eval_tweakableHash]
  rfl

/-! ### A layer's tree -/

theorem xor_div_lt {leaf height level : Nat} (hleaf : leaf < 2 ^ height) (hlevel : level < height) :
    Nat.xor (leaf / 2 ^ level) 1 < 2 ^ (height - level) := by
  have hdiv : leaf / 2 ^ level < 2 ^ (height - level) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    rwa [Nat.sub_add_cancel hlevel.le]
  exact Nat.xor_lt_two_pow hdiv (Nat.one_lt_two_pow (by omega))

theorem eval_buildLayerTree_table (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    let leaves := evalWithAnswerFn f (sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
      buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
        (if leafNat.val = leaf.val then digits else zeroEncoding))
    ∀ level, level ≤ layerHeight lay → ∀ nodeIdx, nodeIdx < 2 ^ (layerHeight lay - level) →
      evalWithAnswerFn f (buildLevels
        (fun level nodeIdx left right =>
          tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
        (layerHeight lay)
        (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
        (layerHeight lay)) level nodeIdx
        = honestNode f parameter lay tree
            (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)) level nodeIdx := by
  intro leaves level hlevel nodeIdx hnodeIdx
  apply eval_buildLevels f _ _ _
    (fun level nodeIdx => honestNode f parameter lay tree
      (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)) level nodeIdx)
  · intro nodeIdx hnodeIdx
    rw [dif_pos hnodeIdx]
    simp only [leaves, evalWithAnswerFn_sequenceFin, eval_buildLeaf]
    congr 1
    simp only [leafOfNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hnodeIdx
      (Nat.pow_le_pow_right (by omega) (layerHeight_le lay)))]
  · intro level nodeIdx _ _
    rw [eval_tweakableHash, honestNode_succ]
  · exact le_rfl
  · exact hlevel
  · exact hnodeIdx

/-- **A layer's tree, built once.** Its root is the specification's root, its path the
specification's path, and the values at the captured leaf the one-time signature's values. -/
theorem eval_buildLayerTree (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (hleaf : leaf.val < 2 ^ layerHeight lay) (digits : Encoding) :
    let result := evalWithAnswerFn f (buildLayerTree parameter lay tree secret leaf digits)
    let table := fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)
    result.1 = (fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (digits chainIdx).val (table leaf chainIdx)))
      ∧ (∀ level, level < layerHeight lay →
          result.2.1 level = honestNode f parameter lay tree table level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∧ result.2.2 = honestNode f parameter lay tree table (layerHeight lay) 0 := by
  intro result table
  have htable := eval_buildLayerTree_table f parameter lay tree secret leaf digits
  simp only [result, buildLayerTree, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  refine ⟨?_, ?_, ?_⟩
  · rw [dif_pos hleaf]
    simp only [evalWithAnswerFn_sequenceFin, eval_buildLeaf]
    funext chainIdx
    simp only [leafOfNat_val, if_true, table]
  · intro level hlevel
    exact htable level hlevel.le _ (xor_div_lt hleaf hlevel)
  · exact htable _ le_rfl 0 (by simp)

theorem eval_buildLayerTree_root (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (hleaf : leaf.val < 2 ^ layerHeight lay) (digits : Encoding) :
    (evalWithAnswerFn f (buildLayerTree parameter lay tree secret leaf digits)).2.2
      = evalWithAnswerFn f (treeRoot parameter lay tree
          (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx))) :=
  (eval_buildLayerTree f parameter lay tree secret leaf hleaf digits).2.2

/-- Key generation's root is the specification's root. -/
theorem eval_keygenRoot (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    evalWithAnswerFn f (keygenRoot parameter secret)
      = evalWithAnswerFn f (treeRoot parameter topLayer rootTree secret) := by
  have h := eval_buildLayerTree_root f parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩
    (Nat.two_pow_pos _) zeroEncoding
  simp only [evalWithAnswerFn_pure] at h
  unfold keygenRoot
  rw [evalWithAnswerFn_bind]
  -- `split` keeps the tree build opaque; generalizing it makes the kernel run the whole build
  split
  next values path root hresult =>
    rw [evalWithAnswerFn_pure, ← h, hresult]

theorem buildLayerTree_eq_table (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTree parameter lay tree secret leaf digits =
      (fun built : (Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest) =>
        ((if h : leaf.val < 2 ^ layerHeight lay then (built.1 ⟨leaf.val, h⟩).1 else fun _ => 0),
          (fun level => built.2 level (Nat.xor (leaf.val / 2 ^ level) 1)), built.2 (layerHeight lay) 0)) <$>
        buildLayerTable parameter lay tree secret leaf digits := by
  simp only [buildLayerTree, buildLayerTable, map_bind, bind_assoc, pure_bind, map_pure]

/-- Key generation's table is the specification's top tree, node for node inside the tree. -/
theorem eval_keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (level : Nat) (hlevel : level ≤ layerHeight topLayer) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (layerHeight topLayer - level)) :
    evalWithAnswerFn f (keygenTable parameter secret) level nodeIdx
      = honestNode f parameter topLayer rootTree secret level nodeIdx := by
  have htable := eval_buildLayerTree_table f parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
    level hlevel nodeIdx hnodeIdx
  simp only [evalWithAnswerFn_pure] at htable
  unfold keygenTable
  rw [evalWithAnswerFn_bind]
  -- `split` keeps the table build opaque; generalizing it makes the kernel run the whole build
  split
  next leaves table hresult =>
    rw [evalWithAnswerFn_pure]
    have hsnd := congrArg Prod.snd hresult
    simp only [buildLayerTable, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hsnd
    rw [← hsnd]
    exact htable

/-- The top-node getter agrees with the specification's top tree on every node of the cached region. -/
def TopAgrees (key : SecretKey) (topNode : Nat → Nat → OracleComp HashSpec Digest) : Prop :=
  ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
    evalWithAnswerFn f (topNode level nodeIdx)
      = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) level nodeIdx

/-- The key's node table is the specification's top tree under `f`. -/
abbrev KeyTopHonest (key : SecretKey) : Prop :=
  TopAgrees f key (fun level nodeIdx => pure (key.top level nodeIdx))

/-- The top tree's node table as key generation computes it under `f`. -/
noncomputable def honestTop (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    Nat → Nat → Digest :=
  evalWithAnswerFn f (keygenTable parameter secret)

theorem honestTop_root (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    honestTop f parameter secret (layerHeight topLayer) 0 =
      honestNode f parameter topLayer rootTree secret (layerHeight topLayer) 0 :=
  eval_keygenTable f parameter secret _ le_rfl 0 (by rw [Nat.sub_self, pow_zero]; exact Nat.one_pos)

/-- A key whose table is key generation's table under `f` passes the top-tree check. -/
theorem keyTopHonest_of_eq (key : SecretKey)
    (h : key.top = honestTop f key.parameter (key.otsSecret topLayer rootTree)) : KeyTopHonest f key := by
  intro level hlevel nodeIdx hnodeIdx
  have hheight : layerHeight topLayer = maxLayerHeight := rfl
  have heval := eval_keygenTable f key.parameter (key.otsSecret topLayer rootTree) level
    (by rw [hheight]; exact hlevel.le) nodeIdx (by rw [hheight]; exact hnodeIdx)
  rw [evalWithAnswerFn_pure, h]
  exact heval

/-- The key with key generation's table under `f`. -/
theorem keyTopHonest_withTop (key : SecretKey) :
    KeyTopHonest f { key with top := honestTop f key.parameter (key.otsSecret topLayer rootTree) } :=
  keyTopHonest_of_eq f _ rfl

/-! ### The forest -/

theorem eval_buildFtsTree (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → OracleComp HashSpec Digest) (leaf : FtsLeaf) :
    let result := evalWithAnswerFn f (buildFtsTree parameter index tree secret leaf)
    let table := fun leaf => evalWithAnswerFn f (secret leaf)
    result.1 = table leaf
      ∧ (∀ level, level < ftsTreeHeight →
          result.2.1 level = honestFtsNode f parameter index tree table level
            (Nat.xor (leaf.val / 2 ^ level) 1))
      ∧ result.2.2 = honestFtsNode f parameter index tree table ftsTreeHeight 0 := by
  intro result table
  have htable : ∀ level, level ≤ ftsTreeHeight → ∀ nodeIdx, nodeIdx < 2 ^ (ftsTreeHeight - level) →
      evalWithAnswerFn f (buildLevels
        (fun level nodeIdx left right =>
          tweakableHash parameter (.ftsNode index tree level nodeIdx) (nodePayload left right))
        ftsTreeHeight
        (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then
          ((evalWithAnswerFn f (sequenceFin fun leafIdx : FtsLeaf => do
            let value ← secret leafIdx
            let hashed ← ftsLeafHash parameter index tree leafIdx value
            return (value, hashed))) ⟨nodeIdx, h⟩).2 else 0)
        ftsTreeHeight) level nodeIdx
        = honestFtsNode f parameter index tree table level nodeIdx := by
    apply eval_buildLevels f _ _ _ (fun level nodeIdx => honestFtsNode f parameter index tree table level nodeIdx)
    · intro nodeIdx hnodeIdx
      rw [dif_pos hnodeIdx]
      have h := honestFtsNode_zero f parameter index tree table ⟨nodeIdx, hnodeIdx⟩
      simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        ftsLeafHash, eval_tweakableHash] at h ⊢
      exact h.symm
    · intro level nodeIdx _ _
      rw [eval_tweakableHash, honestFtsNode_succ]
    · exact le_rfl
  simp only [result, buildFtsTree, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  refine ⟨?_, ?_, ?_⟩
  · simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, table]
  · intro level hlevel
    exact htable level hlevel.le _ (xor_div_lt leaf.isLt hlevel)
  · exact htable _ le_rfl 0 (by simp)

/-- **The forest, built once.** The opened secrets, the specification's opening and the
specification's few-time key. -/
theorem eval_buildForest (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → OracleComp HashSpec Digest) (leaves : IndexGroup → FtsLeaf) :
    let result := evalWithAnswerFn f (buildForest parameter index secret leaves)
    let table := fun tree leaf => evalWithAnswerFn f (secret tree leaf)
    result.1 = (fun tree => table tree (leaves (ftsIndexOf tree)))
      ∧ result.2.1 = evalWithAnswerFn f (ftsOpen parameter index leaves table)
      ∧ result.2.2 = evalWithAnswerFn f (ftsKey parameter index table) := by
  intro result table
  have htree := fun tree => eval_buildFtsTree f parameter index tree (secret tree) (leaves (ftsIndexOf tree))
  simp only [result, buildForest, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    evalWithAnswerFn_sequenceFin]
  refine ⟨?_, ?_, ?_⟩
  · funext tree
    exact (htree tree).1
  · simp only [ftsOpen, evalWithAnswerFn_sequenceFin]
    funext tree level
    exact (htree tree).2.1 level.val level.isLt
  · simp only [ftsKey, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_tweakableHash]
    congr 3
    exact congrArg ftsRootsPayload (funext fun tree => (htree tree).2.2)

/-! ### The layers -/

theorem eval_otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat) :
    evalWithAnswerFn f (otsSignFrom parameter lay tree leaf secret message attempts counter)
      = (evalWithAnswerFn f (encodingSearch parameter lay tree leaf message attempts counter)).map
          fun result => (result.1, fun chainIdx => evalWithAnswerFn f
            (chainWalk parameter lay tree leaf chainIdx 0 (result.2 chainIdx).val (secret chainIdx))) := by
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
      simp only [otsSignFrom, encodingSearch, evalWithAnswerFn_bind, encode_eq]
      cases evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message
          (BitVec.ofNat counterBits counter)) with
      | none => exact ih (counter + 1)
      | some word =>
          simp only [evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure,
            Option.map_some]

/-- A layer's output padded to the tallest layer, the shape of the specification's `signLayer`. -/
def LayerOutput.toPadded (lay : Layer) (output : LayerOutput) : PaddedLayer :=
  (output.1, output.2.1, fun level => if level.val < layerHeight lay then output.2.2 level.val else 0)

theorem LayerOutput.toSignature_eq (lay : Layer) (output : LayerOutput) :
    LayerOutput.toSignature lay output = LayerSignature.ofPadded lay (LayerOutput.toPadded lay output) := by
  simp only [LayerOutput.toSignature, LayerOutput.toPadded, LayerSignature.ofPadded, Fin.val_castLE]
  congr
  funext level
  rw [if_pos level.isLt]

theorem eval_treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    evalWithAnswerFn f (treePath parameter lay tree secret leaf) = fun level =>
      if level.val < layerHeight lay then
        honestNode f parameter lay tree secret level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
      else 0 := by
  simp only [treePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs <;> rfl

/-- **The layers, each built once, sign what the specification signs.** Walking the layers from
`remaining - 1` down to `0`, starting from the specification's message for layer `remaining - 1`,
the built layers fail exactly when some specification layer below `remaining` fails, and otherwise
carry the specification's parts. -/
theorem eval_signLayers (key : SecretKey) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hsecret : ∀ lay tree leaf chainIdx,
      evalWithAnswerFn f (secret lay tree leaf chainIdx) = key.otsSecret lay tree leaf chainIdx)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (htop : TopAgrees f key topNode)
    (remaining : Nat) (hremaining : remaining ≤ numLayers) (message : Digest)
    (hmessage : ∀ h : 0 < remaining,
      message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩)) :
    match evalWithAnswerFn f (signLayers key.parameter index secret topNode remaining message) with
    | none => ∃ lay : Layer, lay.val < remaining ∧ evalWithAnswerFn f (signLayer key index lay) = none
    | some parts => ∀ lay : Layer, lay.val < remaining →
        evalWithAnswerFn f (signLayer key index lay) = some (LayerOutput.toPadded lay (parts lay)) := by
  induction remaining generalizing message with
  | zero =>
      simp only [signLayers, evalWithAnswerFn_pure]
      intro lay hlay
      omega
  | succ remaining ih =>
      have hlayer : remaining < numLayers := by omega
      let lay : Layer := ⟨remaining, hlayer⟩
      have hmsg : message = evalWithAnswerFn f (layerMessage key index lay) := hmessage (by omega)
      have htable : (fun leaf chainIdx => evalWithAnswerFn f
          (secret lay (treeIndexAt index lay) leaf chainIdx)) =
          key.otsSecret lay (treeIndexAt index lay) := by
        funext leaf chainIdx
        exact hsecret _ _ _ _
      have hspec : evalWithAnswerFn f (signLayer key index lay) =
          (evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0)).map fun result =>
              (result.1, fun chainIdx => evalWithAnswerFn f
                (chainWalk key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx 0
                  (result.2 chainIdx).val
                  (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)),
                evalWithAnswerFn f (treePath key.parameter lay (treeIndexAt index lay)
                  (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay))) := by
        simp only [signLayer, evalWithAnswerFn_bind, ← hmsg, otsSign, eval_otsSignFrom]
        cases evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0) with
        | none => rfl
        | some result => simp only [Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      by_cases hzero : remaining = 0
      · subst hzero
        have htree : treeIndexAt index lay = rootTree := Fin.ext (treeIndexAt_topLayer index)
        simp only [signLayers, dif_pos hlayer, ↓reduceIte, signTopLayer, evalWithAnswerFn_bind]
        rw [show topLayer = lay from rfl]
        cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0) with
        | none =>
            refine ⟨lay, Nat.lt_succ_self _, ?_⟩
            rw [hspec, hsearch]
            rfl
        | some result =>
            obtain ⟨counter, word⟩ := result
            simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalWithAnswerFn_sequenceFin]
            intro other hother
            have hother' : other = lay := Fin.ext (by simp [lay]; omega)
            rw [hother', if_pos rfl, hspec, hsearch]
            simp only [Option.map_some, LayerOutput.toPadded, Option.some.injEq, Prod.mk.injEq, true_and]
            refine ⟨?_, ?_⟩
            · funext chainIdx
              rw [hsecret]
            · rw [eval_treePath]
              funext level
              have hheight : layerHeight lay = maxLayerHeight := rfl
              rw [hheight]
              split_ifs with hlevel
              · rw [htree]
                exact (htop level.val hlevel _ (xor_div_lt (leafIndexAt_lt index lay) hlevel)).symm
              · exact absurd level.isLt hlevel
      simp only [signLayers, dif_pos hlayer, if_neg hzero, evalWithAnswerFn_bind]
      cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
          (leafIndexAt index lay) message encodingAttemptLimit 0) with
      | none =>
          refine ⟨lay, Nat.lt_succ_self _, ?_⟩
          rw [hspec, hsearch]
          rfl
      | some result =>
          obtain ⟨counter, word⟩ := result
          have hbuild := eval_buildLayerTree f key.parameter lay (treeIndexAt index lay)
            (secret lay (treeIndexAt index lay)) (leafIndexAt index lay) (leafIndexAt_lt index lay) word
          rw [htable] at hbuild
          simp only [evalWithAnswerFn_bind]
          revert hbuild
          generalize evalWithAnswerFn f (buildLayerTree key.parameter lay (treeIndexAt index lay)
            (secret lay (treeIndexAt index lay)) (leafIndexAt index lay) word) = built
          rcases built with ⟨values, path, root⟩
          rintro ⟨hvalues, hpath, hroot⟩
          simp only at hvalues hpath hroot
          have hnext : ∀ h : 0 < remaining,
              root = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩) := by
            intro h
            have hbelow : remaining - 1 + 1 < numLayers := by omega
            rw [layerMessage, dif_pos hbelow]
            have hlay : (⟨remaining - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            rw [hlay, hroot]
            simp only [treeRoot, honestNode]
          have hrest := ih (by omega) root hnext
          revert hrest
          cases evalWithAnswerFn f (signLayers key.parameter index secret topNode remaining root) with
          | none =>
              rintro ⟨other, hother, hnone⟩
              exact ⟨other, by omega, hnone⟩
          | some rest =>
              intro hrest other hother
              by_cases hl : other = lay
              · subst hl
                have hif : (if lay = (⟨remaining, hlayer⟩ : Layer) then
                    (counter, (values, path, root).1, (values, path, root).2.1) else rest lay) =
                    (counter, values, path) := if_pos rfl
                simp only [hif]
                rw [hspec, hsearch]
                simp only [Option.map_some, LayerOutput.toPadded, Option.some.injEq, Prod.mk.injEq,
                  true_and]
                refine ⟨hvalues.symm, ?_⟩
                rw [eval_treePath]
                funext level
                split_ifs with hlevel
                · exact (hpath level.val hlevel).symm
                · rfl
              · have hif : (if other = (⟨remaining, hlayer⟩ : Layer) then
                    (counter, values, path) else rest other) = rest other := if_neg hl
                simp only [hif]
                exact hrest other (by
                  have : other.val ≠ remaining := fun h => hl (Fin.ext h)
                  omega)

/-! ### The signature -/

theorem signAfterDigest_eq_signFrom (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) :
    (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signFrom key.parameter index (fun tree leaf => pure (key.ftsSecret index tree leaf))
        (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx))
        (fun level nodeIdx => pure (key.top level nodeIdx)) randomness leaves := by
  rw [signAfterDigest]

/-- The signature the specification produces after the digest loop, under `f`. -/
def signatureValue (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : Option Signature :=
  (sequenceFin (m := Option) fun lay => evalWithAnswerFn f (signLayer key index lay)).map fun parts =>
    { randomness := randomness
      ftsSecret := fun tree => key.ftsSecret index tree (leaves (ftsIndexOf tree))
      ftsPath := evalWithAnswerFn f (ftsOpen key.parameter index leaves (key.ftsSecret index))
      layers := fun lay => LayerSignature.ofPadded lay (parts lay) }

theorem layerMessage_bottomLayer_eq (key : SecretKey) (index : Index) :
    (layerMessage key index bottomLayer : OracleComp HashSpec Digest) =
      ftsKey key.parameter index (key.ftsSecret index) := by
  rw [layerMessage, dif_neg (by decide)]

/-- **The signer computes the specification's signature.** -/
theorem eval_signFrom (key : SecretKey) (index : Index)
    (ftsGet : FtsTree → FtsLeaf → OracleComp HashSpec Digest)
    (otsGet : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hfts : ∀ tree leaf, evalWithAnswerFn f (ftsGet tree leaf) = key.ftsSecret index tree leaf)
    (hots : ∀ lay tree leaf chainIdx,
      evalWithAnswerFn f (otsGet lay tree leaf chainIdx) = key.otsSecret lay tree leaf chainIdx)
    (topGet : Nat → Nat → OracleComp HashSpec Digest) (htop : TopAgrees f key topGet)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (signFrom key.parameter index ftsGet otsGet topGet randomness leaves) =
      signatureValue f key randomness index leaves := by
  have hforest := eval_buildForest f key.parameter index ftsGet leaves
  have htable : (fun tree leaf => evalWithAnswerFn f (ftsGet tree leaf)) = key.ftsSecret index := by
    funext tree leaf
    exact hfts tree leaf
  rw [htable] at hforest
  unfold signFrom
  rw [evalWithAnswerFn_bind]
  revert hforest
  generalize evalWithAnswerFn f (buildForest key.parameter index ftsGet leaves) = forest
  rcases forest with ⟨secrets, ftsPath, ftsPublicKey⟩
  rintro ⟨hsecrets, hpath, hkey⟩
  simp only at hsecrets hpath hkey
  have hlayers := eval_signLayers f key index otsGet hots topGet htop numLayers le_rfl ftsPublicKey (by
    intro _
    rw [hkey]
    change _ = evalWithAnswerFn f (layerMessage key index bottomLayer)
    rw [layerMessage_bottomLayer_eq])
  simp only [evalWithAnswerFn_bind]
  unfold signatureValue
  rw [sequenceFin_option_eq]
  revert hlayers
  cases evalWithAnswerFn f (signLayers key.parameter index otsGet topGet numLayers ftsPublicKey) with
  | none =>
      rintro ⟨lay, _, hnone⟩
      rw [dif_neg (fun hall => by have := hall lay; rw [hnone] at this; simp at this)]
      rfl
  | some parts =>
      intro hparts
      have hall : ∀ lay, (evalWithAnswerFn f (signLayer key index lay)).isSome := fun lay => by
        rw [hparts lay lay.isLt]
        rfl
      rw [dif_pos hall]
      simp only [evalWithAnswerFn_pure, Option.map_some, Option.some.injEq]
      rw [hsecrets, hpath]
      congr 1
      funext lay
      rw [LayerOutput.toSignature_eq]
      congr 1
      simp only [hparts lay lay.isLt, Option.get_some]

theorem eval_signAfterDigest (key : SecretKey) (htop : KeyTopHonest f key) (randomness : Randomness)
    (index : Index) (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signatureValue f key randomness index leaves := by
  rw [signAfterDigest_eq_signFrom]
  exact eval_signFrom f key index _ _ (fun _ _ => rfl) (fun _ _ _ _ => rfl) _ htop randomness leaves

/-! ### The signer reads only the cached region of the table -/

/-- Two top-node getters that agree on the cached region. -/
def TopRegionEq {m : Type → Type} (topNode topNode' : Nat → Nat → m Digest) : Prop :=
  ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
    topNode level nodeIdx = topNode' level nodeIdx

theorem signTopLayer_congr_top {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → m Digest) (topNode topNode' : Nat → Nat → m Digest)
    (htop : TopRegionEq topNode topNode') (message : Digest) :
    signTopLayer parameter index secret topNode message = signTopLayer parameter index secret topNode' message := by
  have hpath : (fun level : Fin maxLayerHeight =>
      topNode level.val (Nat.xor ((leafIndexAt index topLayer).val / 2 ^ level.val) 1)) =
      (fun level : Fin maxLayerHeight =>
        topNode' level.val (Nat.xor ((leafIndexAt index topLayer).val / 2 ^ level.val) 1)) :=
    funext fun level => htop _ level.isLt _ (xor_div_lt (leafIndexAt_lt index topLayer) level.isLt)
  simp only [signTopLayer, hpath]

theorem signLayers_congr_top {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) (topNode topNode' : Nat → Nat → m Digest)
    (htop : TopRegionEq topNode topNode') (remaining : Nat) (message : Digest) :
    signLayers parameter index secret topNode remaining message =
      signLayers parameter index secret topNode' remaining message := by
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
      rw [signLayers, signLayers]
      split
      · split
        · rw [signTopLayer_congr_top parameter index _ topNode topNode' htop]
        · simp only [ih]
      · rfl

theorem signAfterDigest_congr_top (key key' : SecretKey) (hparameter : key.parameter = key'.parameter)
    (hots : key.otsSecret = key'.otsSecret) (hfts : key.ftsSecret = key'.ftsSecret)
    (htop : TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (key.top level nodeIdx))
      (fun level nodeIdx => pure (key'.top level nodeIdx)))
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signAfterDigest key' randomness index leaves := by
  rw [signAfterDigest_eq_signFrom, signAfterDigest_eq_signFrom, ← hparameter, ← hots, ← hfts]
  unfold signFrom
  simp only [signLayers_congr_top key.parameter index _ _ _ htop]

end SigGolfCandidate.Base4Candidate.Ideal.Concrete

end AlternateRecoveryPort12

/-! Alternate proof port from the original promoted FORS baseline: Completeness/Paired.lean -/
section AlternateRecoveryPort13

/-!
# The paired builders, evaluated

The seeded signer derives the secrets of two chains (or two few-time leaves) with one query and walks
the pair's members right after it. Under a fixed answer function `f` the order of the work does not
matter, only what each member is handed: member `2k` gets the first half of the pair's answer and
member `2k + 1` the second. So each paired builder evaluates to its per-secret counterpart run with
the secrets `unpairedOts f g` (resp. `unpairedFts f g`) read off the evaluated pair getter `g`, and
everything proved about the per-secret builders (`BuildEval.lean`) applies.
-/

open OracleComp

namespace SigGolfCandidate.Base4Candidate.Ideal.Completeness

open Concrete

variable (f : QueryImpl HashSpec Id)

/-! ## Members of a pair -/

theorem evenChain_chainPairOf {chainIdx : ChainIndex} (h : chainIdx.val % 2 = 0) :
    evenChain (chainPairOf chainIdx) = chainIdx := by
  apply Fin.ext
  simp only [evenChain, chainPairOf]
  omega

theorem oddChain_chainPairOf {chainIdx : ChainIndex} (h : ¬ chainIdx.val % 2 = 0) :
    oddChain (chainPairOf chainIdx) = chainIdx := by
  apply Fin.ext
  simp only [oddChain, chainPairOf]
  omega

theorem evenFtsLeaf_ftsPairOf {leaf : FtsLeaf} (h : leaf.val % 2 = 0) :
    evenFtsLeaf (ftsPairOf leaf) = leaf := by
  apply Fin.ext
  simp only [evenFtsLeaf, ftsPairOf]
  omega

theorem oddFtsLeaf_ftsPairOf {leaf : FtsLeaf} (h : ¬ leaf.val % 2 = 0) :
    oddFtsLeaf (ftsPairOf leaf) = leaf := by
  apply Fin.ext
  simp only [oddFtsLeaf, ftsPairOf]
  omega

/-- Spreading a pairwise map of the members is mapping the spread members. -/
theorem unpairChains_map {α β : Type} (F : ChainIndex → α → β) (pairs : ChainPair → α × α)
    (mapped : ChainPair → β × β)
    (hmapped : ∀ pair, mapped pair = (F (evenChain pair) (pairs pair).1, F (oddChain pair) (pairs pair).2))
    (chainIdx : ChainIndex) :
    unpairChains mapped chainIdx = F chainIdx (unpairChains pairs chainIdx) := by
  unfold unpairChains
  split
  next h => rw [hmapped, evenChain_chainPairOf h]
  next h => rw [hmapped, oddChain_chainPairOf h]

theorem unpairFtsLeaves_map {α β : Type} (F : FtsLeaf → α → β) (pairs : FtsPair → α × α)
    (mapped : FtsPair → β × β)
    (hmapped : ∀ pair, mapped pair = (F (evenFtsLeaf pair) (pairs pair).1, F (oddFtsLeaf pair) (pairs pair).2))
    (leaf : FtsLeaf) :
    unpairFtsLeaves mapped leaf = F leaf (unpairFtsLeaves pairs leaf) := by
  unfold unpairFtsLeaves
  split
  next h => rw [hmapped, evenFtsLeaf_ftsPairOf h]
  next h => rw [hmapped, oddFtsLeaf_ftsPairOf h]

/-- The chain secrets a pair getter hands out under `f`. -/
def unpairedOts (g : ChainPair → OracleComp HashSpec (Digest × Digest)) : ChainIndex → Digest :=
  unpairChains fun pair => evalWithAnswerFn f (g pair)

/-- The few-time leaf secrets a pair getter hands out under `f`. -/
def unpairedFts (g : FtsPair → OracleComp HashSpec (Digest × Digest)) : FtsLeaf → Digest :=
  unpairFtsLeaves fun pair => evalWithAnswerFn f (g pair)

/-- Evaluations agree along a bind when the heads agree and the continuations agree pointwise. -/
theorem eval_bind_congr {α β : Type} {x x' : OracleComp HashSpec α}
    {k k' : α → OracleComp HashSpec β}
    (hx : evalWithAnswerFn f x = evalWithAnswerFn f x')
    (hk : ∀ v, evalWithAnswerFn f (k v) = evalWithAnswerFn f (k' v)) :
    evalWithAnswerFn f (x >>= k) = evalWithAnswerFn f (x' >>= k') := by
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hx, hk]

/-! ## Layer trees -/

theorem eval_buildLeafPaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (g : ChainPair → OracleComp HashSpec (Digest × Digest)) (digits : Encoding) :
    evalWithAnswerFn f (buildLeafPaired parameter lay tree leaf g digits)
      = evalWithAnswerFn f (buildLeaf parameter lay tree leaf
          (fun chainIdx => pure (unpairedOts f g chainIdx)) digits) := by
  have hchains := unpairChains_map
    (fun chainIdx (secret : Digest) => evalWithAnswerFn f
      (buildChain parameter lay tree leaf chainIdx (pure secret) (digits chainIdx).val))
    (fun pair => evalWithAnswerFn f (g pair))
  simp only [buildLeafPaired, buildLeaf, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    evalWithAnswerFn_pure]
  simp only [hchains _ (fun _ => rfl), unpairedOts]

theorem eval_buildLayerTablePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (g : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)) (leaf : LeafIndex)
    (digits : Encoding) :
    evalWithAnswerFn f (buildLayerTablePaired parameter lay tree g leaf digits)
      = evalWithAnswerFn f (buildLayerTable parameter lay tree
          (fun leaf chainIdx => pure (unpairedOts f (g leaf) chainIdx)) leaf digits) := by
  unfold buildLayerTablePaired buildLayerTable
  refine eval_bind_congr f ?_ (fun _ => rfl)
  simp only [evalWithAnswerFn_sequenceFin, eval_buildLeafPaired]

theorem eval_buildLayerTreePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (g : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)) (leaf : LeafIndex)
    (digits : Encoding) :
    evalWithAnswerFn f (buildLayerTreePaired parameter lay tree g leaf digits)
      = evalWithAnswerFn f (buildLayerTree parameter lay tree
          (fun leaf chainIdx => pure (unpairedOts f (g leaf) chainIdx)) leaf digits) := by
  rw [buildLayerTree_eq_table, evalWithAnswerFn_map]
  unfold buildLayerTreePaired
  rw [evalWithAnswerFn_bind, eval_buildLayerTablePaired]
  rfl

/-! ## The forest -/

theorem eval_buildFtsTreePaired (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (g : FtsPair → OracleComp HashSpec (Digest × Digest)) (leaf : FtsLeaf) :
    evalWithAnswerFn f (buildFtsTreePaired parameter index tree g leaf)
      = evalWithAnswerFn f (buildFtsTree parameter index tree
          (fun leaf => pure (unpairedFts f g leaf)) leaf) := by
  have hleaves := unpairFtsLeaves_map
    (fun leaf (secret : Digest) =>
      (secret, evalWithAnswerFn f (ftsLeafHash parameter index tree leaf secret)))
    (fun pair => evalWithAnswerFn f (g pair))
  unfold buildFtsTreePaired buildFtsTree
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure,
    hleaves _ (fun _ => rfl), unpairedFts]

theorem eval_buildForestPaired (parameter : PublicParameter) (index : Index)
    (g : FtsTree → FtsPair → OracleComp HashSpec (Digest × Digest)) (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (buildForestPaired parameter index g leaves)
      = evalWithAnswerFn f (buildForest parameter index
          (fun tree leaf => pure (unpairedFts f (g tree) leaf)) leaves) := by
  unfold buildForestPaired buildForest
  refine eval_bind_congr f ?_ (fun _ => rfl)
  rw [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_sequenceFin]
  funext tree
  exact eval_buildFtsTreePaired f parameter index tree (g tree) (leaves (ftsIndexOf tree))

/-! ## Signing -/

theorem eval_signTopLayerPaired (parameter : PublicParameter) (index : Index)
    (g : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (message : Digest) :
    evalWithAnswerFn f (signTopLayerPaired parameter index g topNode message)
      = evalWithAnswerFn f (signTopLayer parameter index
          (fun leaf chainIdx => pure (unpairedOts f (g leaf) chainIdx)) topNode message) := by
  unfold signTopLayerPaired signTopLayer
  refine eval_bind_congr f rfl (fun result => ?_)
  rcases result with _ | ⟨counter, encoding⟩
  · rfl
  · have hvalues := unpairChains_map
      (fun chainIdx (secret : Digest) => evalWithAnswerFn f (chainWalk parameter topLayer
        (treeIndexAt index topLayer) (leafIndexAt index topLayer) chainIdx 0
        (encoding chainIdx).val secret))
      (fun pair => evalWithAnswerFn f (g (leafIndexAt index topLayer) pair))
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]
    rw [show (unpairChains fun pair =>
        (evalWithAnswerFn f (chainWalk parameter topLayer (treeIndexAt index topLayer)
          (leafIndexAt index topLayer) (evenChain pair) 0 (encoding (evenChain pair)).val
          (evalWithAnswerFn f (g (leafIndexAt index topLayer) pair)).1),
        evalWithAnswerFn f (chainWalk parameter topLayer (treeIndexAt index topLayer)
          (leafIndexAt index topLayer) (oddChain pair) 0 (encoding (oddChain pair)).val
          (evalWithAnswerFn f (g (leafIndexAt index topLayer) pair)).2)))
        = fun chainIdx => evalWithAnswerFn f (chainWalk parameter topLayer (treeIndexAt index topLayer)
          (leafIndexAt index topLayer) chainIdx 0 (encoding chainIdx).val
          (unpairedOts f (g (leafIndexAt index topLayer)) chainIdx)) from
      funext fun chainIdx => hvalues _ (fun _ => rfl) chainIdx]

theorem eval_signLayersPaired (parameter : PublicParameter) (index : Index)
    (g : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) :
    ∀ (remaining : Nat) (message : Digest),
      evalWithAnswerFn f (signLayersPaired parameter index g topNode remaining message)
        = evalWithAnswerFn f (signLayers parameter index
            (fun lay tree leaf chainIdx => pure (unpairedOts f (g lay tree leaf) chainIdx))
            topNode remaining message) := by
  intro remaining
  induction remaining with
  | zero => intro message; rfl
  | succ remaining ih =>
      intro message
      rw [signLayersPaired, signLayers]
      split
      next hlayer =>
        split
        next hzero =>
          exact eval_bind_congr f (eval_signTopLayerPaired f parameter index _ topNode message)
            (fun _ => rfl)
        next hzero =>
          refine eval_bind_congr f rfl (fun result => ?_)
          rcases result with _ | ⟨counter, encoding⟩
          · rfl
          · refine eval_bind_congr f (eval_buildLayerTreePaired f _ _ _ _ _ _) (fun built => ?_)
            rcases built with ⟨values, path, root⟩
            exact eval_bind_congr f (ih root) (fun _ => rfl)
      next hlayer => rfl

/-- **The paired signer evaluates like the per-secret signer**, with the secrets the pair getters hand
out under `f`. -/
theorem eval_signFromPaired (parameter : PublicParameter) (index : Index)
    (ftsGet : FtsTree → FtsPair → OracleComp HashSpec (Digest × Digest))
    (otsGet : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (signFromPaired parameter index ftsGet otsGet topNode randomness leaves)
      = evalWithAnswerFn f (signFrom parameter index
          (fun tree leaf => pure (unpairedFts f (ftsGet tree) leaf))
          (fun lay tree leaf chainIdx => pure (unpairedOts f (otsGet lay tree leaf) chainIdx))
          topNode randomness leaves) := by
  unfold signFromPaired signFrom
  refine eval_bind_congr f (eval_buildForestPaired f _ _ _ _) (fun forest => ?_)
  rcases forest with ⟨secrets, ftsPath, ftsPublicKey⟩
  exact eval_bind_congr f (eval_signLayersPaired f _ _ _ _ _ _) (fun _ => rfl)

end SigGolfCandidate.Base4Candidate.Ideal.Completeness

end AlternateRecoveryPort13

/-! Alternate proof port from the original promoted FORS baseline: Completeness/Recovery.lean -/
section AlternateRecoveryPort14

/-!
# Recovery: what the signer produces, the verifier accepts

The specification's §sec:ver argues that each one-time recovery returns the leaf the signer built
and each authentication path returns its root, so verification accepts whenever signing succeeds.
This file is that argument.

Everything is deterministic once the oracle is fixed, so the whole file works under an answer
function `f`: `evalWithAnswerFn f` reads each algorithm as a plain function. Nothing here is
probabilistic, and nothing depends on the answers being uniform.

The signer builds each tree once; `BuildEval.lean` shows that under `f` it computes the recursive
specification of `IdealStatement.lean` (`eval_signFrom`, `eval_buildLayerTree`), read with the
secrets the seed derives under `f`. So the argument is made once, against the specification: each
layer's counter search returns a counter below `C_max` that encodes its message, the verifier's
chains end at the specification's endpoints, its folds climb the specification's trees, and the
root it reaches at the top is the public key's.
-/

open OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SigGolfCandidate.Base4Candidate.Ideal.Completeness

open Concrete

-- the attempt limits are `2 ^ 20` and `2 ^ 22`; unfolding them unfolds the loops that many times
attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

variable (f : QueryImpl HashSpec Id)

/-! ## Climbing a tree

The signer's authentication path is the sibling at every level, so folding the signed leaf through
it climbs the honest tree: one level at a time, the pair the verifier hashes is exactly the pair the
specification's node hashed. -/

private theorem even_parts (value : Nat) (hbit : value.testBit 0 = false) :
    value = 2 * (value / 2) ∧ Nat.xor value 1 = 2 * (value / 2) + 1 := by
  have heven : Even value := Nat.even_iff.mpr (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  have hmod : value % 2 = 0 := Nat.even_iff.mp heven
  refine ⟨by omega, ?_⟩
  show value ^^^ 1 = _
  rw [Nat.xor_one_of_even heven]
  omega

private theorem odd_parts (value : Nat) (hbit : value.testBit 0 = true) :
    value = 2 * (value / 2) + 1 ∧ Nat.xor value 1 = 2 * (value / 2) := by
  have hodd : Odd value := Nat.odd_iff.mpr (Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit)
  have hmod : value % 2 = 1 := Nat.odd_iff.mp hodd
  refine ⟨by omega, ?_⟩
  show value ^^^ 1 = _
  rw [Nat.xor_one_of_odd hodd]
  omega

private theorem testBit_div_pow (value level : Nat) :
    (value / 2 ^ level).testBit 0 = value.testBit level := by
  simpa only [Nat.zero_add] using (Nat.testBit_add value 0 level).symm

private theorem parts_odd (value level : Nat) (hbit : value.testBit level = true) :
    value / 2 ^ level = 2 * (value / 2 ^ (level + 1)) + 1
      ∧ Nat.xor (value / 2 ^ level) 1 = 2 * (value / 2 ^ (level + 1)) := by
  have hdiv : value / 2 ^ (level + 1) = value / 2 ^ level / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv]
  exact odd_parts (value / 2 ^ level) (by rw [testBit_div_pow, hbit])

private theorem parts_even (value level : Nat) (hbit : value.testBit level = false) :
    value / 2 ^ level = 2 * (value / 2 ^ (level + 1))
      ∧ Nat.xor (value / 2 ^ level) 1 = 2 * (value / 2 ^ (level + 1)) + 1 := by
  have hdiv : value / 2 ^ (level + 1) = value / 2 ^ level / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv]
  exact even_parts (value / 2 ^ level) (by rw [testBit_div_pow, hbit])

/-- Folding the honest leaf through the honest siblings reaches the honest node above it. -/
theorem eval_treeFold_honest (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels : Nat, (∀ level, level < levels →
        path level = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (treeFold parameter lay tree leaf path levels
          (honestNode f parameter lay tree secret 0 leaf.val) : OracleComp HashSpec Digest)
        = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels) := by
  intro levels
  induction levels with
  | zero => intro _; simp [treeFold]
  | succ levels ih =>
      intro hpath
      rw [treeFold, evalWithAnswerFn_bind,
        ih (fun level hlevel => hpath level (Nat.lt_succ_of_lt hlevel))]
      rw [hpath levels (Nat.lt_succ_self levels), honestNode_succ]
      cases hbit : leaf.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd leaf.val levels hbit
          simp only [if_true, Concrete.eval_tweakableHash]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, if_false, Concrete.eval_tweakableHash]
          rw [hsib, hcur]

/-- Folding an opened few-time secret through its siblings reaches the honest node above it. -/
theorem eval_ftsFold_honest (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) :
    ∀ levels : Nat, levels ≤ ftsTreeHeight →
      (∀ (level : Nat) (hlevel : level < ftsTreeHeight), level < levels →
        path ⟨level, hlevel⟩ = honestFtsNode f parameter index tree secret level
          (Nat.xor (leaf.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (ftsFold parameter index tree leaf path levels
          (honestFtsNode f parameter index tree secret 0 leaf.val) : OracleComp HashSpec Digest)
        = honestFtsNode f parameter index tree secret levels (leaf.val / 2 ^ levels) := by
  intro levels
  induction levels with
  | zero => intro _ _; simp [ftsFold]
  | succ levels ih =>
      intro hheight hpath
      have hlevels : levels < ftsTreeHeight := Nat.lt_of_succ_le hheight
      rw [ftsFold, evalWithAnswerFn_bind,
        ih (Nat.le_of_succ_le hheight)
          (fun level hlevel hlt => hpath level hlevel (Nat.lt_succ_of_lt hlt))]
      rw [dif_pos hlevels, hpath levels hlevels (Nat.lt_succ_self levels), honestFtsNode_succ]
      cases hbit : leaf.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd leaf.val levels hbit
          simp only [if_true, Concrete.eval_tweakableHash]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, if_false, Concrete.eval_tweakableHash]
          rw [hsib, hcur]

/-- The verifier recovers the specification's few-time public key from the opened secrets and the
specification's opening. -/
theorem eval_ftsRecover_honest (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsRecover parameter index leaves
        (fun tree => secret tree (leaves (ftsIndexOf tree)))
        (evalWithAnswerFn f (ftsOpen parameter index leaves secret)) : OracleComp HashSpec Digest)
      = evalWithAnswerFn f (ftsKey parameter index secret : OracleComp HashSpec Digest) := by
  have hroot : ∀ tree : FtsTree,
      evalWithAnswerFn f (ftsFold parameter index tree (leaves (ftsIndexOf tree))
          (evalWithAnswerFn f (ftsOpen parameter index leaves secret) tree) ftsTreeHeight
          (evalWithAnswerFn f (ftsLeafHash parameter index tree (leaves (ftsIndexOf tree))
            (secret tree (leaves (ftsIndexOf tree))) : OracleComp HashSpec Digest))
          : OracleComp HashSpec Digest)
        = honestFtsNode f parameter index tree (secret tree) ftsTreeHeight 0 := by
    intro tree
    have hzero : evalWithAnswerFn f (ftsLeafHash parameter index tree (leaves (ftsIndexOf tree))
        (secret tree (leaves (ftsIndexOf tree))) : OracleComp HashSpec Digest)
        = honestFtsNode f parameter index tree (secret tree) 0 (leaves (ftsIndexOf tree)).val := by
      simp only [honestFtsNode, ftsNode_zero_eq, ftsLeafOfNat_val]
    rw [hzero, eval_ftsFold_honest f parameter index tree (secret tree) (leaves (ftsIndexOf tree)) _
      ftsTreeHeight (Nat.le_refl _) (fun level hlevel _ => by
        simp only [ftsOpen, evalWithAnswerFn_sequenceFin, honestFtsNode])]
    congr 1
    exact Nat.div_eq_of_lt (leaves (ftsIndexOf tree)).isLt
  simp only [ftsRecover, ftsKey, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, hroot,
    honestFtsNode]

/-! ## One layer

A layer's counter search returns a counter below `C_max` that encodes the layer's message; the
signer's chain values are the partial walks at that encoding, so the verifier's halves of the chains
reach the specification's endpoints and the leaf it hashes is the specification's leaf. -/

/-- What a successful counter search returned: an encoding of the message, at a counter it tried. -/
theorem encodingSearch_spec (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) :
    ∀ (attempts start : Nat) {counter : Counter} {word : Encoding}, start + attempts ≤ 2 ^ 32 →
      evalWithAnswerFn f (encodingSearch parameter lay tree leaf message attempts start
          : OracleComp HashSpec (Option (Counter × Encoding))) = some (counter, word) →
      evalWithAnswerFn f (encode parameter lay tree leaf message counter
          : OracleComp HashSpec (Option Encoding)) = some word
        ∧ counter.toNat < start + attempts := by
  intro attempts
  induction attempts with
  | zero => intro start counter word _ h; simp [encodingSearch] at h
  | succ attempts ih =>
      intro start counter word hbound h
      rw [encodingSearch, evalWithAnswerFn_bind] at h
      cases hencode : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          rw [hencode] at h
          obtain ⟨hword, hlt⟩ := ih (start + 1) (by omega) h
          exact ⟨hword, by omega⟩
      | some found =>
          rw [hencode] at h
          simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hencode, ?_⟩
          rw [BitVec.toNat_ofNat, counterBits, Nat.mod_eq_of_lt (by omega)]
          omega

/-- What one layer of the specification signs, when it signs: a counter below `C_max`, chain values
the verifier completes to the specification's leaf, and the specification's path. -/
theorem signLayer_spec (key : SecretKey) (index : Index) (lay : Layer) {part : PaddedLayer}
    (h : evalWithAnswerFn f (signLayer key index lay) = some part) :
    part.1.toNat < encodingAttemptLimit
      ∧ evalWithAnswerFn f (otsLeaf key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f (layerMessage key index lay : OracleComp HashSpec Digest))
          part.1 part.2.1 : OracleComp HashSpec (Option Digest))
        = some (honestNode f key.parameter lay (treeIndexAt index lay)
            (key.otsSecret lay (treeIndexAt index lay)) 0 (leafIndexAt index lay).val)
      ∧ ∀ (level : Nat) (hlevel : level < layerHeight lay),
          part.2.2 ⟨level, Nat.lt_of_lt_of_le hlevel (layerHeight_le lay)⟩
            = honestNode f key.parameter lay (treeIndexAt index lay)
                (key.otsSecret lay (treeIndexAt index lay)) level
                (Nat.xor ((leafIndexAt index lay).val / 2 ^ level) 1) := by
  have hlimit : 0 + encodingAttemptLimit ≤ 2 ^ 32 := by rw [encodingAttemptLimit]; norm_num
  rw [signLayer, evalWithAnswerFn_bind, otsSign, evalWithAnswerFn_bind, eval_otsSignFrom] at h
  cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage key index lay : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 : OracleComp HashSpec (Option (Counter × Encoding))) with
  | none =>
      rw [hsearch] at h
      simp at h
  | some result =>
      obtain ⟨counter, word⟩ := result
      obtain ⟨hencode, hlt⟩ := encodingSearch_spec f key.parameter lay _ _ _
        encodingAttemptLimit 0 hlimit hsearch
      rw [hsearch] at h
      simp only [Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        Option.some.injEq] at h
      subst h
      refine ⟨by simpa using hlt, ?_, ?_⟩
      · rw [otsLeaf, evalWithAnswerFn_bind, hencode]
        simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
          eval_recoverChain]
        rw [honestNode_zero_eq_leafHash, honestEndpoints_def]
        simp only [leafHash, Concrete.eval_tweakableHash]
      · intro level hlevel
        rw [eval_treePath]
        simp only [hlevel, if_true]

/-! ## The hypertree

Layer `lay` signs the root of the tree below it, so the value the verifier carries up is the message
the next layer signed, and layer `0`'s root is the public key. -/

/-- The root of the tree layer `lay` carries, on the route `index` selects. -/
def layerRoot (key : SecretKey) (index : Index) (lay : Layer) : Digest :=
  honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay))
    (layerHeight lay) 0

/-- The message entering the verifier's walk with `remaining` layers left to check. -/
def enterMessage (key : SecretKey) (index : Index) : Nat → Digest
  | 0 => layerRoot f key index topLayer
  | r + 1 => if h : r < numLayers then
      evalWithAnswerFn f (layerMessage key index ⟨r, h⟩ : OracleComp HashSpec Digest) else 0

theorem layerRoot_eq_enterMessage (key : SecretKey) (index : Index) (r : Nat) (h : r < numLayers) :
    layerRoot f key index ⟨r, h⟩ = enterMessage f key index r := by
  cases r with
  | zero => rfl
  | succ r =>
      rw [enterMessage, dif_pos (Nat.lt_of_succ_lt h), layerMessage, dif_pos h]
      rfl

/-- The verifier's walk up the hypertree ends at the root of the top tree. -/
theorem eval_verifyLayers (key : SecretKey) (index : Index) (signature : Signature)
    (hlayers : ∀ lay : Layer, ∃ part, evalWithAnswerFn f (signLayer key index lay) = some part
      ∧ signature.layers lay = LayerSignature.ofPadded lay part) :
    ∀ remaining : Nat, remaining ≤ numLayers →
      evalWithAnswerFn f (verifyLayers key.parameter index signature remaining
          (enterMessage f key index remaining) : OracleComp HashSpec (Option Digest))
        = some (layerRoot f key index topLayer) := by
  intro remaining
  induction remaining with
  | zero => intro _; rw [verifyLayers]; rfl
  | succ r ih =>
      intro hrem
      have hlayer : r < numLayers := Nat.lt_of_succ_le hrem
      obtain ⟨part, hpart, hsig⟩ := hlayers ⟨r, hlayer⟩
      obtain ⟨_, hleaf, hpath⟩ := signLayer_spec f key index ⟨r, hlayer⟩ hpart
      have hfold := eval_treeFold_honest f key.parameter ⟨r, hlayer⟩
        (treeIndexAt index ⟨r, hlayer⟩) (key.otsSecret ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩))
        (leafIndexAt index ⟨r, hlayer⟩) (signaturePath signature ⟨r, hlayer⟩)
        (layerHeight ⟨r, hlayer⟩) (fun level hlevel => by
          rw [signaturePath, dif_pos hlevel, hsig]
          exact hpath level hlevel)
      rw [Nat.div_eq_of_lt (leafIndexAt_lt index _)] at hfold
      rw [verifyLayers, dif_pos hlayer, enterMessage, dif_pos hlayer]
      dsimp only
      rw [hsig]
      simp only [evalWithAnswerFn_bind, hleaf, hfold]
      rw [show honestNode f key.parameter ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩)
          (key.otsSecret ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩)) (layerHeight ⟨r, hlayer⟩) 0
          = layerRoot f key index ⟨r, hlayer⟩ from rfl,
        layerRoot_eq_enterMessage f key index r hlayer]
      exact ih (Nat.le_of_succ_le hrem)

attribute [local semireducible] Concrete.verify

/-- **Recovery for the specification.** If the digest is admissible and the specification signs
after it, the verifier accepts, for a key whose root is its top tree's. -/
theorem verify_of_signatureValue (key : SecretKey) (message : Message) (randomness : Randomness)
    {signature : Signature}
    (hroot : key.root = honestNode f key.parameter topLayer rootTree
      (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (hadmissible : Admissible (evalWithAnswerFn f (messageDigest key.parameter key.root message
      randomness : OracleComp HashSpec MessageDigest)))
    (hsig : signatureValue f key randomness
      (digestIndex (evalWithAnswerFn f (messageDigest key.parameter key.root message randomness)))
      (digestLeaves (evalWithAnswerFn f (messageDigest key.parameter key.root message randomness)))
      = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨key.root, key.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  set digest := evalWithAnswerFn f (messageDigest key.parameter key.root message randomness
    : OracleComp HashSpec MessageDigest) with hdigest
  set index := digestIndex digest with hindex
  unfold signatureValue at hsig
  rw [sequenceFin_option_eq] at hsig
  split at hsig
  next hall =>
    simp only [Option.map_some, Option.some.injEq] at hsig
    have hlayers : ∀ lay : Layer, ∃ part, evalWithAnswerFn f (signLayer key index lay) = some part
        ∧ signature.layers lay = LayerSignature.ofPadded lay part := fun lay => by
      rw [← hsig]
      exact ⟨_, (Option.some_get (hall lay)).symm, rfl⟩
    have hcounters : CountersInRange signature := fun lay => by
      rw [← hsig]
      exact (signLayer_spec f key index lay (Option.some_get (hall lay)).symm).1
    have hrandomness : signature.randomness = randomness := by rw [← hsig]
    have hsecrets : signature.ftsSecret
        = fun tree => key.ftsSecret index tree (digestLeaves digest (ftsIndexOf tree)) := by
      rw [← hsig]
    have hpaths : signature.ftsPath
        = evalWithAnswerFn f (ftsOpen key.parameter index (digestLeaves digest) (key.ftsSecret index)) := by
      rw [← hsig]
    have hbottom : enterMessage f key index numLayers
        = evalWithAnswerFn f (ftsKey key.parameter index (key.ftsSecret index)
          : OracleComp HashSpec Digest) := by
      rw [show numLayers = 4 + 1 from rfl, enterMessage, dif_pos (by decide),
        ← layerMessage_bottomLayer_eq]
      rfl
    have htop : layerRoot f key index topLayer = key.root := by
      rw [hroot, layerRoot, show treeIndexAt index topLayer = rootTree from
        Fin.ext (treeIndexAt_topLayer index)]
    rw [Concrete.verify, if_pos hcounters, verifyCore]
    simp only [evalWithAnswerFn_bind, hrandomness, ← hdigest, if_neg (not_not_intro hadmissible),
      hsecrets, hpaths]
    rw [← hindex, eval_ftsRecover_honest, ← hbottom,
      eval_verifyLayers f key index signature hlayers numLayers (Nat.le_refl _), htop]
    simp
  next => simp at hsig

/-! ## The seeded signer

The seeded signer derives its secrets from the seed, two per query; read under `f`, they are a table
of secrets (`unpairedOts`, `unpairedFts`), the paired builders compute what the per-secret builders
compute with that table (`Paired.lean`), and the key they form is a key of the specification. It reads the top layer's path from the cache,
unmasking each node with a freshly derived mask; for the cache key generation wrote, that is the top
tree's node. -/

/-- The specification's key the seeded key stands for under `f`. Its node table is the top tree the
derived secrets span (the signer reads the top path through the cache instead). -/
def tableKey (secretKey : Seeded.SecretKey) : SecretKey where
  parameter := secretKey.parameter
  root := secretKey.root
  otsSecret lay tree leaf chainIdx := unpairedOts f (Seeded.otsSecret secretKey.parameter secretKey.seed lay tree leaf) chainIdx
  ftsSecret index tree leaf := unpairedFts f (Seeded.ftsSecret secretKey.parameter secretKey.seed index tree) leaf
  top level nodeIdx := honestNode f secretKey.parameter topLayer rootTree
    (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret secretKey.parameter secretKey.seed topLayer rootTree leaf) chainIdx) level nodeIdx

@[simp] theorem eval_oracleHash (input : HashInput) :
    evalWithAnswerFn f (oracleHash input : OracleComp HashSpec HashOutput) = f input := by
  simp only [oracleHash, HasQuery.query]
  exact simulateQ_spec_query f input

/-- The cache holds the top tree the seeded key's secrets span, each node masked with its derived mask. -/
def CacheHonest (secretKey : Seeded.SecretKey) (cache : TopCache) : Prop :=
  ∀ (level : Nat) (hlevel : level < maxLayerHeight) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (maxLayerHeight - level)),
    cache.region ⟨level, hlevel⟩ ⟨nodeIdx, hnodeIdx⟩
      = honestNode f secretKey.parameter topLayer rootTree
          (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret secretKey.parameter secretKey.seed topLayer rootTree leaf) chainIdx) level nodeIdx
        ^^^ evalWithAnswerFn f (Seeded.maskSecret secretKey.parameter secretKey.seed level nodeIdx
          : OracleComp HashSpec Digest)

/-- Reading an honest cache unmasks to the top tree: the mask derivation returns the mask the node
was stored under. -/
theorem cachedTopNode_agrees (secretKey : Seeded.SecretKey) (cache : TopCache)
    (hcache : CacheHonest f secretKey cache) :
    TopAgrees f (tableKey f secretKey) (Seeded.cachedTopNode secretKey.parameter secretKey.seed cache) := by
  intro level hlevel nodeIdx hnodeIdx
  have hnode : cache.node level nodeIdx = cache.region ⟨level, hlevel⟩ ⟨nodeIdx, hnodeIdx⟩ := by
    simp only [TopCache.node, dif_pos hlevel, dif_pos hnodeIdx]
  simp only [Seeded.cachedTopNode, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [hnode, hcache level hlevel nodeIdx hnodeIdx, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rfl

/-- The digest the signer accepted. -/
def digestValue (secretKey : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    MessageDigest :=
  evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message randomness
    : OracleComp HashSpec MessageDigest)

theorem signDigestLoop_spec (secretKey : Seeded.SecretKey) (message : Message) :
    ∀ (attempts trial : Nat) {randomness : Randomness} {index : Index}
      {leaves : IndexGroup → FtsLeaf},
      evalWithAnswerFn f (Seeded.signDigestLoop secretKey message attempts trial
          : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf))))
          = some (randomness, index, leaves) →
      Admissible (digestValue f secretKey message randomness)
        ∧ index = digestIndex (digestValue f secretKey message randomness)
        ∧ leaves = digestLeaves (digestValue f secretKey message randomness) := by
  intro attempts
  induction attempts with
  | zero => intro trial randomness index leaves h; simp [Seeded.signDigestLoop] at h
  | succ attempts ih =>
      intro trial randomness index leaves h
      simp only [Seeded.signDigestLoop, Seeded.signAttempt, evalWithAnswerFn_bind] at h
      by_cases hadmissible : Admissible (digestValue f secretKey
          (message := message) (randomness := truncateHash (f (randomizerHashInput
            secretKey.parameter secretKey.seed message (BitVec.ofNat 32 trial)))))
      · rw [digestValue] at hadmissible
        simp only [deriveRandomizer, evalWithAnswerFn_bind, eval_oracleHash,
          evalWithAnswerFn_pure, if_pos hadmissible, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨hrand, hindex, hleaves⟩ := h
        subst hrand
        exact ⟨hadmissible, hindex.symm, hleaves.symm⟩
      · rw [digestValue] at hadmissible
        simp only [deriveRandomizer, evalWithAnswerFn_bind, eval_oracleHash,
          evalWithAnswerFn_pure, if_neg hadmissible] at h
        exact ih (trial + 1) h

-- Below, only the shape of `sign` matters; sealing the loop keeps the unfolding shallow.
attribute [local irreducible] Seeded.signDigestLoop Concrete.signFrom Concrete.signFromPaired

/-- What a successful signing after the MAC check produced: an admissible digest, and the
specification's signature after it for the key the seed derives. -/
theorem signChecked_spec (secretKey : Seeded.SecretKey) (cache : TopCache)
    (hcache : CacheHonest f secretKey cache) (message : Message) {signature : Signature}
    (h : evalWithAnswerFn f (Seeded.signChecked secretKey cache message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    Admissible (digestValue f secretKey message signature.randomness)
      ∧ signatureValue f (tableKey f secretKey) signature.randomness
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestLeaves (digestValue f secretKey message signature.randomness)) = some signature := by
  rw [Seeded.signChecked, evalWithAnswerFn_bind] at h
  cases hloop : evalWithAnswerFn f (Seeded.signDigestLoop secretKey message digestAttemptLimit 0
      : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf)))) with
  | none => rw [hloop] at h; simp at h
  | some result =>
      obtain ⟨randomness, index, leaves⟩ := result
      rw [hloop] at h
      obtain ⟨hadmissible, hindex, hleaves⟩ :=
        signDigestLoop_spec f secretKey message digestAttemptLimit 0 hloop
      change evalWithAnswerFn f (signFromPaired secretKey.parameter index
        (Seeded.ftsSecret secretKey.parameter secretKey.seed index)
        (Seeded.otsSecret secretKey.parameter secretKey.seed)
        (Seeded.cachedTopNode secretKey.parameter secretKey.seed cache) randomness leaves
          : OracleComp HashSpec (Option Signature)) = some signature at h
      rw [eval_signFromPaired] at h
      have hsf := eval_signFrom f (tableKey f secretKey) index
        (fun tree leaf => pure (unpairedFts f
          (Seeded.ftsSecret secretKey.parameter secretKey.seed index tree) leaf))
        (fun lay tree leaf chainIdx => pure (unpairedOts f
          (Seeded.otsSecret secretKey.parameter secretKey.seed lay tree leaf) chainIdx))
        (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        (Seeded.cachedTopNode secretKey.parameter secretKey.seed cache)
        (cachedTopNode_agrees f secretKey cache hcache) randomness leaves
      rw [show (tableKey f secretKey).parameter = secretKey.parameter from rfl] at hsf
      rw [hsf] at h
      have hrand : signature.randomness = randomness := by
        unfold signatureValue at h
        cases hparts : sequenceFin (m := Option) fun lay =>
            evalWithAnswerFn f (signLayer (tableKey f secretKey) index lay) with
        | none => rw [hparts] at h; simp at h
        | some parts =>
            rw [hparts] at h
            simp only [Option.map_some, Option.some.injEq] at h
            rw [← h]
      rw [hrand]
      subst hindex hleaves
      exact ⟨hadmissible, h⟩

/-- A successful signing passed the MAC check and then signed. -/
theorem signChecked_of_sign (secretKey : Seeded.SecretKey) (cache : TopCache) (message : Message)
    {signature : Signature}
    (h : evalWithAnswerFn f (Seeded.sign secretKey cache message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Seeded.signChecked secretKey cache message
        : OracleComp HashSpec (Option Signature)) = some signature := by
  rw [Seeded.sign, evalWithAnswerFn_bind, eval_oracleHash] at h
  split_ifs at h with htag
  · exact h
  · simp at h

/-- **Recovery.** A signature the signer produced with an honest cache is one the verifier accepts:
`doc/sphincs` §sec:ver. -/
theorem verify_of_sign (secretKey : Seeded.SecretKey) (cache : TopCache) (message : Message)
    {signature : Signature}
    (hroot : secretKey.root = honestNode f secretKey.parameter topLayer rootTree
      (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret secretKey.parameter secretKey.seed topLayer rootTree leaf) chainIdx) (layerHeight topLayer) 0)
    (hcache : CacheHonest f secretKey cache)
    (h : evalWithAnswerFn f (Seeded.sign secretKey cache message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨secretKey.root, secretKey.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  obtain ⟨hadmissible, hsig⟩ :=
    signChecked_spec f secretKey cache hcache message (signChecked_of_sign f secretKey cache message h)
  exact verify_of_signatureValue f (tableKey f secretKey) message signature.randomness hroot
    hadmissible hsig

/-! ## Key generation -/

/-- The node table key generation builds from the seed under `f`. -/
def keygenTableValue (seed : MasterSeed) : Nat → Nat → Digest :=
  (evalWithAnswerFn f (buildLayerTablePaired 0 topLayer rootTree (Seeded.otsSecret 0 seed topLayer rootTree)
    ⟨0, Nat.two_pow_pos _⟩ zeroEncoding : OracleComp HashSpec _)).2

/-- `keygenTableValue`'s definition, proved at the level of the function: the generated equation
lemma would make the kernel unfold `Prod.snd` first and so run the whole tree build. -/
theorem keygenTableValue_def (seed : MasterSeed) :
    keygenTableValue f seed = (evalWithAnswerFn f (buildLayerTablePaired 0 topLayer rootTree
      (Seeded.otsSecret 0 seed topLayer rootTree) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
        : OracleComp HashSpec _)).2 :=
  congrFun (congrFun (show keygenTableValue = fun f seed => (evalWithAnswerFn f (buildLayerTablePaired 0
    topLayer rootTree (Seeded.otsSecret 0 seed topLayer rootTree) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
      : OracleComp HashSpec _)).2 from rfl) f) seed

/-- The masked region key generation writes under `f`. -/
def keygenRegionValue (seed : MasterSeed) : TopRegion :=
  evalWithAnswerFn f (Seeded.maskRegion 0 seed (keygenTableValue f seed) : OracleComp HashSpec TopRegion)

theorem keygenRegionValue_def (seed : MasterSeed) :
    keygenRegionValue f seed = evalWithAnswerFn f
      (Seeded.maskRegion 0 seed (keygenTableValue f seed) : OracleComp HashSpec TopRegion) := rfl

-- Both values stand for a whole tree build under `f`; unfolding them runs it.
attribute [local irreducible] keygenTableValue keygenRegionValue

theorem eval_keygenFromSeed (seed : MasterSeed) :
    evalWithAnswerFn f (Seeded.keygenFromSeed seed)
      = (⟨keygenTableValue f seed (layerHeight topLayer) 0, 0⟩,
          ⟨f (macHashInput 0 seed (keygenRegionValue f seed)), keygenRegionValue f seed⟩,
          ⟨seed, 0, keygenTableValue f seed (layerHeight topLayer) 0⟩) := by
  rw [Seeded.keygenFromSeed, evalWithAnswerFn_bind, keygenRegionValue_def, keygenTableValue_def]
  split
  next leaves table h =>
    rw [h]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_oracleHash]

/-- A built table carries the specification's nodes, for every tree and every secret derivation. -/
theorem eval_buildLayerTable_node (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex) (digits : Encoding)
    (level : Nat) (hlevel : level ≤ layerHeight lay) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (layerHeight lay - level)) :
    (evalWithAnswerFn f (buildLayerTable parameter lay tree secret leaf digits)).2 level nodeIdx
      = honestNode f parameter lay tree
          (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)) level nodeIdx := by
  have htable := eval_buildLayerTree_table f parameter lay tree secret leaf digits
    level hlevel nodeIdx hnodeIdx
  unfold buildLayerTable
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact htable

/-- A table built with pair getters carries the specification's nodes for the secrets they hand out. -/
theorem eval_buildLayerTablePaired_node (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)) (leaf : LeafIndex)
    (digits : Encoding) (level : Nat) (hlevel : level ≤ layerHeight lay) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (layerHeight lay - level)) :
    (evalWithAnswerFn f (buildLayerTablePaired parameter lay tree secret leaf digits)).2 level nodeIdx
      = honestNode f parameter lay tree
          (fun leaf chainIdx => unpairedOts f (secret leaf) chainIdx) level nodeIdx := by
  rw [eval_buildLayerTablePaired]
  exact eval_buildLayerTable_node f parameter lay tree _ leaf digits level hlevel nodeIdx hnodeIdx

/-- Key generation's table is the specification's top tree for the derived secrets. -/
theorem keygenTableValue_eq (seed : MasterSeed) (level : Nat) (hlevel : level ≤ layerHeight topLayer)
    (nodeIdx : Nat) (hnodeIdx : nodeIdx < 2 ^ (layerHeight topLayer - level)) :
    keygenTableValue f seed level nodeIdx = honestNode f 0 topLayer rootTree
      (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret 0 seed topLayer rootTree leaf) chainIdx) level nodeIdx := by
  rw [keygenTableValue_def]
  exact eval_buildLayerTablePaired_node f 0 topLayer rootTree _ _ _ level hlevel nodeIdx hnodeIdx

theorem eval_maskRegion (parameter : PublicParameter) (seed : MasterSeed) (table : Nat → Nat → Digest)
    (level : Fin maxLayerHeight) (nodeIdx : Fin (2 ^ (maxLayerHeight - level.val))) :
    evalWithAnswerFn f (Seeded.maskRegion parameter seed table : OracleComp HashSpec TopRegion) level nodeIdx
      = table level.val nodeIdx.val ^^^ evalWithAnswerFn f
          (Seeded.maskSecret parameter seed level.val nodeIdx.val : OracleComp HashSpec Digest) := by
  simp only [Seeded.maskRegion, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    evalWithAnswerFn_pure, dif_pos nodeIdx.isLt]

/-- Masking a table of the top tree gives an honest cache. -/
theorem cacheHonest_of_table (seed : MasterSeed) (root : Digest) (tag : HashOutput)
    (table : Nat → Nat → Digest)
    (htable : ∀ level, level ≤ layerHeight topLayer → ∀ nodeIdx, nodeIdx < 2 ^ (layerHeight topLayer - level) →
      table level nodeIdx = honestNode f 0 topLayer rootTree
        (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret 0 seed topLayer rootTree leaf) chainIdx) level nodeIdx) :
    CacheHonest f ⟨seed, 0, root⟩
      ⟨tag, evalWithAnswerFn f (Seeded.maskRegion 0 seed table : OracleComp HashSpec TopRegion)⟩ := by
  intro level hlevel nodeIdx hnodeIdx
  have hheight : layerHeight topLayer = maxLayerHeight := rfl
  have hmask := eval_maskRegion f 0 seed table ⟨level, hlevel⟩ ⟨nodeIdx, hnodeIdx⟩
  dsimp only at hmask
  rw [htable level (by rw [hheight]; omega) nodeIdx (by rw [hheight]; exact hnodeIdx)] at hmask
  -- reduce the key's projections first: comparing them unreduced unfolds the evaluations
  dsimp only
  exact hmask

/-- The cache key generation writes is honest for the key it returns. -/
theorem keygen_cacheHonest (seed : MasterSeed) (tag : HashOutput) :
    CacheHonest f ⟨seed, 0, keygenTableValue f seed (layerHeight topLayer) 0⟩
      ⟨tag, keygenRegionValue f seed⟩ := by
  rw [keygenRegionValue_def]
  exact cacheHonest_of_table f seed _ tag _ (keygenTableValue_eq f seed)

/-- The root is the specification's root of the top tree for the derived secrets. -/
theorem keygenRootValue_eq (seed : MasterSeed) :
    keygenTableValue f seed (layerHeight topLayer) 0 = honestNode f 0 topLayer rootTree
      (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret 0 seed topLayer rootTree leaf) chainIdx) (layerHeight topLayer) 0 :=
  keygenTableValue_eq f seed _ le_rfl 0 (by simp)

/-- Recovery for a key of key generation's shape, stated with its fields as variables. -/
theorem verify_of_sign_seeded (seed : MasterSeed) (root : Digest) (cache : TopCache) (message : Message)
    {signature : Signature}
    (hroot : root = honestNode f 0 topLayer rootTree
      (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret 0 seed topLayer rootTree leaf) chainIdx) (layerHeight topLayer) 0)
    (hcache : CacheHonest f ⟨seed, 0, root⟩ cache)
    (h : evalWithAnswerFn f (Seeded.sign ⟨seed, 0, root⟩ cache message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨root, 0⟩ message signature : OracleComp HashSpec Bool) = true :=
  verify_of_sign f ⟨seed, 0, root⟩ cache message hroot hcache h

/-- **Correctness for key generation.** What the signer produces with the key and cache key
generation returned, the verifier accepts. -/
theorem verify_of_keygen_sign (seed : MasterSeed) (message : Message) {publicKey : PublicKey}
    {cache : TopCache} {secretKey : Seeded.SecretKey} {signature : Signature}
    (hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (publicKey, cache, secretKey))
    (hsign : evalWithAnswerFn f (Seeded.sign secretKey cache message
      : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)
      = true := by
  rw [eval_keygenFromSeed] at hkeys
  simp only [Prod.mk.injEq] at hkeys
  obtain ⟨rfl, rfl, rfl⟩ := hkeys
  exact verify_of_sign_seeded f seed _ _ message (keygenRootValue_eq f seed)
    (keygen_cacheHonest f seed _) hsign

end SigGolfCandidate.Base4Candidate.Ideal.Completeness

end AlternateRecoveryPort14

/-! Simulation rules for the alternate verifier image. These rules expose every
remaining byte, HASH-argument, framing, and cycle obligation to subsequent proofs. -/
namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

abbrev image := Reference.VerifyImage.image

def queryFormat (x : List Byte) := AddressFormat.queryPerm (SigGolfCandidate.Ref.pad64 x)

abbrev Obs := Bool × Nat

def obs (e : Execution) : Obs := (decide (e.exit = .success), e.hashCalls)

def Good (s : MachineState) (N C : Nat) (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C

@[simp] theorem obs_charge (e : Execution) (c b : Nat) :
    obs (e.charge c 0 b) = obs e := by
  cases e; simp [obs, Execution.charge]

theorem obs_charge1 (e : Execution) (c b : Nat) :
    obs (e.charge c 1 b) = ((obs e).1, 1 + (obs e).2) := by
  cases e; rfl

theorem Good.mono {s : MachineState} {N C N' C' : Nat} {X : OracleComp HashSpec Obs}
    (h : Good s N C X) (hN : N ≤ N') (hC : C ≤ C') : Good s N' C' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  exact ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2; omega⟩⟩

theorem Good.congr {s : MachineState} {N C : Nat} {X Y : OracleComp HashSpec Obs}
    (h : Good s N C X) (hXY : X = Y) : Good s N C Y := hXY ▸ h

theorem Good.steps {s t : MachineState} {k c N C : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : Good t N C X) : Good s (N + k) (C + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨(h2 hash).1, by have := (h2 hash).2; omega⟩

theorem Good.steps' {s t : MachineState} {k c N C N' C' : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : Good t N C X) (hN : N + k ≤ N') (hC : C + c ≤ C') :
    Good s N' C' X := (h.steps hst).mono hN hC

/-! ## The counting continuation -/

def cc {α : Type} (oa : OracleComp HashSpec α) (K : α → OracleComp HashSpec Obs) :
    OracleComp HashSpec Obs :=
  countCalls oa >>= fun p => (fun q => (q.1, p.2 + q.2)) <$> K p.1

@[simp] theorem cc_pure {α : Type} (a : α) (K : α → OracleComp HashSpec Obs) :
    cc (pure a) K = K a := by
  simp only [cc, countCalls_pure, pure_bind, Nat.zero_add]
  exact id_map' _

theorem cc_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (K : β → OracleComp HashSpec Obs) : cc (oa >>= f) K = cc oa (fun a => cc (f a) K) := by
  simp only [cc, countCalls_bind, bind_assoc, map_bind, Functor.map_map, bind_map_left]
  congr 1; funext p; congr 1; funext r
  simp only [Nat.add_assoc]

theorem cc_hash16 (x : List Byte) (K : Val → OracleComp HashSpec Obs) :
    cc (Reference.h16 x) K = (do
      let a ← (HashSpec.query (queryFormat x) : OracleComp HashSpec _)
      (fun q => (q.1, 1 + q.2)) <$> K (answerBytes 16 a)) := by
  simp only [Reference.h16, cc_bind]
  simp only [cc, Reference.hash, countCalls_query, bind_map_left, countCalls_pure, pure_bind,
    Functor.map_map, Nat.zero_add]

/-! ## HASH and HALT -/

theorem Good.hash {s : MachineState} {N C : Nat} {x : List Byte}
    {K : Val → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = queryFormat x)
    (h : ∀ a, Good (writeHash s a) N C (K (answerBytes 16 a))) :
    Good s (N + 1) (C + 8 * (queryFormat x).blocks) (cc (Reference.h16 x) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_hash16, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2⟩ := (h (hash (queryFormat x)) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨h1, by omega⟩

theorem cc_H (x : List Byte) (K : BitVec 256 → OracleComp HashSpec Obs) :
    cc (Reference.hash x) K = (do
      let a ← (HashSpec.query (queryFormat x) : OracleComp HashSpec _)
      (fun q => (q.1, 1 + q.2)) <$> K a) := by
  simp only [cc, Reference.hash, countCalls_query, bind_map_left]

theorem Good.hashH {s : MachineState} {N C : Nat} {x : List Byte}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = queryFormat x)
    (h : ∀ a, Good (writeHash s a) N C (K a)) :
    Good s (N + 1) (C + 8 * (queryFormat x).blocks) (cc (Reference.hash x) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_H, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2⟩ := (h (hash (queryFormat x)) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    exact ⟨h1, by omega⟩

theorem Good.halt {s : MachineState} (hf : fetch image s = some (.base .ECALL))
    (ht0 : s.getReg .x5 = 1) : Good s 1 1 (pure (decide (s.getReg .x10 = 0), 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf ht0, map_pure]
    by_cases hx : s.getReg .x10 = 0
    · simp only [obs, hx, if_true]
    · simp only [obs, hx, if_false]; rfl
  · rw [hF', evalWith_halt hash (F - 1) hf ht0]
    refine ⟨?_, le_refl _⟩
    by_cases hx : s.getReg .x10 = 0
    · simp only [hx, if_true]; decide
    · simp only [hx, if_false]; decide

end SigGolfCandidate.Base4Candidate.VerifyProof
namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def GoodQ (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat) (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F image s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F image s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F image s)).exit = .success →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F image s)).cycles ≤ A)

theorem Good.toQ {s : MachineState} {N C : Nat} {X : OracleComp HashSpec Obs} (h : Good s N C X) :
    GoodQ s N C True C X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  exact ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2, fun _ => ⟨trivial, (h2 hash).2⟩⟩⟩

theorem GoodQ.toGood {s : MachineState} {N C : Nat} {Q : Prop} {A : Nat} {X : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) : Good s N C X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  exact ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2.1⟩⟩

theorem GoodQ.mono {s : MachineState} {N C A N' C' A' : Nat} {Q Q' : Prop} {X : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hQ : Q → Q' ∧ A ≤ A') :
    GoodQ s N' C' Q' A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
  exact ⟨(hQ hq).1, by have := (hQ hq).2; omega⟩

theorem GoodQ.congr {s : MachineState} {N C A : Nat} {Q : Prop} {X Y : OracleComp HashSpec Obs}
    (h : GoodQ s N C Q A X) (hXY : X = Y) : GoodQ s N C Q A Y := hXY ▸ h

theorem GoodQ.steps {s t : MachineState} {k c N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : GoodQ t N C Q A X) : GoodQ s (N + k) (C + c) Q (A + c) X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h (F - k) (by omega)
  have hF' : F = (F - k) + k := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hst.execute_le (by omega : k ≤ F), Functor.map_map]
    simp only [obs_charge]
    exact h1
  · rw [hF', hst.evalWith hash (F - k)]
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs
    exact ⟨hq, by omega⟩

theorem GoodQ.steps' {s t : MachineState} {k c N C A N' C' A' : Nat} {Q Q' : Prop}
    {X : OracleComp HashSpec Obs} (hst : Steps image s k c t) (h : GoodQ t N C Q A X)
    (hN : N + k ≤ N') (hC : C + c ≤ C') (hQ : Q → Q' ∧ A + c ≤ A') : GoodQ s N' C' Q' A' X :=
  (h.steps hst).mono hN hC hQ

theorem GoodQ.hash {s : MachineState} {N C A : Nat} {Q : Prop} {x : List Byte}
    {K : Val → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = queryFormat x)
    (h : ∀ a, GoodQ (writeHash s a) N C Q A (K (answerBytes 16 a))) :
    GoodQ s (N + 1) (C + 8 * (queryFormat x).blocks) Q (A + 8 * (queryFormat x).blocks) (cc (Reference.h16 x) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_hash16, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2, h3⟩ := (h (hash (queryFormat x)) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨h1, by omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := h3 hs
    exact ⟨hq, by omega⟩

theorem GoodQ.hashH {s : MachineState} {N C A : Nat} {Q : Prop} {x : List Byte}
    {K : BitVec 256 → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = queryFormat x)
    (h : ∀ a, GoodQ (writeHash s a) N C Q A (K a)) :
    GoodQ s (N + 1) (C + 8 * (queryFormat x).blocks) Q (A + 8 * (queryFormat x).blocks) (cc (Reference.hash x) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf ht0 hv, cc_H, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf ht0 hv, hin]
    obtain ⟨h1, h2, h3⟩ := (h (hash (queryFormat x)) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨h1, by omega, fun hs => ?_⟩
    obtain ⟨hq, ha⟩ := h3 hs
    exact ⟨hq, by omega⟩

/-- HALT(1): a rejecting run (any acceptance condition). -/
theorem GoodQ.reject {s : MachineState} {Q : Prop} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : GoodQ s 1 1 Q A (pure (false, 0)) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_halt (F - 1) hf h5, map_pure]
    simp only [obs, h10]
    rfl
  · rw [hF', evalWith_halt hash (F - 1) hf h5]
    simp only [h10]
    refine ⟨by decide, le_refl _, fun h => ?_⟩
    exact absurd h (by decide)

end SigGolfCandidate.Base4Candidate.VerifyProof


namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Ref

def hashArgsB (a n d : Nat) : Bool :=
  decide (a % 8 = 0) && decide (0 < n ∧ n % 64 = 0) && decide (a + n ≤ MEMORY_BYTES) &&
    decide (d + 8 ≤ MEMORY_BYTES ∧ d % 8 = 0) && decide (d + 32 ≤ MEMORY_BYTES)

theorem hashArgs_ofNat (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) (h : hashArgsB a n d = true) :
    hashArgumentsValid t = true := by
  simp only [hashArgsB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Bool.and_eq_true,
    decide_eq_true_eq]
  omega


def blockAddress (lay chain : Nat) : Nat := 5376+3968*lay+64*chain

def FreshWord (lay chain otherLay otherChain word : Nat) : Prop :=
  otherLay < 4 ∧ otherChain < 62 ∧ 2 ≤ word ∧ word < 8 ∧
    (otherLay < lay ∨ (otherLay = lay ∧ chain ≤ otherChain))

def Fresh (witness : List Byte) (lay chain : Nat) (state : MachineState) : Prop :=
  ∀ a b k, FreshWord lay chain a b k →
    state.getMem (BitVec.ofNat 64 (blockAddress a b+8*k)) =
      BitVec.ofNat 64 (leNat (slice witness (Reference.witnessChainOffset a b+8*k) 8))

theorem fresh_next {lay chain a b k : Nat} (h : FreshWord lay (chain+1) a b k) :
    FreshWord lay chain a b k := by
  unfold FreshWord at *
  omega

theorem fresh_layer {lay a b k : Nat} (hl : 1 ≤ lay)
    (h : FreshWord (lay-1) 0 a b k) : FreshWord lay 62 a b k := by
  unfold FreshWord at *
  omega

/-- A full HASH output may spill into the next header, but never into a future
chain's padding or value. Counters live in a separate witness region. -/
theorem fresh_ne_written {lay chain a b k : Nat} (hw : FreshWord lay (chain+1) a b k)
    (hi : chain < 62) (d : Nat)
    (hd : d = 0 ∨ d = 8 ∨ d = 48 ∨ d = 56 ∨ d = 64 ∨ d = 72) :
    blockAddress a b+8*k ≠ blockAddress lay chain+d := by
  unfold FreshWord at hw
  unfold blockAddress
  rcases hw with ⟨ha,hb,hk,hk',horder⟩
  rcases horder with horder | ⟨rfl,horder⟩ <;> omega

theorem fresh_own {lay chain k : Nat} (hl : lay < 4) (hi : chain < 62)
    (hk : 2 ≤ k) (hk' : k < 8) : FreshWord lay chain lay chain k :=
  ⟨hl,hi,hk,hk',Or.inr ⟨rfl,le_rfl⟩⟩

theorem block_aligned (lay chain : Nat) : blockAddress lay chain % 64 = 0 := by
  unfold blockAddress
  omega

theorem block_interval (lay chain : Nat) (hl : lay < 4) (hi : chain < 62) :
    5376 ≤ blockAddress lay chain ∧ blockAddress lay chain+96 ≤ 21280 := by
  unfold blockAddress
  omega

theorem block_access (lay chain k width : Nat) (hl : lay < 4) (hi : chain < 62)
    (hk : k < 128) (hw : width = 1 ∨ width = 8)
    (ha : (blockAddress lay chain+k) % width = 0) :
    accessValid (BitVec.ofNat 64 (blockAddress lay chain+k)) width = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold blockAddress; omega)]
  refine ⟨?_,ha⟩
  simp only [MEMORY_BYTES]
  unfold blockAddress
  omega

/-- HASH addresses used by a chain and its final leaf slot satisfy the pinned
alignment and memory-end checks, including the full 32-byte output. -/
theorem chain_hash_arguments (lay chain : Nat) (hl : lay < 4) (hi : chain < 62) :
    hashArgsB (blockAddress lay chain) 64 (blockAddress lay chain+48) = true ∧
    hashArgsB (blockAddress lay chain) 64 (Reference.ChainCode.leafSlot chain) = true := by
  simp only [hashArgsB, MEMORY_BYTES, blockAddress, Reference.ChainCode.leafSlot]
  simp
  omega

end SigGolfCandidate.Base4Candidate.VerifyProof

namespace SigGolfCandidate.Base4Candidate.SwarProof
open SigGolfCandidate.Verify (land_split)
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem split2 (n M : Nat) : n &&& (16*M+3) = 16*((n/16) &&& M)+n%4 :=
  land_split n M 2 4 (by decide)
theorem split4 (n M : Nat) : n &&& (256*M+15) = 256*((n/256) &&& M)+n%16 :=
  land_split n M 4 8 (by decide)
theorem and3 (n : Nat) : n &&& 3 = n%4 := Nat.and_two_pow_sub_one_eq_mod n 2
theorem and15 (n : Nat) : n &&& 15 = n%16 := Nat.and_two_pow_sub_one_eq_mod n 4

theorem mask2 (n : Nat) : n &&& 3689348814741910323 =
    16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 % 4) + n / 16 / 16 % 4) + n / 16 % 4) + n % 4 := by
  rw [show (3689348814741910323 : Nat) = 16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3 by norm_num]
  simp only [split2, and3]

theorem mask4 (n : Nat) : n &&& 1085102592571150095 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 % 16) + n / 256 / 256 % 16) + n / 256 % 16) + n % 16 := by
  rw [show (1085102592571150095 : Nat) = 256 * (256 * (256 * (256 * (256 * (256 * (256 * (15) + 15) + 15) + 15) + 15) + 15) + 15) + 15 by norm_num]
  simp only [split4, and15]

theorem mask4_nibbles (n : Nat) : n &&& 1085102592571150095 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 % 16) + n % 16 := by
  rw [mask4]
  simp only [Nat.div_div_eq_div_mul]

theorem hdiv16 (c R : Nat) (h : c < 16) : (c+16*R)/16 = R := by omega
theorem hmod16 (c R : Nat) (h : c < 16) : (c+16*R)%16 = c := by omega

theorem byteChecksum (P0 P1 P2 P3 P4 P5 P6 P7 : Nat) (h0 : P0 ≤ 24) (h1 : P1 ≤ 24) (h2 : P2 ≤ 24) (h3 : P3 ≤ 24) (h4 : P4 ≤ 24) (h5 : P5 ≤ 24) (h6 : P6 ≤ 24) (h7 : P7 ≤ 24) :
    ((P0) + 256 * ((P1) + 256 * ((P2) + 256 * ((P3) + 256 * ((P4) + 256 * ((P5) + 256 * ((P6) + 256 * (P7)))))))) % 255 = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 := by
  omega

def tail (X : Nat) : Nat := (((X &&& 1085102592571150095) + (X/16 &&& 1085102592571150095)) % 18446744073709551616) % 255

theorem lanes (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 : Nat) (h0 : L0 ≤ 12) (h1 : L1 ≤ 12) (h2 : L2 ≤ 12) (h3 : L3 ≤ 12) (h4 : L4 ≤ 12) (h5 : L5 ≤ 12) (h6 : L6 ≤ 12) (h7 : L7 ≤ 12) (h8 : L8 ≤ 12) (h9 : L9 ≤ 12) (h10 : L10 ≤ 12) (h11 : L11 ≤ 12) (h12 : L12 ≤ 12) (h13 : L13 ≤ 12) (h14 : L14 ≤ 12) (h15 : L15 ≤ 12)
    (X : Nat) (hX : X = (L0) + 16 * ((L1) + 16 * ((L2) + 16 * ((L3) + 16 * ((L4) + 16 * ((L5) + 16 * ((L6) + 16 * ((L7) + 16 * ((L8) + 16 * ((L9) + 16 * ((L10) + 16 * ((L11) + 16 * ((L12) + 16 * ((L13) + 16 * ((L14) + 16 * (L15)))))))))))))))) : tail X = L0 + L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10 + L11 + L12 + L13 + L14 + L15 := by
  have hM : (X &&& 1085102592571150095) + (X/16 &&& 1085102592571150095) = (L0+L1) + 256 * ((L2+L3) + 256 * ((L4+L5) + 256 * ((L6+L7) + 256 * ((L8+L9) + 256 * ((L10+L11) + 256 * ((L12+L13) + 256 * (L14+L15))))))) := by
    rw [hX, mask4_nibbles, mask4_nibbles]
    simp (disch := omega) only [hdiv16, hmod16, Nat.mod_eq_of_lt]
    omega
  unfold tail
  rw [hM, Nat.mod_eq_of_lt (by omega)]
  have h := byteChecksum (L0+L1) (L2+L3) (L4+L5) (L6+L7) (L8+L9) (L10+L11) (L12+L13) (L14+L15) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

def first (a b : Nat) : Nat :=
  (((a &&& 3689348814741910323)+(a/4 &&& 3689348814741910323)) % 18446744073709551616 +
    ((b &&& 3689348814741910323)+(b/4 &&& 3689348814741910323)) % 18446744073709551616) % 18446744073709551616

def digitSum (a : Nat) : Nat := ((List.range 32).map fun i => a/4^i%4).sum

theorem digitSum_expanded (a : Nat) : digitSum a =
    a % 4 + a / 4 % 4 + a / 16 % 4 + a / 64 % 4 + a / 256 % 4 + a / 1024 % 4 + a / 4096 % 4 + a / 16384 % 4 + a / 65536 % 4 + a / 262144 % 4 + a / 1048576 % 4 + a / 4194304 % 4 + a / 16777216 % 4 + a / 67108864 % 4 + a / 268435456 % 4 + a / 1073741824 % 4 + a / 4294967296 % 4 + a / 17179869184 % 4 + a / 68719476736 % 4 + a / 274877906944 % 4 + a / 1099511627776 % 4 + a / 4398046511104 % 4 + a / 17592186044416 % 4 + a / 70368744177664 % 4 + a / 281474976710656 % 4 + a / 1125899906842624 % 4 + a / 4503599627370496 % 4 + a / 18014398509481984 % 4 + a / 72057594037927936 % 4 + a / 288230376151711744 % 4 + a / 1152921504606846976 % 4 + a / 4611686018427387904 % 4 := by
  simp only [digitSum, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num
  omega

/-- All 64 digits are summed exactly. The decoder separately zeros the upper
four bits, so the final two digits contribute zero for valid encodings. -/
theorem sum_exact (a b : Nat) : tail (first a b) = digitSum a+digitSum b := by
  generalize hX : first a b = X
  unfold first at hX
  rw [digitSum_expanded, digitSum_expanded]
  simp only [mask2, Nat.div_div_eq_div_mul] at hX
  norm_num at hX
  have ha0 : a % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a % 4 = a0 at *
  have ha1 : a / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4 % 4 = a1 at *
  have ha2 : a / 16 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16 % 4 = a2 at *
  have ha3 : a / 64 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 64 % 4 = a3 at *
  have ha4 : a / 256 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 256 % 4 = a4 at *
  have ha5 : a / 1024 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1024 % 4 = a5 at *
  have ha6 : a / 4096 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4096 % 4 = a6 at *
  have ha7 : a / 16384 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16384 % 4 = a7 at *
  have ha8 : a / 65536 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 65536 % 4 = a8 at *
  have ha9 : a / 262144 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 262144 % 4 = a9 at *
  have ha10 : a / 1048576 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1048576 % 4 = a10 at *
  have ha11 : a / 4194304 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4194304 % 4 = a11 at *
  have ha12 : a / 16777216 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16777216 % 4 = a12 at *
  have ha13 : a / 67108864 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 67108864 % 4 = a13 at *
  have ha14 : a / 268435456 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 268435456 % 4 = a14 at *
  have ha15 : a / 1073741824 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1073741824 % 4 = a15 at *
  have ha16 : a / 4294967296 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4294967296 % 4 = a16 at *
  have ha17 : a / 17179869184 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 17179869184 % 4 = a17 at *
  have ha18 : a / 68719476736 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 68719476736 % 4 = a18 at *
  have ha19 : a / 274877906944 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 274877906944 % 4 = a19 at *
  have ha20 : a / 1099511627776 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1099511627776 % 4 = a20 at *
  have ha21 : a / 4398046511104 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4398046511104 % 4 = a21 at *
  have ha22 : a / 17592186044416 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 17592186044416 % 4 = a22 at *
  have ha23 : a / 70368744177664 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 70368744177664 % 4 = a23 at *
  have ha24 : a / 281474976710656 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 281474976710656 % 4 = a24 at *
  have ha25 : a / 1125899906842624 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1125899906842624 % 4 = a25 at *
  have ha26 : a / 4503599627370496 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4503599627370496 % 4 = a26 at *
  have ha27 : a / 18014398509481984 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 18014398509481984 % 4 = a27 at *
  have ha28 : a / 72057594037927936 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 72057594037927936 % 4 = a28 at *
  have ha29 : a / 288230376151711744 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 288230376151711744 % 4 = a29 at *
  have ha30 : a / 1152921504606846976 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1152921504606846976 % 4 = a30 at *
  have ha31 : a / 4611686018427387904 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4611686018427387904 % 4 = a31 at *
  have hb0 : b % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b % 4 = b0 at *
  have hb1 : b / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4 % 4 = b1 at *
  have hb2 : b / 16 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 16 % 4 = b2 at *
  have hb3 : b / 64 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 64 % 4 = b3 at *
  have hb4 : b / 256 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 256 % 4 = b4 at *
  have hb5 : b / 1024 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1024 % 4 = b5 at *
  have hb6 : b / 4096 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4096 % 4 = b6 at *
  have hb7 : b / 16384 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 16384 % 4 = b7 at *
  have hb8 : b / 65536 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 65536 % 4 = b8 at *
  have hb9 : b / 262144 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 262144 % 4 = b9 at *
  have hb10 : b / 1048576 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1048576 % 4 = b10 at *
  have hb11 : b / 4194304 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4194304 % 4 = b11 at *
  have hb12 : b / 16777216 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 16777216 % 4 = b12 at *
  have hb13 : b / 67108864 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 67108864 % 4 = b13 at *
  have hb14 : b / 268435456 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 268435456 % 4 = b14 at *
  have hb15 : b / 1073741824 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1073741824 % 4 = b15 at *
  have hb16 : b / 4294967296 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4294967296 % 4 = b16 at *
  have hb17 : b / 17179869184 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 17179869184 % 4 = b17 at *
  have hb18 : b / 68719476736 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 68719476736 % 4 = b18 at *
  have hb19 : b / 274877906944 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 274877906944 % 4 = b19 at *
  have hb20 : b / 1099511627776 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1099511627776 % 4 = b20 at *
  have hb21 : b / 4398046511104 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4398046511104 % 4 = b21 at *
  have hb22 : b / 17592186044416 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 17592186044416 % 4 = b22 at *
  have hb23 : b / 70368744177664 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 70368744177664 % 4 = b23 at *
  have hb24 : b / 281474976710656 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 281474976710656 % 4 = b24 at *
  have hb25 : b / 1125899906842624 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1125899906842624 % 4 = b25 at *
  have hb26 : b / 4503599627370496 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4503599627370496 % 4 = b26 at *
  have hb27 : b / 18014398509481984 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 18014398509481984 % 4 = b27 at *
  have hb28 : b / 72057594037927936 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 72057594037927936 % 4 = b28 at *
  have hb29 : b / 288230376151711744 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 288230376151711744 % 4 = b29 at *
  have hb30 : b / 1152921504606846976 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1152921504606846976 % 4 = b30 at *
  have hb31 : b / 4611686018427387904 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4611686018427387904 % 4 = b31 at *
  rw [lanes (a0+a1+b0+b1) (a2+a3+b2+b3) (a4+a5+b4+b5) (a6+a7+b6+b7) (a8+a9+b8+b9) (a10+a11+b10+b11) (a12+a13+b12+b13) (a14+a15+b14+b15) (a16+a17+b16+b17) (a18+a19+b18+b19) (a20+a21+b20+b21) (a22+a23+b22+b23) (a24+a25+b24+b25) (a26+a27+b26+b27) (a28+a29+b28+b29) (a30+a31+b30+b31) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) X (by
    rw [← hX]
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    omega)]
  omega

end SigGolfCandidate.Base4Candidate.SwarProof


namespace SigGolfCandidate.Base4Candidate.SwarProof
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- A mask whose set bits stay in the low machine word ignores higher bits,
even when it is applied after the fixed two-bit shift. -/
theorem mask_low_word (n shift mask : Nat) (hs : shift ≤ 64)
    (hm : mask < 2^(64-shift)) :
    (n%2^64/2^shift &&& mask) = (n/2^shift &&& mask) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i+shift < 64
  · simp [hi]
  · have hp : 2^(64-shift) ≤ (2:Nat)^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hz := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp)
    simp [hi,hz]

theorem first_low_word (a b : Nat) : first (a%2^64) b = first a b := by
  have h0 := mask_low_word a 0 3689348814741910323 (by decide) (by decide)
  have h2 := mask_low_word a 2 3689348814741910323 (by decide) (by decide)
  norm_num only [Nat.reduceSub, Nat.reducePow, Nat.div_one] at h0 h2
  unfold first
  rw [h0,h2]

theorem digit_value (d : BitVec 128) (i : Base4Candidate.Index) :
    (Base4Candidate.digits d i).val = d.toNat/4^i.val%4 := by
  simp [Base4Candidate.digits, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, pow_mul]

/-- The two high radix-four digits are zero exactly where the concrete decoder
requires four high padding bits to be clear. -/
theorem decoded_weight (d : BitVec 128) (hd : d.toNat < 2^124) :
    Base4Candidate.weight (Base4Candidate.digits d) =
      digitSum d.toNat + digitSum (d.toNat/2^64) := by
  have h62 : d.toNat/2^124 = 0 := Nat.div_eq_of_lt hd
  have h63 : d.toNat/2^126 = 0 := Nat.div_eq_of_lt (lt_trans hd (by norm_num))
  simp only [Base4Candidate.weight, digit_value, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [digitSum_expanded, digitSum_expanded]
  simp only [Nat.div_div_eq_div_mul]
  norm_num at h62 h63 ⊢
  rw [h62,h63]
  omega

/-- Exact natural arithmetic performed by the verifier's packed digit check.
The remaining machine proof must connect register operations to these terms. -/
theorem decoder_sum (d : BitVec 128) (hd : d.toNat < 2^124) :
    tail (first (d.toNat%2^64) (d.toNat/2^64)) =
      Base4Candidate.weight (Base4Candidate.digits d) := by
  rw [first_low_word, sum_exact, ← decoded_weight d hd]

end SigGolfCandidate.Base4Candidate.SwarProof


namespace SigGolfCandidate.Base4Candidate.SwarProof

abbrev maskWord2 : BitVec 64 := 3689348814741910323
abbrev maskWord4 : BitVec 64 := 1085102592571150095

def firstWord (a b : BitVec 64) : BitVec 64 :=
  ((a &&& maskWord2)+((a >>> 2) &&& maskWord2)) +
    ((b &&& maskWord2)+((b >>> 2) &&& maskWord2))

def sumWord (a b : BitVec 64) : BitVec 64 :=
  let x := firstWord a b
  ((x &&& maskWord4)+((x >>> 4) &&& maskWord4)) % 255

theorem firstWord_toNat (a b : BitVec 64) :
    (firstWord a b).toNat = first a.toNat b.toNat := by
  simp [firstWord, first, BitVec.toNat_add, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, maskWord2]

theorem sumWord_toNat (a b : BitVec 64) :
    (sumWord a b).toNat = tail (first a.toNat b.toNat) := by
  simp [sumWord, tail, BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, maskWord4, firstWord_toNat]

theorem sumWord_decoder (d : BitVec 128) (hd : d.toNat < 2^124) :
    (sumWord (BitVec.ofNat 64 d.toNat) (BitVec.ofNat 64 (d.toNat/2^64))).toNat =
      Base4Candidate.weight (Base4Candidate.digits d) := by
  have hb : d.toNat/2^64 < 2^64 := by
    have h := d.isLt
    norm_num at h ⊢
    omega
  rw [sumWord_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  exact decoder_sum d hd

end SigGolfCandidate.Base4Candidate.SwarProof


namespace SigGolfCandidate.Base4Candidate.SwarProof
open SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- Register arithmetic before instantiating the caller's masks and divisor. -/
def rawSumWord (a b m1 m2 modulus : BitVec 64) : BitVec 64 :=
  let x := ((a &&& m1)+((a >>> 2) &&& m1))+
    ((b &&& m1)+((b >>> 2) &&& m1))
  rv64_remu ((x &&& m2)+((x >>> 4) &&& m2)) modulus

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem block_register_raw (s : MachineState) :
    (Reference.AsmChecks.digit_sum.res.toState s).getReg .x24 =
      rawSumWord (s.getReg .x16) (s.getReg .x17) (s.getReg .x18)
        (s.getReg .x19) (s.getReg .x20) := by rfl

theorem block_register (s : MachineState)
    (h18 : s.getReg .x18 = maskWord2) (h19 : s.getReg .x19 = maskWord4)
    (h20 : s.getReg .x20 = 255) :
    (Reference.AsmChecks.digit_sum.res.toState s).getReg .x24 =
      sumWord (s.getReg .x16) (s.getReg .x17) := by
  rw [block_register_raw,h18,h19,h20]
  unfold rawSumWord sumWord firstWord
  rw [rv64_remu, if_neg (by decide)]
  rfl

set_option maxRecDepth 100000 in
theorem block_preserves_encoding (s : MachineState) :
    (Reference.AsmChecks.digit_sum.res.toState s).getReg .x16 = s.getReg .x16 ∧
    (Reference.AsmChecks.digit_sum.res.toState s).getReg .x17 = s.getReg .x17 := by
  exact ⟨rfl,rfl⟩

theorem block_decoder_sum (s : MachineState) (d : BitVec 128)
    (hd : d.toNat < 2^124)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 d.toNat)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 (d.toNat/2^64))
    (h18 : s.getReg .x18 = maskWord2) (h19 : s.getReg .x19 = maskWord4)
    (h20 : s.getReg .x20 = 255) :
    ((Reference.AsmChecks.digit_sum.res.toState s).getReg .x24).toNat =
      Base4Candidate.weight (Base4Candidate.digits d) := by
  rw [block_register s h18 h19 h20,h16,h17]
  exact sumWord_decoder d hd

end SigGolfCandidate.Base4Candidate.SwarProof

namespace SigGolfCandidate.Base4Candidate.SwarProof

theorem block_cost : Reference.AsmChecks.digit_sum.res.steps = 14 ∧
    Reference.AsmChecks.digit_sum.res.cycles = 17 := by
  exact ⟨rfl,rfl⟩

end SigGolfCandidate.Base4Candidate.SwarProof


namespace SigGolfCandidate.Base4Candidate.VerifyProof
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The witness-relative serialization and runtime memory address agree. -/
theorem block_serialization (lay chain : Nat) :
    blockAddress lay chain = 2048 + Reference.witnessChainOffset lay chain := by
  unfold blockAddress Reference.witnessChainOffset
  omega

theorem Fresh.mono {w : List Byte} {s : MachineState} {lay chain lay' chain' : Nat}
    (h : Fresh w lay chain s)
    (sub : ∀ a b k, FreshWord lay' chain' a b k → FreshWord lay chain a b k) :
    Fresh w lay' chain' s := fun a b k hk => h a b k (sub a b k hk)

/-- In-place chain hashing preserves all future witness words. This includes
its sixteen-byte spill into the following header. -/
theorem Fresh.hash_inplace {w : List Byte} {s : MachineState} {lay chain : Nat}
    (h : Fresh w lay chain s) (hl : lay < 4) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (blockAddress lay chain+48))
    (answer : BitVec 256) : Fresh w lay (chain+1) (writeHash s answer) := by
  intro a b k hk
  have hb := block_interval lay chain hl hi
  have ha : blockAddress a b+8*k < 2^64 := by
    rcases hk with ⟨ha,hb,hk,hk',horder⟩
    unfold blockAddress
    omega
  have hout : blockAddress a b+8*k < blockAddress lay chain+48 ∨
      blockAddress lay chain+48+32 ≤ blockAddress a b+8*k := by
    rcases hk with ⟨ha,hb,hk,hk',horder⟩
    unfold blockAddress
    rcases horder with horder | ⟨rfl,horder⟩ <;> omega
  rw [SigGolfCandidate.Sign.writeHash_getMem_frame s answer
    (blockAddress lay chain+48) (blockAddress a b+8*k) hd (by omega) ha
    (hout.imp_right Or.inl)]
  exact h a b k (fresh_next hk)

/-- The final chain hash writes into the separate leaf buffer, below every
witness chain. Its full output preserves both the current and future pads. -/
theorem Fresh.hash_leaf {w : List Byte} {s : MachineState} {lay chain : Nat}
    (h : Fresh w lay chain s) (hi : chain < 62)
    (hd : s.getReg .x12 = BitVec.ofNat 64 (Reference.ChainCode.leafSlot chain))
    (answer : BitVec 256) : Fresh w lay chain (writeHash s answer) := by
  intro a b k hk
  have hs : Reference.ChainCode.leafSlot chain+32 < 5376 := by
    unfold Reference.ChainCode.leafSlot
    omega
  have ha : blockAddress a b+8*k < 2^64 := by
    rcases hk with ⟨ha,hb,hk,hk',horder⟩
    unfold blockAddress
    omega
  have hout : Reference.ChainCode.leafSlot chain+32 ≤ blockAddress a b+8*k := by
    unfold blockAddress
    omega
  rw [SigGolfCandidate.Sign.writeHash_getMem_frame s answer
    (Reference.ChainCode.leafSlot chain) (blockAddress a b+8*k) hd
    (by omega) ha (Or.inr (Or.inl hout))]
  exact h a b k hk

end SigGolfCandidate.Base4Candidate.VerifyProof


namespace SigGolfCandidate.Base4Candidate
open SigGolfCandidate.Legacy

/-- The four alternate programs and their actual declared input/output buffers.
This value is not selected in Solution.lean until its complete certificate exists. -/
def candidateSubmission : Submission where
  sizes := ⟨7232,19200,131072⟩
  layout := ⟨64,128,160,32768,196608,2048⟩
  image
    | .keygen => Reference.KeygenCode.image
    | .sign => Reference.SignLayerCode.image
    | .expand => Reference.ExpandCode.image
    | .verify => Reference.VerifyImage.image

theorem candidate_sizes_valid : candidateSubmission.sizes.Valid := by decide

theorem candidate_image_valid (phase : Phase) :
    (candidateSubmission.image phase).Valid candidateSubmission.sizes candidateSubmission.layout := by
  cases phase with
  | keygen => exact ⟨Reference.KeygenCode.image_room, by decide⟩
  | sign => exact ⟨Reference.SignLayerCode.image_room, by decide⟩
  | expand => exact ⟨Reference.ExpandCode.image_room, by decide⟩
  | verify => exact ⟨Reference.VerifyImage.image_room, by decide⟩

theorem candidate_witness_charge : witnessCycles candidateSubmission.sizes.witness = 75 := rfl

end SigGolfCandidate.Base4Candidate
