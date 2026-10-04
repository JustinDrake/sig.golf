import SigGolfCandidate.Ref.Basic
import VCVio.EvalDist.Expectation

section

namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy OracleComp OracleSpec
abbrev NodeFmt := Nat → Nat → Val → Val → List Byte
def buildLevel (node : NodeFmt) (lam : Nat) (level : List Val) :
    OracleComp HashSpec (List Val) :=
  (List.range (level.length / 2)).foldlM (fun acc j => do
    let v ← hash16 (node lam j (level.getD (2 * j) []) (level.getD (2 * j + 1) []))
    pure (acc ++ [v])) []
def levelStep (node : NodeFmt) (cap : Nat) (st : List Val × List Val) (lam : Nat) :
    OracleComp HashSpec (List Val × List Val) := do
  let path := st.2 ++ [st.1.getD ((cap / 2 ^ (lam - 1)) ^^^ 1) []]
  let level ← buildLevel node lam st.1
  pure (level, path)
def buildLevels (node : NodeFmt) (cap h : Nat) (leaves : List Val) :
    OracleComp HashSpec (Val × List Val) := do
  let st ← (List.range' 1 h).foldlM (levelStep node cap) (leaves, [])
  pure (st.1.getD 0 [], st.2)
def chainSteps (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec (Val × Val) :=
  (List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
    let v ← hash16 (chainInput lay tau e i mu st.1)
    pure (v, if mu = x then v else st.2)) (v, v)
def buildLeaf (S : List Byte) (lay tau e : Nat) (x : List Nat) :
    OracleComp HashSpec (Val × List Val) := do
  let st ← (List.range (nChains / 2)).foldlM (fun (st : List Val × List Val) k => do
    let (s0, s1) ← prf2 (prfInput S lay tau e k)
    let (v0, c0) ← chainSteps lay tau e (2 * k) (x.getD (2 * k) 0) s0
    let (v1, c1) ← chainSteps lay tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
    pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1])) ([], [])
  let leaf ← hash16 (leafInput lay tau e st.1)
  pure (leaf, st.2)
def buildLeaves (S : List Byte) (lay tau h cap : Nat) (x : List Nat) :
    OracleComp HashSpec (List Val × List Val) :=
  (List.range (2 ^ h)).foldlM (fun (st : List Val × List Val) e => do
    let (leaf, c) ← buildLeaf S lay tau e x
    pure (st.1 ++ [leaf], if e = cap then c else st.2)) ([], [])
def buildTree (S : List Byte) (lay tau h cap : Nat) (x : List Nat) :
    OracleComp HashSpec (Val × List Val × List Val) := do
  let (leaves, vals) ← buildLeaves S lay tau h cap x
  let (root, path) ← buildLevels (nodeInput lay tau) cap h leaves
  pure (root, vals, path)
def buildAllLevels (node : NodeFmt) (h : Nat) (leaves : List Val) :
    OracleComp HashSpec (List (List Val)) :=
  (List.range' 1 h).foldlM (fun (levels : List (List Val)) lam => do
    let level ← buildLevel node lam (levels.getD (lam - 1) [])
    pure (levels ++ [level])) [leaves]
def maskLevel (S : List Byte) (l : Nat) (level : List Val) : OracleComp HashSpec (List Val) :=
  (List.range level.length).foldlM (fun acc j => do
    let mk ← hash16 (maskInput S l j)
    pure (acc ++ [xorBytes (level.getD j []) mk])) []
def keygenList (S : List Byte) : OracleComp HashSpec (Val × List Byte) := do
  let (leaves, _) ← buildLeaves S 0 0 topH 0 []
  let levels ← buildAllLevels (nodeInput 0 0) topH leaves
  let masked ← (List.range topH).foldlM (fun (acc : List Val) l => do
    let ml ← maskLevel S l (levels.getD l [])
    pure (acc ++ ml)) []
  let region := masked.flatten
  let tag ← H (macInput S region)
  pure ((levels.getD topH []).getD 0 [],
    toList (n := 32) tag ++ region ++ zeros (cacheBytes - 32 - regionBytes))
def keygenRef (sk : Bytes 32) : OracleComp HashSpec (Bytes 16 × Cache) := do
  let (root, cache) ← keygenList (toList sk)
  pure (ofList 16 root, ofList CACHE_BYTES cache)
def searchDigest (S m : List Byte) (a : Nat) : Nat → OracleComp HashSpec (Option (Val × Nat))
  | 0 => pure none
  | fuel + 1 => do
    let rho ← hash16 (rndInput S m a)
    let N ← digest rho m
    if admissible N then pure (some (rho, N)) else searchDigest S m (a + 1) fuel
def buildPorsLeaves (S : List Byte) (idx : Nat) : OracleComp HashSpec (List Val × List Val) :=
  (List.range (porsT / 2)).foldlM (fun (st : List Val × List Val) q => do
    let (s0, s1) ← prf2 (porsPrfInput S idx q)
    let l0 ← hash16 (porsLeafInput idx (2 * q) s0)
    let l1 ← hash16 (porsLeafInput idx (2 * q + 1) s1)
    pure (st.1 ++ [l0, l1], st.2 ++ [s0, s1])) ([], [])
def porsNodeFmt (idx : Nat) : NodeFmt := fun lam j l r => porsNodeInput idx (heapIndex porsH lam j) l r
def buildPorsTree (S : List Byte) (idx : Nat) :
    OracleComp HashSpec (List (List Val) × List Val) := do
  let (leaves, secrets) ← buildPorsLeaves S idx
  let levels ← buildAllLevels (porsNodeFmt idx) porsH leaves
  pure (levels, secrets)
def porsOpening (vs : List Nat) (levels : List (List Val)) (secrets : List Val) : List Val :=
  let fts := vs.map (fun x => secrets.getD x []) ++
    (schedule vs).2.map (fun hj => (levels.getD hj.1 []).getD hj.2 [])
  fts ++ List.replicate (porsK + porsM - fts.length) (zeros 16)
def searchCounter (lay tau e : Nat) (M : Val) (c : Nat) :
    Nat → OracleComp HashSpec (Option (Nat × List Nat))
  | 0 => pure none
  | fuel + 1 => do
    let d ← hash16 (encInput lay tau e M c)
    match decodeDigits d with
    | some x => pure (some (c, x))
    | none => searchCounter lay tau e M (c + 1) fuel
abbrev LayerSig := Nat × List Val × List Val
def chainTo (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' 1 x).foldlM (fun v mu => hash16 (chainInput lay tau e i mu v)) v
def topPath (S cache : List Byte) (e : Nat) : OracleComp HashSpec (List Val) :=
  (List.range topH).foldlM (fun acc l => do
    let s := (e / 2 ^ l) ^^^ 1
    let mk ← hash16 (maskInput S l s)
    pure (acc ++ [xorBytes (cacheNode cache l s) mk])) []
def signTop (S cache : List Byte) (idx : Nat) (M : Val) :
    OracleComp HashSpec (Option (List LayerSig)) := do
  let (e, tau) := route idx 0
  match ← searchCounter 0 tau e M 0 cMax with
  | none => pure none
  | some (c, x) =>
    let vals ← (List.range (nChains / 2)).foldlM (fun acc k => do
      let (s0, s1) ← prf2 (prfInput S 0 tau e k)
      let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
      let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
      pure (acc ++ [v0, v1])) []
    let path ← topPath S cache e
    pure (some [(c, vals, path)])
def signLayers (S cache : List Byte) (idx : Nat) :
    Nat → Val → OracleComp HashSpec (Option (List LayerSig))
  | 0, M => signTop S cache idx M
  | lay + 1, M => do
    let (e, tau) := route idx (lay + 1)
    match ← searchCounter (lay + 1) tau e M 0 cMax with
    | none => pure none
    | some (c, x) =>
      let (root, vals, path) ← buildTree S (lay + 1) tau (height (lay + 1)) e x
      match ← signLayers S cache idx lay root with
      | none => pure none
      | some rest => pure (some (rest ++ [(c, vals, path)]))
def serialize (rho : Val) (fts : List Val) (lays : List LayerSig) : List Byte :=
  rho ++ fts.flatten ++
    (lays.map fun l => l.2.1.flatten ++ l.2.2.flatten).flatten
def signList (S cache m : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  let tag ← H (macInput S (cacheRegion cache))
  if toList (n := 32) tag = cacheTag cache then
    match ← searchDigest S m 0 aMax with
    | none => pure none
    | some (rho, N) =>
      let (levels, secrets) ← buildPorsTree S (idxOf N)
      let M := (levels.getD porsH []).getD 0 []
      let fts := porsOpening (sortLeaves (leavesOf N)) levels secrets
      match ← signLayers S cache (idxOf N) (nLayers - 1) M with
      | none => pure none
      | some lays => pure (some (serialize rho fts lays))
  else pure none
def signRef (sk : Bytes 32) (cache : Cache) (m : Bytes 32) :
    OracleComp HashSpec (Option (Bytes 6048)) := do
  let r ← signList (toList sk) (toList cache) (toList m)
  pure (r.map (ofList 6048))
def sigLayerBytes (lay : Nat) : Nat := 4 + 16 * nChains + 16 * height lay
def bodyBytes (lay : Nat) : Nat := 16 * nChains + 16 * height lay
def headBytes : Nat := 16 + 16 * (porsK + porsM)
def sigLayerOff (lay : Nat) : Nat := headBytes + ((List.range lay).map bodyBytes).sum
def sigRho (sig : List Byte) : Val := slice sig 0 16
def sigItem (sig : List Byte) (i : Nat) : Val := slice sig (16 + 16 * i) 16
def sigAuth (sig : List Byte) (i : Nat) : Val := sigItem sig (porsK + i)
def sigLayerBody (sig : List Byte) (lay : Nat) : List Byte := slice sig (sigLayerOff lay) (bodyBytes lay)
def wPi : Nat := 16
def wSec : Nat := 32
def wStream : Nat := wSec + 16 * porsK
def streamBytes : Nat := 8 * porsSegs + 16 * 120
def wLayers : Nat := wStream + streamBytes
def witLayerOff (lay : Nat) : Nat := wLayers + ((List.range lay).map fun l => sigLayerBytes l - 4).sum
def witCounters : Nat := witLayerOff nLayers
def streamStep (sig : List Byte) (st : List Byte × Nat) (b : Nat) : List Byte × Nat :=
  (st.1 ++ [byte b] ++ zeros 7 ++ ((List.range (b % 16)).map fun i => sigAuth sig (st.2 + i)).flatten,
    st.2 + b % 16)
def segStream (sig : List Byte) (segs : List Nat) : List Byte := (segs.foldl (streamStep sig) ([], 0)).1
def witnessBody (sig : List Byte) (v vs segs : List Nat) : List Byte :=
  sigRho sig ++ vs.map (fun x => byte (8 * v.idxOf x)) ++ zeros (wSec - wPi - porsK) ++
    ((List.range porsK).map (sigItem sig)).flatten ++
    (segStream sig segs ++ zeros streamBytes).take streamBytes ++
    ((List.range nLayers).map (sigLayerBody sig)).flatten
def witnessList (sig : List Byte) (v vs segs : List Nat) : List Byte :=
  witnessBody sig v vs segs ++ zeros (4 * nLayers)
def expandOf (sig : List Byte) (N : Nat) : Option (List Byte) :=
  let v := leavesOf N
  if !decide v.Nodup then none
  else
    let vs := sortLeaves v
    if octopusSize vs > porsM then none
    else
      let (segs, reads) := schedule vs
      let n := reads.length
      if !(List.range' n (porsM - n)).all (fun i => sigAuth sig i == zeros 16) then none
      else some (witnessList sig v vs segs)
def witRho (w : List Byte) : Val := slice w 0 16
def witPi (w : List Byte) (s : Nat) : Nat := (w.getD (wPi + s) 0).toNat
def witSecret (w : List Byte) (s : Nat) : Val := slice w (wSec + 16 * s) 16
def wbyte (w : List Byte) (off : Nat) : Nat := (w.getD off 0).toNat
def wbytes (w : List Byte) (off n : Nat) : Val := (List.range n).map fun i => w.getD (off + i) 0
def witChain (w : List Byte) (lay i : Nat) : Val := slice w (witLayerOff lay + 16 * i) 16
def witSib (w : List Byte) (lay l : Nat) : Val := slice w (witLayerOff lay + 672 + 16 * l) 16
def witPath (w : List Byte) (lay : Nat) : List Val := (List.range (height lay)).map (witSib w lay)
def witCounter (w : List Byte) (lay : Nat) : Nat := leNat (slice w (witCounters + 4 * lay) 4)
def countersOk (w : List Byte) : Bool := (List.range nLayers).all fun lay => witCounter w lay < cMax
def foldPath (node : NodeFmt) (leaf : Nat) (v : Val) (path : List Val) : OracleComp HashSpec Val :=
  (List.range path.length).foldlM (fun v lam =>
    let sib := path.getD lam []
    let j := leaf / 2 ^ (lam + 1)
    if leaf / 2 ^ lam % 2 = 1 then hash16 (node (lam + 1) j sib v)
    else hash16 (node (lam + 1) j v sib)) v
inductive Pending where
  | leaf (x : Nat) (s : Val)
  | merge (H : Nat) (l : Val)
def pendingHash (idx : Nat) (node : Val) : Pending → OracleComp HashSpec Val
  | .leaf x s => hash16 (porsLeafInput idx x s)
  | .merge H l => hash16 (porsNodeInput idx H l node)
def segFolds (idx : Nat) (w : List Byte) (ptr a : Nat) (node : Val) (E : Nat) :
    OracleComp HashSpec (Val × Nat) :=
  (List.range a).foldlM (fun (st : Val × Nat) i =>
    let sib := wbytes w (ptr + 8 + 16 * i) 16
    if st.2 % 2 = 1 then do
      let v ← hash16 (porsNodeInput idx (st.2 / 2) sib st.1)
      pure (v, st.2 / 2)
    else do
      let v ← hash16 (porsNodeInput idx (st.2 / 2) st.1 sib)
      pure (v, st.2 / 2)) (node, E)
def segment (idx : Nat) (w : List Byte) (ptr E folds : Nat) (pending : Pending) (node : Val) :
    OracleComp HashSpec (Option (Nat × Nat × Nat × Val × Bool)) := do
  let b := wbyte w ptr
  let a := b % 16
  let merge := b / 16 % 2
  let t := b / 32 % 2
  if a > porsH then pure none
  else if 0 < a ∧ t ≠ E % 2 then pure none
  else
    let node ← pendingHash idx node pending
    let (node, E) ← segFolds idx w ptr a node E
    pure (some (ptr + 8 + 16 * a, E, folds + a, node, merge = 1))
def segLoop (idx : Nat) (w : List Byte) :
    Nat → Nat → Nat → Pending → Val → List (Val × Nat) →
      OracleComp HashSpec (Option (Nat × Nat × Nat × Val × List (Val × Nat)))
  | ptr, E, folds, pending, node, [] => do
    match ← segment idx w ptr E folds pending node with
    | none => pure none
    | some (ptr, E, folds, node, merge) =>
      if merge then pure none else pure (some (ptr, E, folds, node, []))
  | ptr, E, folds, pending, node, (pnode, Q) :: rest => do
    match ← segment idx w ptr E folds pending node with
    | none => pure none
    | some (ptr, E, folds, node, merge) =>
      if !merge then pure (some (ptr, E, folds, node, (pnode, Q) :: rest))
      else if Q ≠ E then pure none
      else segLoop idx w ptr (E / 2) folds (.merge (E / 2) pnode) node rest
structure PorsState where
  ptr : Nat
  prev : Nat
  E : Nat
  folds : Nat
  node : Val
  stack : List (Val × Nat)
def porsLeaves (idx : Nat) (v : List Nat) (w : List Byte) :
    List Nat → PorsState → OracleComp HashSpec (Option PorsState)
  | [], st => pure (some st)
  | s :: rest, st => do
    let x := (v ++ [porsT]).getD (witPi w s / 8 % 16) 0
    if s ≠ 0 ∧ ¬ st.prev < x then pure none
    else if s = porsK - 1 ∧ ¬ x < porsT then pure none
    else
      match ← segLoop idx w st.ptr (porsT ||| x) st.folds (.leaf x (witSecret w s)) st.node
          st.stack with
      | none => pure none
      | some (ptr, E, folds, node, stack) =>
        let stack := if s < porsK - 1 then (node, E ^^^ 1) :: stack else stack
        porsLeaves idx v w rest ⟨ptr, x, E, folds, node, stack⟩
def porsRoot (idx : Nat) (v : List Nat) (w : List Byte) : OracleComp HashSpec (Option Val) := do
  match ← porsLeaves idx v w (List.range porsK) ⟨wStream, 0, 0, 0, [], []⟩ with
  | none => pure none
  | some st =>
    if st.folds > porsM ∨ st.E ≠ 1 ∨ st.stack ≠ [] then pure none else pure (some st.node)
def chainFrom (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' (x + 1) (7 - x)).foldlM (fun v mu => hash16 (chainInput lay tau e i mu v)) v
def verifyLeaf (w : List Byte) (lay tau e : Nat) (x : List Nat) : OracleComp HashSpec Val := do
  let ends ← (List.range nChains).foldlM (fun ends i => do
    let v ← chainFrom lay tau e i (x.getD i 0) (witChain w lay i)
    pure (ends ++ [v])) []
  hash16 (leafInput lay tau e ends)
def verifyLayers (w : List Byte) (idx : Nat) : Nat → Val → OracleComp HashSpec (Option Val)
  | 0, M => pure (some M)
  | lay + 1, M => do
    let (e, tau) := route idx lay
    let d ← hash16 (encInput lay tau e M (witCounter w lay))
    match decodeDigits d with
    | none => pure none
    | some x =>
      let leaf ← verifyLeaf w lay tau e x
      let root ← foldPath (nodeInput lay tau) e leaf (witPath w lay)
      verifyLayers w idx lay root
def verifyList (m pk w : List Byte) : OracleComp HashSpec Bool := do
  if !countersOk w then return false
  let N ← digest (witRho w) m
  match ← porsRoot (idxOf N) (leavesOf N) w with
  | none => pure false
  | some M =>
    match ← verifyLayers w (idxOf N) nLayers M with
    | none => pure false
    | some root => pure (root == pk)
def verifyRef (m : Bytes 32) (pk : Bytes 16) (w : Bytes 6348) : OracleComp HashSpec Bool :=
  verifyList (toList m) (toList pk) (toList w)
def expandLayers (w : List Byte) (idx : Nat) : Nat → Val → OracleComp HashSpec (Option (List Nat))
  | 0, _ => pure (some [])
  | 1, M => do
    let (e, tau) := route idx 0
    match ← searchCounter 0 tau e M 0 cMax with
    | none => pure none
    | some (c, _) => pure (some [c])
  | lay + 2, M => do
    let (e, tau) := route idx (lay + 1)
    match ← searchCounter (lay + 1) tau e M 0 cMax with
    | none => pure none
    | some (c, x) =>
      let leaf ← verifyLeaf w (lay + 1) tau e x
      let root ← foldPath (nodeInput (lay + 1) tau) e leaf (witPath w (lay + 1))
      match ← expandLayers w idx (lay + 1) root with
      | none => pure none
      | some cs => pure (some (cs ++ [c]))
def withCounters (w0 : List Byte) (cs : List Nat) : List Byte := w0.take witCounters ++ (cs.map le32).flatten
def expandList (m sig : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  let N ← digest (sigRho sig) m
  match expandOf sig N with
  | none => pure none
  | some w0 =>
    match ← porsRoot (idxOf N) (leavesOf N) w0 with
    | none => pure none
    | some M =>
      match ← expandLayers w0 (idxOf N) nLayers M with
      | none => pure none
      | some cs => pure (some (withCounters w0 cs))
def expandRef (m : Bytes 32) (_pk : Bytes 16) (sig : Bytes 6048) :
    OracleComp HashSpec (Option (Bytes 6348)) := do
  let r ← expandList (toList m) (toList sig)
  pure (r.map (ofList 6348))
def verifySigRef (m : Bytes 32) (pk : Bytes 16) (sig : Bytes 6048) : OracleComp HashSpec Bool := do
  match ← expandRef m pk sig with
  | none => pure false
  | some w => verifyRef m pk w
end SigGolfCandidate.Ref
end

section

namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy OracleComp OracleSpec
universe u
def countImpl (wt : Query → Nat) : QueryImpl HashSpec (StateT Nat (OracleComp HashSpec)) :=
  fun q => do
    modify (· + wt q)
    liftM (HashSpec.query q)
def countWith (wt : Query → Nat) {α : Type} (oa : OracleComp HashSpec α) :
    OracleComp HashSpec (α × Nat) :=
  (simulateQ (countImpl wt) oa).run 0
def countCalls {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat) :=
  countWith (fun _ => 1) oa
def countBlocks {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat) :=
  countWith Query.blocks oa
section
variable (wt : Query → Nat) {α β : Type}
theorem countImpl_run (oa : OracleComp HashSpec α) (n : Nat) :
    (simulateQ (countImpl wt) oa).run n = (fun p => (p.1, n + p.2)) <$> countWith wt oa := by
  unfold countWith
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT Nat (OracleComp HashSpec) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp HashSpec _) := fun s => rfl
    simp only [hl, bind_map_left, ih _ (n + wt q), ih _ (0 + wt q), Functor.map_map]
    congr 1; funext a; congr 1; funext p; simp only [Prod.mk.injEq, true_and]; omega
@[simp] theorem countWith_pure (a : α) : countWith wt (pure a : OracleComp HashSpec α) = pure (a, 0) :=
  rfl
theorem countWith_bind (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countWith wt (oa >>= f) =
      countWith wt oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countWith wt (f p.1) := by
  conv_lhs => unfold countWith
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl_run wt (f p.1) p.2)
@[simp] theorem countWith_query (q : Query) :
    countWith wt (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, wt q)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) := by
  unfold countWith
  rw [simulateQ_spec_query]
  simp only [countImpl, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl
@[simp] theorem fst_countWith (oa : OracleComp HashSpec α) : Prod.fst <$> countWith wt oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countWith_bind, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    exact ih a
@[simp] theorem countWith_H (x : List Byte) :
    countWith wt (H x) = (fun a => (a, wt (fmt x))) <$> H x :=
  countWith_query wt (fmt x)
end
theorem countCalls_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countCalls (oa >>= f) =
      countCalls oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countCalls (f p.1) :=
  countWith_bind _ oa f
@[simp] theorem countCalls_pure {α : Type} (a : α) :
    countCalls (pure a : OracleComp HashSpec α) = pure (a, 0) := rfl
@[simp] theorem countCalls_query (q : Query) :
    countCalls (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, 1)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) :=
  countWith_query _ q
@[simp] theorem countCalls_H (x : List Byte) : countCalls (H x) = (fun a => (a, 1)) <$> H x :=
  countWith_H _ x
@[simp] theorem fst_countCalls {α : Type} (oa : OracleComp HashSpec α) :
    Prod.fst <$> countCalls oa = oa := fst_countWith _ oa
theorem evalWith_countCalls_fst {α : Type} (hash : Hash) (oa : OracleComp HashSpec α) :
    (evalWithAnswerFn hash (countCalls oa)).1 = evalWithAnswerFn hash oa := by
  conv_rhs => rw [← fst_countCalls oa]
  simp only [evalWithAnswerFn, simulateQ_map]
  rfl
end SigGolfCandidate.Ref
end

section


namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy
theorem byte_toNat (v : Nat) : (byte v).toNat = v % 256 := by simp [byte]
theorem leNat_lt (l : List Byte) : leNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b bs ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have := b.isLt
    simp only [Nat.reducePow] at this
    nlinarith
theorem leNat_map_range (n v : Nat) :
    leNat ((List.range n).map fun i => byte (v / 256 ^ i)) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [leNat, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [leNat, Nat.pow_zero, Nat.div_one, byte_toNat]
    have h : (fun i => byte (v / 256 ^ i)) ∘ Nat.succ = fun i => byte (v / 256 / 256 ^ i) := by
      funext i; simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [h, ih, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
theorem leNat_div_mod (l : List Byte) (i : Nat) :
    leNat l / 256 ^ i % 256 = (l.getD i 0).toNat := by
  induction l generalizing i with
  | nil => simp [leNat]
  | cons b bs ih =>
    have hb := b.isLt
    cases i with
    | zero => simp only [leNat, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]; simp at hb ⊢; omega
    | succ i =>
      simp only [leNat, List.getD_cons_succ, Nat.pow_succ]
      rw [Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul]
      rw [show (b.toNat + 256 * leNat bs) / 256 = leNat bs by simp at hb; omega]
      exact ih i
theorem extractByte_ofNat (w v i : Nat) (h : 8 * i + 8 ≤ w) :
    (BitVec.ofNat w v).extractLsb' (8 * i) 8 = byte (v / 256 ^ i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, byte_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]
  rw [show w = 8 * i + (w - 8 * i) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
theorem toList_ofList (n : Nat) (l : List Byte) (h : l.length = n) : toList (ofList n l) = l := by
  subst h
  apply List.ext_getElem (by simp [toList, SigGolfCandidate.Legacy.bytes])
  intro i h1 h2
  simp only [toList, SigGolfCandidate.Legacy.bytes, ofList, List.getElem_map, List.getElem_range]
  rw [extractByte_ofNat _ _ _ (by simp [toList, SigGolfCandidate.Legacy.bytes] at h1; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
theorem toList_eq_map {n : Nat} (x : Bytes n) :
    toList x = (List.range n).map fun i => byte (x.toNat / 256 ^ i) := by
  simp only [toList, SigGolfCandidate.Legacy.bytes]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := extractByte_ofNat (8 * n) x.toNat i (by omega)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
theorem leNat_toList {n : Nat} (x : Bytes n) : leNat (toList x) = x.toNat := by
  rw [toList_eq_map, leNat_map_range, Nat.mod_eq_of_lt]
  have := x.isLt
  rwa [Nat.pow_mul] at this
theorem ofList_toList {n : Nat} (x : Bytes n) : ofList n (toList x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [ofList, leNat_toList]
theorem length_toList {n : Nat} (x : Bytes n) : (toList x).length = n := by
  simp [toList, SigGolfCandidate.Legacy.bytes]
@[simp] theorem length_leBytes (k v : Nat) : (leBytes k v).length = k := by simp [leBytes]
@[simp] theorem length_le32 (v : Nat) : (le32 v).length = 4 := by simp [le32]
@[simp] theorem length_zeros (k : Nat) : (zeros k).length = k := by simp [zeros]
@[simp] theorem length_P : P.length = 16 := rfl
@[simp] theorem length_tweak (t lay tau p j : Nat) : (tweak t lay tau p j).length = 16 := by
  simp [tweak]
@[simp] theorem length_answerBytes (k : Nat) (a : BitVec 256) : (answerBytes k a).length = k := by
  simp [answerBytes]
@[simp] theorem length_thInput (tw payload : List Byte) :
    (thInput tw payload).length = tw.length + 16 + payload.length := by
  simp [thInput]; omega
theorem padBlocks_eq (len n : Nat) (h1 : len ≤ 64 * (n + 1)) (h2 : 64 * n < len) :
    padBlocks len = n := by
  unfold padBlocks; omega
theorem pad64_eq (x : List Byte) (n : Nat) (h1 : x.length ≤ 64 * (n + 1)) (h2 : 64 * n < x.length) :
    pad64 x = ⟨n, ofList _ (x ++ zeros (64 * (n + 1) - x.length))⟩ := by
  unfold pad64 padTo64
  rw [padBlocks_eq _ _ h1 h2]
theorem leNat_le32 (v : Nat) : leNat (le32 v) = v % 2 ^ 32 := by
  unfold le32 leBytes; rw [leNat_map_range]; norm_num
theorem fmt_of_chain (x : List Byte) (h : IsChainFmt x) : fmt x = ⟨0, ofList _ (chainBlock x)⟩ := by
  unfold fmt; rw [if_pos h]
theorem fmt_of_node (x : List Byte) (h : IsNodeFmt x) : fmt x = ⟨0, ofList _ (nodeBlock x)⟩ := by
  unfold fmt; rw [if_neg (fun hc => by have := hc.1.symm.trans h.1; omega), if_pos h]
theorem fmt_of_digest (x : List Byte) (h : IsDigestFmt x) : fmt x = ⟨0, ofList _ (digestBlock x)⟩ := by
  unfold fmt
  rw [if_neg (fun hc => by have := hc.1.symm.trans h.1; omega),
    if_neg (fun hc => by have := hc.1.symm.trans h.1; omega), if_pos h]
theorem fmt_of_plain (x : List Byte) (h1 : ¬ IsChainFmt x) (h2 : ¬ IsNodeFmt x)
    (h3 : ¬ IsDigestFmt x) : fmt x = pad64 x := by
  unfold fmt; rw [if_neg h1, if_neg h2, if_neg h3]
theorem fmt_of_tag (x : List Byte) (h : x.getD 1 0 ∉ [byte 1, byte 3, byte 12]) :
    fmt x = pad64 x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact fmt_of_plain x (fun hc => h.1 hc.2) (fun hc => h.2.1 hc.2) (fun hc => h.2.2 hc.2)
theorem fmt_of_length (x : List Byte) (h : x.length ≠ 48 ∧ x.length ≠ 64 ∧ x.length ≠ 96) :
    fmt x = pad64 x :=
  fmt_of_plain x (fun hc => h.1 hc.1) (fun hc => h.2.1 hc.1) (fun hc => h.2.2 hc.1)
theorem getD_one_thInput (t lay tau p j : Nat) (payload : List Byte) :
    (thInput (tweak t lay tau p j) payload).getD 1 0 = byte t := by
  simp [thInput, tweak]
theorem fmt_thInput (t lay tau p j : Nat) (payload : List Byte)
    (ht : byte t ∉ [byte 1, byte 3, byte 12]) :
    fmt (thInput (tweak t lay tau p j) payload) = pad64 (thInput (tweak t lay tau p j) payload) :=
  fmt_of_tag _ (by rw [getD_one_thInput]; exact ht)
private theorem thInput_split (t lay tau p j : Nat) (pl : List Byte) :
    thInput (tweak t lay tau p j) pl =
      [byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ (le32 p ++ (le32 (tau % 2 ^ 32) ++
        (le32 j ++ (P ++ pl)))) := by
  simp [thInput, tweak]
private theorem take_app {l₁ : List Byte} (l₂ : List Byte) {n : Nat} (h : l₁.length = n) :
    (l₁ ++ l₂).take n = l₁ := by subst h; simp
private theorem drop_app {l₁ : List Byte} (l₂ : List Byte) {n : Nat} (h : l₁.length = n) :
    (l₁ ++ l₂).drop n = l₂ := by subst h; simp
theorem fmt_thInput_chain (lay tau p j : Nat) (v : Val) (hv : v.length = 16) (hp : p < 2 ^ 32) :
    fmt (thInput (tweak 1 lay tau p j) v) =
      ⟨0, ofList _ (tweak 1 lay tau (splitP p) j ++ zeros 32 ++ v)⟩ := by
  have hc : IsChainFmt (thInput (tweak 1 lay tau p j) v) :=
    ⟨by simp [hv], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_chain _ hc]
  congr 2
  unfold chainBlock slice
  rw [thInput_split]
  have e4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).take 4 = [a, b, c, d] :=
    fun l a b c d => rfl
  have d4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).drop 4 = l :=
    fun l a b c d => rfl
  rw [e4, d4, take_app _ (length_le32 p), leNat_le32, Nat.mod_eq_of_lt hp]
  rw [show (8 : Nat) = 4 + 4 from rfl, ← List.drop_drop, d4, drop_app _ (length_le32 p),
    show 32 = 4 + 28 from rfl, ← List.drop_drop, d4, show 28 = 4 + 24 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 p), show 24 = 4 + 20 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), show 20 = 4 + 16 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), drop_app _ length_P]
  have : (le32 (tau % 2 ^ 32) ++ (le32 j ++ (P ++ v))).take (4 + 4) = le32 (tau % 2 ^ 32) ++ le32 j := by
    rw [List.take_add, take_app _ (length_le32 _), drop_app _ (length_le32 _), take_app _ (length_le32 _)]
  rw [this]
  simp [tweak, zeros]
theorem fmt_chainInput (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) (hmu : 1 ≤ mu)
    (hmu' : mu ≤ 8) (hi : i < 2 ^ 24) :
    fmt (chainInput lay tau e i mu v) =
      ⟨0, ofList _ (tweak 1 lay tau (mu - 1 + 256 * i) e ++ zeros 32 ++ v)⟩ := by
  unfold chainInput
  rw [fmt_thInput_chain _ _ _ _ _ hv (by omega)]
  have : splitP (8 * i + mu - 1) = mu - 1 + 256 * i := by unfold splitP; omega
  rw [this]
theorem fmt_thInput_node (lay tau lam j : Nat) (pl : List Byte)
    (hpl : pl.length = 32) (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32) :
    fmt (thInput (tweak 3 lay tau lam j) pl) =
      ⟨0, ofList _ (thInput (tweak 3 lay tau 0 (heapIndex (height (lay % 256)) lam j)) pl)⟩ := by
  have hn : IsNodeFmt (thInput (tweak 3 lay tau lam j) pl) :=
    ⟨by simp [hpl], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_node _ hn]
  congr 2
  have hh : nodeHeight (thInput (tweak 3 lay tau lam j) pl) = height (lay % 256) := by
    simp [nodeHeight, thInput, tweak, byte_toNat]
  unfold nodeBlock slice
  rw [hh, thInput_split]
  have e4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).take 4 = [a, b, c, d] :=
    fun l a b c d => rfl
  have d4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).drop 4 = l :=
    fun l a b c d => rfl
  rw [e4, d4, take_app _ (length_le32 lam), leNat_le32, Nat.mod_eq_of_lt hlam]
  rw [show (8 : Nat) = 4 + 4 from rfl, ← List.drop_drop, d4, drop_app _ (length_le32 lam),
    take_app _ (length_le32 _), show 12 = 4 + 8 from rfl, ← List.drop_drop, d4,
    show 8 = 4 + 4 from rfl, ← List.drop_drop, drop_app _ (length_le32 lam),
    drop_app _ (length_le32 _), take_app _ (length_le32 j), leNat_le32, Nat.mod_eq_of_lt hj,
    show 16 = 4 + 12 from rfl, ← List.drop_drop, d4, show 12 = 4 + 8 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 lam), show 8 = 4 + 4 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), drop_app _ (length_le32 j)]
  simp [thInput, tweak]
theorem fmt_nodeInput (lay tau lam j : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16)
    (hlay : lay < 256) (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32) :
    fmt (nodeInput lay tau lam j l r) =
      ⟨0, ofList _ (thInput (tweak 3 lay tau 0 (heapIndex (height lay) lam j)) (l ++ r))⟩ := by
  unfold nodeInput
  rw [fmt_thInput_node _ _ _ _ _ (by simp [hl, hr]) hlam hj, Nat.mod_eq_of_lt hlay]
theorem fmt_porsNodeInput (idx H : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    fmt (porsNodeInput idx H l r) = ⟨0, ofList _ (porsNodeInput idx H l r)⟩ := by
  unfold porsNodeInput
  rw [fmt_thInput _ _ _ _ _ _ (by decide),
    pad64_eq _ 0 (by simp [hl, hr]) (by simp [hl, hr])]
  simp [hl, hr, zeros]
theorem fmt_porsLeafInput (idx j : Nat) (s : Val) (hs : s.length = 16) :
    fmt (porsLeafInput idx j s) = ⟨0, ofList _ (porsLeafInput idx j s ++ zeros 16)⟩ := by
  unfold porsLeafInput
  rw [fmt_thInput _ _ _ _ _ _ (by decide), pad64_eq _ 0 (by simp [hs]) (by simp [hs])]
  simp [hs]
theorem fmt_porsPrfInput (S : List Byte) (idx q : Nat) :
    fmt (porsPrfInput S idx q) = pad64 (porsPrfInput S idx q) :=
  fmt_thInput _ _ _ _ _ _ (by decide)
theorem fmt_digestInput (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    fmt (digestInput rho m) = ⟨0, ofList _ (tweak 12 0 0 0 0 ++ rho ++ m)⟩ := by
  have hd : IsDigestFmt (digestInput rho m) :=
    ⟨by simp [digestInput, hr, hm], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_digest _ hd]
  congr 2
  unfold digestBlock slice digestInput thInput
  have h16 := length_tweak 12 0 0 0 0
  simp only [List.append_assoc]
  rw [take_app _ h16, show 32 = 16 + 16 from rfl, ← List.drop_drop, drop_app _ h16,
    drop_app _ length_P, take_app _ hr, show 64 = 16 + 48 from rfl, ← List.drop_drop, drop_app _ h16,
    show 48 = 16 + 32 from rfl, ← List.drop_drop, drop_app _ length_P,
    show 32 = 16 + 16 from rfl, ← List.drop_drop, drop_app _ hr, drop_app _ (length_zeros 16)]
theorem length_chainBlock (x : List Byte) (h : x.length = 48) : (chainBlock x).length = 64 := by
  simp [chainBlock, slice, h]
theorem length_nodeBlock (x : List Byte) (h : x.length = 64) : (nodeBlock x).length = 64 := by
  simp [nodeBlock, slice, h]
theorem length_digestBlock (x : List Byte) (h : x.length = 96) : (digestBlock x).length = 64 := by
  simp [digestBlock, slice, h]
theorem length_padTo64 (x : List Byte) : (padTo64 x).length = 64 * (padBlocks x.length + 1) := by
  simp only [padTo64, List.length_append, length_zeros, padBlocks]; omega
set_option exponentiation.threshold 600 in
theorem toList_fmt (x : List Byte) : toList (fmt x).2 = fmtList x := by
  have key : ∀ (l : List Byte) (hl : l.length = 64), toList (⟨0, ofList _ l⟩ : Query).2 = l :=
    fun l hl => toList_ofList _ _ hl
  by_cases h1 : IsChainFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_chain x h1)
    refine e.trans ((key _ (length_chainBlock x h1.1)).trans ?_)
    unfold fmtList; rw [if_pos h1]
  by_cases h2 : IsNodeFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_node x h2)
    refine e.trans ((key _ (length_nodeBlock x h2.1)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_pos h2]
  by_cases h3 : IsDigestFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_digest x h3)
    refine e.trans ((key _ (length_digestBlock x h3.1)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_neg h2, if_pos h3]
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_plain x h1 h2 h3)
    refine e.trans ((toList_ofList _ _ (length_padTo64 x)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_neg h2, if_neg h3]
theorem getD_fmtList (x : List Byte) (i : Nat) (hi : i < 4 ∨ (8 ≤ i ∧ i < 12)) :
    (fmtList x).getD i 0 = x.getD i 0 := by
  unfold fmtList
  split_ifs with h1 h2 h3
  · unfold chainBlock slice
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rcases hi with hi | hi
    · rw [List.getElem?_append_left (by simp [h1.1]; omega), List.getElem?_take_of_lt hi]
    · rw [List.getElem?_append_right (by simp [h1.1]; omega),
        List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp [h1.1]; omega),
        List.getElem?_take_of_lt (by simp [h1.1]; omega), List.getElem?_drop]
      simp only [List.length_take, length_le32, h1.1]
      congr 2; omega
  · unfold nodeBlock slice
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rcases hi with hi | hi
    · rw [List.getElem?_append_left (by simp [h2.1]; omega), List.getElem?_take_of_lt hi]
    · rw [List.getElem?_append_right (by simp [h2.1]; omega),
        List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp [h2.1]; omega),
        List.getElem?_take_of_lt (by simp [h2.1]; omega), List.getElem?_drop]
      simp only [List.length_take, length_le32, h2.1]
      congr 2; omega
  · unfold digestBlock
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_left (by simp [h3.1]; omega), List.getElem?_take_of_lt (by omega)]
  · unfold padTo64
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, zeros]
    split
    · rfl
    · rename_i h
      simp
      rw [List.getElem?_eq_none (l := x) (by omega), List.getElem?_replicate]
      split <;> rfl
theorem getD_toList_fmt (x : List Byte) (i : Nat) (hi : i < 4 ∨ (8 ≤ i ∧ i < 12)) :
    (toList (fmt x).2).getD i 0 = x.getD i 0 := by
  rw [toList_fmt, getD_fmtList x i hi]
theorem blocks_fmt (x : List Byte) (h : ¬ IsDigestFmt x) : (fmt x).blocks = (pad64 x).blocks := by
  by_cases h1 : IsChainFmt x
  · rw [fmt_of_chain x h1]; show 0 + 1 = padBlocks x.length + 1; rw [h1.1]; rfl
  by_cases h2 : IsNodeFmt x
  · rw [fmt_of_node x h2]; show 0 + 1 = padBlocks x.length + 1; rw [h2.1]; rfl
  rw [fmt_of_plain x h1 h2 h]
theorem blocks_fmt_digest (x : List Byte) (h : IsDigestFmt x) : (fmt x).blocks = 1 := by
  rw [fmt_of_digest x h]; rfl
theorem blocks_fmt_le (x : List Byte) : (fmt x).blocks ≤ (pad64 x).blocks := by
  by_cases h : IsDigestFmt x
  · rw [blocks_fmt_digest x h]; show 1 ≤ padBlocks x.length + 1; omega
  · rw [blocks_fmt x h]
theorem height_values : (List.range nLayers).map height = [11, 6, 6, 6, 5] := by decide
theorem shiftBelow_values :
    (List.range nLayers).map shiftBelow = [23, 17, 11, 5, 0] := by decide
theorem topH_eq : topH = 11 := rfl
theorem topN_values : (List.range (topH + 1)).map topN =
    [0, 2048, 3072, 3584, 3840, 3968, 4032, 4064, 4080, 4088, 4092, 4094] := by decide
theorem regionBytes_eq : regionBytes = 65504 := by decide
theorem porsT_eq : porsT = 16384 := rfl
theorem porsSegs_eq : porsSegs = 29 := rfl
theorem headBytes_eq : headBytes = 2144 := rfl
theorem sigLayerOff_values :
    (List.range (nLayers + 1)).map sigLayerOff = [2144, 2992, 3760, 4528, 5296, 6048] := by
  decide
theorem bodyBytes_eq (lay : Nat) : bodyBytes lay = sigLayerBytes lay - 4 := by
  simp only [bodyBytes, sigLayerBytes]; omega
theorem witLayerOff_eq_sig (lay : Nat) (h : lay ≤ nLayers) : witLayerOff lay = sigLayerOff lay + 280 := by
  simp only [nLayers] at h
  interval_cases lay <;> decide
theorem sigBytes_eq_sigLayerOff : sigBytes = sigLayerOff nLayers := by decide
theorem wStream_eq : wStream = 272 := rfl
theorem streamBytes_eq : streamBytes = 2152 := rfl
theorem wLayers_eq : wLayers = 2424 := rfl
theorem witLayerOff_values :
    (List.range (nLayers + 1)).map witLayerOff = [2424, 3272, 4040, 4808, 5576, 6328] := by
  decide
theorem witCounters_eq : witCounters = 6328 := by decide
theorem witBytes_eq : witBytes = witCounters + 4 * nLayers := by decide
private theorem length_slice (l : List Byte) (off len : Nat) (h : off + len ≤ l.length) :
    (slice l off len).length = len := by
  simp [slice]; omega
private theorem length_flatten_map_range (n k : Nat) (f : Nat → List Byte)
    (hf : ∀ i, i < n → (f i).length = k) : ((List.range n).map f).flatten.length = n * k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      ih (fun i hi => hf i (by omega))]
    simp [hf n (by omega)]; ring
private theorem length_flatten_map_range' (n : Nat) (f : Nat → List Byte) (g : Nat → Nat)
    (hf : ∀ i, i < n → (f i).length = g i) :
    ((List.range n).map f).flatten.length = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      ih (fun i hi => hf i (by omega))]
    simp [hf n (by omega)]
theorem length_witnessList (sig : List Byte) (hsig : sig.length = sigBytes) (v vs segs : List Nat)
    (hvs : vs.length = porsK) : (witnessList sig v vs segs).length = witBytes := by
  have hs : sig.length = 6048 := hsig
  have hoff : ∀ lay, lay < nLayers → sigLayerOff lay + bodyBytes lay ≤ 6048 := by decide
  have hitem : ∀ i, i < porsK → (sigItem sig i).length = 16 := fun i hi =>
    length_slice _ _ _ (by rw [hs]; unfold porsK at hi; omega)
  have hbody : ∀ lay, lay < nLayers → (sigLayerBody sig lay).length = bodyBytes lay :=
    fun lay hl => length_slice _ _ _ (by have := hoff lay hl; rw [hs]; omega)
  unfold witnessList witnessBody
  simp only [List.length_append, List.length_map, List.length_take, length_zeros, hvs,
    length_flatten_map_range _ _ _ hitem, length_flatten_map_range' _ _ _ hbody]
  rw [show (sigRho sig).length = 16 from length_slice _ _ _ (by rw [hs]; decide)]
  have : ((List.range nLayers).map bodyBytes).sum = 3904 := by decide
  rw [this]
  have : min streamBytes ((segStream sig segs).length + streamBytes) = streamBytes := by omega
  rw [this]
  decide
theorem length_of_expandOf (sig : List Byte) (hsig : sig.length = sigBytes) (N : Nat)
    (w : List Byte) (h : expandOf sig N = some w) : w.length = witBytes := by
  unfold expandOf at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  exact length_witnessList _ hsig _ _ _ (by simp [sortLeaves, leavesOf, porsK])
end SigGolfCandidate.Ref
end

section

end

section


namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.Ref
abbrev RCache := QueryCache HashSpec
abbrev qry (q : Query) : OracleComp HashSpec (BitVec 256) :=
  liftM (OracleSpec.query (spec := HashSpec) q)
noncomputable def roRun {α : Type} (oa : OracleComp HashSpec α) (c : RCache) :
    ProbComp (α × RCache) :=
  (simulateQ randomOracle oa).run c
theorem roRun_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (c : RCache) : roRun (oa >>= f) c = roRun oa c >>= fun x => roRun (f x.1) x.2 := by
  simp only [roRun, simulateQ_bind, StateT.run_bind]
theorem roRun_map {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache) :
    roRun (g <$> oa) c = (fun x => (g x.1, x.2)) <$> roRun oa c := by
  simp only [roRun, simulateQ_map, StateT.run_map]
@[simp] theorem roRun_pure {α : Type} (a : α) (c : RCache) :
    roRun (pure a : OracleComp HashSpec α) c = pure (a, c) := by
  simp [roRun]
theorem roRun_qry (q : Query) (c : RCache) :
    roRun (qry q) c = (randomOracle q).run c := by
  simp [roRun, qry]
theorem mem_support_roRun_of_count {α : Type} (wt : Query → Nat) (oa : OracleComp HashSpec α)
    (c : RCache) (x : (α × Nat) × RCache) (hx : x ∈ support (roRun (countWith wt oa) c)) :
    (x.1.1, x.2) ∈ support (roRun oa c) := by
  have h : roRun oa c = (fun x => (x.1.1, x.2)) <$> roRun (countWith wt oa) c := by
    conv_lhs => rw [← fst_countWith wt oa]
    rw [roRun_map]
  rw [h, support_map]
  exact ⟨x, hx, rfl⟩
theorem ev_const_mul {γ : Type} (mx : ProbComp γ) (g : γ → ℝ≥0∞) (a : ℝ≥0∞) :
    expectedValue mx (fun x => a * g x) = a * expectedValue mx g := by
  simp only [mul_comm a]
  exact expectedValue_mul_const mx g a
noncomputable def V (z : ℝ≥0∞) {α : Type} (oa : OracleComp HashSpec α) (c : RCache) : ℝ≥0∞ :=
  expectedValue (roRun (countBlocks oa) c) (fun x => z ^ x.1.2)
@[simp] theorem V_pure (z : ℝ≥0∞) {α : Type} (a : α) (c : RCache) :
    V z (pure a : OracleComp HashSpec α) c = 1 := by
  simp [V, countBlocks]
theorem V_bind_eq (z : ℝ≥0∞) {α β : Type} (oa : OracleComp HashSpec α)
    (f : α → OracleComp HashSpec β) (c : RCache) :
    V z (oa >>= f) c = expectedValue (roRun (countBlocks oa) c)
      (fun x => z ^ x.1.2 * V z (f x.1.1) x.2) := by
  unfold V countBlocks
  rw [countWith_bind, roRun_bind, expectedValue_bind]
  congr 1; funext x
  rw [roRun_map, expectedValue_map]
  simp only [pow_add]
  exact ev_const_mul _ _ _
theorem V_bind_le (z : ℝ≥0∞) {α β : Type} (oa : OracleComp HashSpec α)
    (f : α → OracleComp HashSpec β) (c : RCache) (b : ℝ≥0∞)
    (h : ∀ x ∈ support (roRun oa c), V z (f x.1) x.2 ≤ b) :
    V z (oa >>= f) c ≤ V z oa c * b := by
  rw [V_bind_eq]
  unfold V
  rw [← expectedValue_mul_const]
  refine expectedValue_mono_of_support fun x hx => ?_
  have := h (x.1.1, x.2) (mem_support_roRun_of_count _ oa c x hx)
  exact mul_le_mul' le_rfl this
theorem V_map (z : ℝ≥0∞) {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache) :
    V z (g <$> oa) c = V z oa c := by
  rw [map_eq_bind_pure_comp, V_bind_eq, V]
  simp
theorem V_map_le (z : ℝ≥0∞) {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache)
    (b : ℝ≥0∞) (h : V z oa c ≤ b) : V z (g <$> oa) c ≤ b := by
  rwa [V_map]
theorem V_query (z : ℝ≥0∞) {α : Type} (q : Query) (f : BitVec 256 → OracleComp HashSpec α)
    (c : RCache) :
    V z (qry q >>= f) c =
      z ^ q.blocks * expectedValue ((randomOracle q).run c) (fun y => V z (f y.1) y.2) := by
  rw [V_bind_eq]
  unfold countBlocks
  rw [countWith_query, roRun_map, expectedValue_map, roRun_qry]
  exact ev_const_mul ((randomOracle q).run c) (fun y => V z (f y.1) y.2) (z ^ q.blocks)
theorem expectedValue_ro_fresh (q : Query) (c : RCache) (hq : c q = none)
    (g : BitVec 256 × RCache → ℝ≥0∞) :
    expectedValue ((randomOracle q).run c) g =
      expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (fun u => g (u, c.cacheQuery q u)) := by
  rw [randomOracle.run_eq, hq]
  simp only
  rw [expectedValue_bind]
  simp
theorem expectedValue_ro_cached (q : Query) (c : RCache) (u : BitVec 256) (hq : c q = some u)
    (g : BitVec 256 × RCache → ℝ≥0∞) :
    expectedValue ((randomOracle q).run c) g = g (u, c) := by
  rw [randomOracle.run_eq, hq]
  simp
theorem mem_support_ro (q : Query) (c : RCache) (y : BitVec 256 × RCache)
    (hy : y ∈ support ((randomOracle q).run c)) :
    (c q = some y.1 ∧ y.2 = c) ∨ (c q = none ∧ y.2 = c.cacheQuery q y.1) := by
  rw [randomOracle.run_eq] at hy
  cases hq : c q with
  | some u =>
    rw [hq] at hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    left; exact ⟨rfl, rfl⟩
  | none =>
    rw [hq] at hy
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hy
    obtain ⟨u, _, rfl⟩ := hy
    right; exact ⟨rfl, rfl⟩
inductive Spec (P : Query → Prop) {α : Type} (Post : α → Prop) :
    Nat → OracleComp HashSpec α → Prop
  | pure (a : α) (k : Nat) : Post a → Spec P Post k (pure a)
  | query (q : Query) (f : BitVec 256 → OracleComp HashSpec α) (k : Nat) :
      P q → (∀ u, Spec P Post k (f u)) → Spec P Post (q.blocks + k) (qry q >>= f)
namespace Spec
variable {P : Query → Prop} {α β : Type}
theorem mono_k {Post : α → Prop} {k k' : Nat} {oa : OracleComp HashSpec α}
    (h : Spec P Post k oa) (hk : k ≤ k') : Spec P Post k' oa := by
  induction h generalizing k' with
  | pure a k hp => exact .pure a k' hp
  | query q f k hq _ ih =>
    have : k' = q.blocks + (k' - q.blocks) := by omega
    rw [this]
    exact .query q f _ hq fun u => ih u (by omega)
theorem mono {P' : Query → Prop} {Post Post' : α → Prop} {k : Nat} {oa : OracleComp HashSpec α}
    (h : Spec P Post k oa) (hP : ∀ q, P q → P' q) (hQ : ∀ a, Post a → Post' a) :
    Spec P' Post' k oa := by
  induction h with
  | pure a k hp => exact .pure a k (hQ a hp)
  | query q f k hq _ ih => exact .query q f k (hP q hq) ih
theorem bind {Q : α → Prop} {R : β → Prop} {k l : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} (h : Spec P Q k oa) (hf : ∀ a, Q a → Spec P R l (f a)) :
    Spec P R (k + l) (oa >>= f) := by
  induction h with
  | pure a k hp => rw [pure_bind]; exact (hf a hp).mono_k (by omega)
  | query q g k hq _ ih =>
    rw [bind_assoc, Nat.add_assoc]
    exact .query q _ _ hq ih
theorem bind' {Q : α → Prop} {R : β → Prop} {k l n : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} (h : Spec P Q k oa) (hf : ∀ a, Q a → Spec P R l (f a))
    (hn : k + l ≤ n) : Spec P R n (oa >>= f) :=
  (h.bind hf).mono_k hn
theorem map {Q : α → Prop} {R : β → Prop} {k : Nat} {oa : OracleComp HashSpec α} (g : α → β)
    (h : Spec P Q k oa) (hg : ∀ a, Q a → R (g a)) : Spec P R k (g <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact (h.bind (l := 0) fun a ha => .pure _ 0 (hg a ha))
theorem qry_bind {R : β → Prop} {q : Query} {f : BitVec 256 → OracleComp HashSpec β} {k n : Nat}
    (hq : P q) (hf : ∀ u, Spec P R k (f u)) (hn : q.blocks + k ≤ n) :
    Spec P R n (qry q >>= f) :=
  (Spec.query q f k hq hf).mono_k hn
theorem V_le {Post : α → Prop} {k : Nat} {oa : OracleComp HashSpec α} (h : Spec P Post k oa)
    {z : ℝ≥0∞} (hz : 1 ≤ z) (c : RCache) : V z oa c ≤ z ^ k := by
  induction h generalizing c with
  | pure a k _ => rw [V_pure]; exact one_le_pow₀ hz
  | query q f k _ _ ih =>
    rw [V_query, pow_add]
    exact mul_le_mul' le_rfl (expectedValue_le_of_le _ fun y => ih y.1 y.2)
def _root_.SigGolfCandidate.Budget.CacheInv (I : Query → Prop) (c : RCache) : Prop :=
  ∀ q u, c q = some u → I q
theorem support {Post : α → Prop} {k : Nat} {oa : OracleComp HashSpec α} (h : Spec P Post k oa)
    {I : Query → Prop} (hPI : ∀ q, P q → I q) (c : RCache) (hc : CacheInv I c)
    (x : α × RCache) (hx : x ∈ support (roRun oa c)) : Post x.1 ∧ CacheInv I x.2 := by
  induction h generalizing c with
  | pure a k hp =>
    rw [roRun_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨hp, hc⟩
  | query q f k hq _ ih =>
    rw [roRun_bind, support_bind] at hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [roRun_qry] at hy
    refine ih y.1 y.2 ?_ hx
    rcases mem_support_ro q c y hy with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]; exact hc
    · rw [h2]
      intro q' u hq'
      by_cases hqq : q' = q
      · subst hqq; exact hPI _ hq
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hq'
        exact hc q' u hq'
end Spec
theorem CacheInv.mono {I I' : Query → Prop} {c : RCache} (h : CacheInv I c)
    (hI : ∀ q, I q → I' q) : CacheInv I' c := fun q u hq => hI q (h q u hq)
end SigGolfCandidate.Budget
end

section

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref
def qbyte (q : Query) (i : Nat) : Nat := q.2.toNat / 256 ^ i % 256
theorem length_padTo64 (x : List Byte) : (padTo64 x).length = 64 * (padBlocks x.length + 1) := by
  unfold padTo64 padBlocks
  simp only [List.length_append, length_zeros]
  omega
theorem getD_padTo64 (x : List Byte) (i : Nat) : (padTo64 x).getD i 0 = x.getD i 0 := by
  unfold padTo64 zeros
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < x.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := x) (by omega),
      List.getElem?_replicate]
    split <;> rfl
theorem qbyte_pad64 (x : List Byte) (i : Nat) : qbyte (pad64 x) i = (x.getD i 0).toNat := by
  unfold qbyte pad64 ofList
  simp only [BitVec.toNat_ofNat]
  have hlt := leNat_lt (padTo64 x)
  rw [length_padTo64] at hlt
  have h2 : (2 : Nat) ^ (8 * (64 * (padBlocks x.length + 1))) = 256 ^ (64 * (padBlocks x.length + 1)) := by
    rw [Nat.pow_mul]
  rw [h2, Nat.mod_eq_of_lt hlt, leNat_div_mod, getD_padTo64]
theorem getD_eq_of_pad64_eq {x y : List Byte} (e : pad64 x = pad64 y) (i : Nat) :
    x.getD i 0 = y.getD i 0 := by
  have h := congrArg (fun q => qbyte q i) e
  simp only [qbyte_pad64] at h
  exact BitVec.eq_of_toNat_eq h
theorem pad64_inj {x y : List Byte} (h : x.length = y.length) (e : pad64 x = pad64 y) : x = y := by
  apply List.ext_getElem h
  intro i h1 h2
  have := getD_eq_of_pad64_eq e i
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this
theorem blocks_pad64 (x : List Byte) : (pad64 x).blocks = padBlocks x.length + 1 := rfl
theorem blocks_pad64_le (x : List Byte) (k : Nat) (h : x.length ≤ 64 * k) (hk : 1 ≤ k) :
    (pad64 x).blocks ≤ k := by
  rw [blocks_pad64]; unfold padBlocks; omega
theorem blocksFmt_le (x : List Byte) (k : Nat) (h : x.length ≤ 64 * k) (hk : 1 ≤ k) :
    (fmt x).blocks ≤ k :=
  (Ref.blocks_fmt_le x).trans (blocks_pad64_le x k h hk)
theorem qbyte_fmt (x : List Byte) (i : Nat) (hi : i < 4) : qbyte (fmt x) i = (x.getD i 0).toNat := by
  unfold qbyte
  rw [← leNat_toList, leNat_div_mod, getD_toList_fmt x i (Or.inl hi)]
theorem fmt_eq_pad64 (t lay tau p j : Nat) (pl : List Byte)
    (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 12) :
    fmt (thInput (tweak t lay tau p j) pl) = pad64 (thInput (tweak t lay tau p j) pl) := by
  refine fmt_thInput _ _ _ _ _ _ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have := congrArg BitVec.toNat h <;>
    simp [byte_toNat] at this <;> omega
theorem qbyte_tag (t lay tau p j : Nat) (pl : List Byte) :
    qbyte (fmt (thInput (tweak t lay tau p j) pl)) 1 = t % 256 := by
  rw [qbyte_fmt _ _ (by omega)]; simp [thInput, tweak, byte_toNat]
theorem qbyte_lay (t lay tau p j : Nat) (pl : List Byte) :
    qbyte (fmt (thInput (tweak t lay tau p j) pl)) 2 = lay % 256 := by
  rw [qbyte_fmt _ _ (by omega)]; simp [thInput, tweak, byte_toNat]
theorem leNat_leBytes (k v : Nat) : leNat (leBytes k v) = v % 256 ^ k := leNat_map_range k v
theorem le32_inj {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32) (h : le32 c = le32 c') :
    c = c' := by
  have := congrArg leNat h
  simp only [le32, leNat_leBytes] at this
  rw [Nat.mod_eq_of_lt (by simpa using hc), Nat.mod_eq_of_lt (by simpa using hc')] at this
  exact this
theorem tweak_p_inj {t lay tau p j t' lay' tau' p' j' : Nat} (hp : p < 2 ^ 32) (hp' : p' < 2 ^ 32)
    (h : tweak t lay tau p j = tweak t' lay' tau' p' j') : p = p' := by
  unfold tweak at h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨-, -, -, -, h⟩ := h
  have h2 := List.append_inj_left' (List.append_inj_left' h (by simp)) (by simp)
  exact le32_inj hp hp' (List.append_inj_left' h2 (by simp))
theorem getD_len_le {l : List (List Byte)} {n : Nat} (h : ∀ v ∈ l, v.length ≤ n) (i : Nat) :
    (l.getD i []).length ≤ n := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some v => exact h v (List.mem_of_getElem? hi)
theorem length_flatten_le {l : List (List Byte)} {n : Nat} (h : ∀ v ∈ l, v.length ≤ n) :
    l.flatten.length ≤ n * l.length := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have h1 := h v (by simp)
    have h2 := ih (fun w hw => h w (by simp [hw]))
    rw [Nat.mul_succ]; omega
end SigGolfCandidate.Budget
end
