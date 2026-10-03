import SigGolfCandidate.T3.Secc.LargeResidualT3
import SigGolfCandidate.T3.Secc.WotsExtractWord
import SigGolfCandidate.T3.Secc.CaseCSearch

/-!
# LR-34 (router): the padded game as a residual-world program

The router runs the adversary against the residual world (`LargeResidual.World`), replacing honest key generation
and honest signing by **disclosures** and routing every adversary/verifier public query exactly as the contact test
of the monitor (`ContactTest`):

* parsed source position `N`: if a child is unknown, a probe guessing the first unknown child (its slot of the input)
  with the label hit of `N`; if all children are known, disclose them; the honest cell is answered by disclosing `N`
  (and the presampled high half), any other input by a probe with the label hit of `N`;
* encoding row of a route leaf `L`: if `L`'s honest message is unknown, a probe guessing it with the reference-digest
  hit; if known, the reference rows up to the selected counter come from the presampled rows (`tick`), others are
  probes with the reference-digest hit;
* digest rows: reads with one unit of mass; everything else: reads (or a tick outside the universe).

A repeated input is never tested again (`read`, the row is cached). The router stops spending at the budget: before
a charged query with `calls ≥ q` it ends (no stop). Honest signing reads the digest rows (uncharged reads), checks
the presampled route selections, and discloses `signItemsWith routerDigits` — exactly what the signature reveals.

Auxiliary data (`AuxData`, sampled once by the `init` query): the label high halves, the honest-message encoding rows
of every route leaf (their first success is the presampled selection, G §6), and a private table for the cache MAC and
the masks. Signing nonces are hidden world coordinates (`WCoord = Coord ⊕ Message`), sampled lazily at the first
signing of their message (a disclosure), so that a fresh nonce is uniform at signing time (CC-1).
-/

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeResidualRouter : DecidableEq T3.Cache := Classical.decEq _

/-! ## Auxiliary spec -/

/-- Auxiliary queries of the router: the adversary's coins, and one initial presampled datum. -/
inductive AuxQuery where
  | coin (n : Nat)
  | init

/-- The presampled data: label high halves, the encoding rows of every route leaf at its honest message (all
`2^22` counters; only the first-success prefix is used), a private table (nonces, cache MAC, masks). -/
structure AuxData where
  high : CanonGraph.Node → Digest
  rows : EncLeaf → Fin (2 ^ 22) → HashOutput
  priv : FullGame.FullTable

/-- The presampled encoding selections: the first success of each leaf's rows. -/
noncomputable def AuxData.sel (a : AuxData) : Selections := fun L =>
  SphincsSecurity.Concrete.FirstSuccessTable.select (decodeAt L) (a.rows L)

/-- Answer types of the auxiliary queries. -/
abbrev AuxSpec : OracleSpec AuxQuery
  | .coin n => Fin (n + 1)
  | .init => AuxData

/-- The auxiliary laws: uniform coins, a given law of the presampled data. -/
noncomputable def auxLaw (initLaw : PMF AuxData) : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)
  | .coin n => PMF.uniformOfFintype (Fin (n + 1))
  | .init => initLaw

/-- The residual cells: the eager public universe. -/
abbrev Cell (U : Finset HashInput) := {x // x ∈ U}

/-- The world's hidden coordinates: the canonical label/secret coordinates and the signing nonces (lazily sampled at
the first signing of a message: a disclosure). -/
abbrev WCoord := Coord ⊕ Message

/-- The router's world. -/
abbrev RWorld (U : Finset HashInput) := World AuxSpec WCoord (Cell U)

section Requests
variable (U : Finset HashInput)

def coinReq (n : Nat) : OracleComp (RWorld U) (Fin (n + 1)) := liftM ((RWorld U).query (.inl (.coin n)))
def initReq : OracleComp (RWorld U) AuxData := liftM ((RWorld U).query (.inl .init))
def readReq (row : Cell U) (charge : Charge) : OracleComp (RWorld U) HashOutput :=
  liftM ((RWorld U).query (.inr (.read row charge)))
def probeReq (row : Cell U) (test : Probe WCoord) : OracleComp (RWorld U) HashOutput :=
  liftM ((RWorld U).query (.inr (.probe row test)))
def discloseReq (c : WCoord) (charge : Charge) : OracleComp (RWorld U) Digest :=
  liftM ((RWorld U).query (.inr (.disclose c charge)))
def tickReq (charge : Charge) : OracleComp (RWorld U) Unit := liftM ((RWorld U).query (.inr (.tick charge)))

/-- Disclose a list of coordinates (uncharged), keeping the values. -/
def discloseAll : List Coord → OracleComp (RWorld U) (List (Coord × Digest))
  | [] => pure []
  | c :: rest => do
      let v ← discloseReq U (.inl c) .none
      let tail ← discloseAll rest
      pure ((c, v) :: tail)

end Requests

/-- Look up a disclosed value (`0` if absent). -/
def lookupVal (pairs : List (Coord × Digest)) (c : Coord) : Digest :=
  ((pairs.find? fun p => decide (p.1 = c)).map Prod.snd).getD 0

/-! ## Router data -/

/-- The router's own state: disclosures (signatures), adversary/verifier inputs seen, charged calls, and the
case-C bank ghost (CC-1, CC's macro steps `core_birth`/`core_sign`): the honest digest trial rows read, the **births**
(inputs and answers of fresh adversary/verifier digest rows, all within the budget; they are also the ghost cache of
the reuse test), the **exposures** (selected digest outputs of fresh signings outside the reuse event), the **reuse**
flag (CC's `Reuse`: at a fresh signing some cached trial row of the nonce and message is admissible), and the digest
search result of every signed message (repeated signings of a message are deterministic: memoized). -/
structure RouterState where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  trials : List HashInput
  births : List (HashInput × HashOutput)
  exposures : List HashOutput
  reused : Bool
  memo : List (Message × Option (BitVec 32 × HashOutput))

def RouterState.initial : RouterState := ⟨[], [], 0, [], [], [], false, []⟩

/-- The router state after one adversary/verifier query. -/
def RouterState.after (st : RouterState) (X : HashInput) : RouterState :=
  { st with seen := X :: st.seen, calls := st.calls + 1 }

/-- A public row never read before (neither by the adversary/verifier nor by an honest search). -/
def RouterState.Fresh (st : RouterState) (X : HashInput) : Prop := X ∉ st.seen ∧ X ∉ st.trials

/-- The router state after an adversary/verifier query of `X` answered `y` (a fresh digest row of `U` is a birth). -/
noncomputable def RouterState.next (U : Finset HashInput) (st : RouterState) (X : HashInput) (y : HashOutput) :
    RouterState :=
  if X ∈ U ∧ IsDigestRow X ∧ st.Fresh X then { st.after X with births := (X, y) :: st.births } else st.after X

/-- The adversary's knowledge in a router state (as the monitor's). -/
def RouterState.known (st : RouterState) : Coord → Prop :=
  Known fun c => c ∈ keygenDisclosed ∨ c ∈ st.disclosed

/-- The honest cell of a node from the values of its children. -/
noncomputable def cellFrom (N : CanonGraph.Node) (v : Coord → Digest) : HashInput :=
  cell (fun s => v (.inr s)) N (joinLabels (fun M => v (.inl M)) fun _ => 0)

/-- The digest of the dummy word. -/
noncomputable def dummyDigest (lay : Layer) : Digest := Classical.choose (Wots.dummyDigits_valid lay)

/-- The presampled reference digest of a route leaf. -/
noncomputable def refDigest (a : AuxData) (L : EncLeaf) : Digest :=
  match a.sel L with
  | some r => r.2
  | none => dummyDigest L.1.lay

/-- An encoding counter inside the presampled first-success prefix (rows up to the selected counter; all rows if
the search fails). -/
def PrefixRow (a : AuxData) (L : EncLeaf) (ctr : BitVec 32) : Prop :=
  ctr.toNat < 2 ^ 22 ∧ ∀ r, a.sel L = some r → ctr.toNat ≤ r.1.val

/-- The presampled row at a counter (`0` outside the family). -/
def prefixValue (a : AuxData) (L : EncLeaf) (ctr : BitVec 32) : HashOutput :=
  if h : ctr.toNat < 2 ^ 22 then a.rows L ⟨ctr.toNat, h⟩ else 0

/-- The router's reference digits of a W leaf (presampled selection at route leaves, the dummy word otherwise). -/
noncomputable def routerDigits (a : AuxData) (L : Wots.LeafAddr) : List Nat :=
  if h : ∃ L' : EncLeaf, L'.toWots = L then
    ((a.sel (Classical.choose h)).bind fun r => decode L.lay r.2).getD (Wots.dummyDigits L.lay)
  else Wots.dummyDigits L.lay

/-- Every route encoding search succeeds (presampled selections). -/
def RouteOkR (a : AuxData) (index : Nat) : Prop :=
  ∀ lay : Layer, ∃ (L : EncLeaf) (r : Fin (2 ^ 22) × Digest),
    L.toWots = routeAddr index lay ∧ a.sel L = some r ∧ (decode lay r.2).isSome

/-- Mask of the cached top tree. -/
def maskOf (a : AuxData) (level node : Nat) : Digest :=
  let answer := a.priv (.inl (header 13 0 0 level (node/2)))
  if node%2=0 then answer.extractLsb' 0 128 else answer.extractLsb' 128 128

/-- Four-lane polynomial tag from the same two private key answers as the source. -/
def macOf (a : AuxData) (region : Region) : HashOutput :=
  SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag
    (fun i => a.priv (.inl (header 14 0 0 0 i.val))) (List.ofFn region))

/-- The router's top-tree value at `(level, node)` from disclosed values. -/
def topValue (v : Coord → Digest) (level node : Nat) : Digest :=
  ((treeChild 0 0 level node).map v).getD 0

/-! ## Classification of public inputs -/

/-- An encoding row of a route leaf. -/
def EncRow (X : HashInput) : Prop :=
  ∃ (L : EncLeaf) (m : (Digest × BitVec 96 × Digest)) (ctr : BitVec 32), X = Wots.encodingRow L.toWots m ctr

/-- A parsed source position. -/
def Parsed (X : HashInput) : Prop := ∃ N : CanonGraph.Node, Extract.posOf X = some N.toPos

/-! ## One adversary/verifier query -/

section Route
variable (U : Finset HashInput)

/-- Route a fresh-or-repeated test: a probe at the first occurrence, a read afterwards. -/
def testReq (first : Bool) (row : Cell U) (test : Probe WCoord) : OracleComp (RWorld U) HashOutput :=
  if first then probeReq U row test else readReq U row .call

/-- **Route one adversary/verifier public query** (one charged request). -/
noncomputable def routeQuery (a : AuxData) (st : RouterState) (X : HashInput) :
    OracleComp (RWorld U) (HashOutput × RouterState) :=
  let st' : RouterState := st.after X
  let first : Bool := decide (X ∉ st.seen)
  if h : X ∈ U then
    if hp : Parsed X then
      let N := Classical.choose hp
      match firstUnknown st.known N with
      | some cs => (fun y => (y, st')) <$>
          testReq U first ⟨X, h⟩ ⟨some (.inl cs.1, slotValue X cs.2), .label (.inl (.inl N))⟩
      | none => do
          let pairs ← discloseAll U ((childSlots N).map Prod.fst)
          if X = cellFrom N (lookupVal pairs) then do
            let v ← discloseReq U (.inl (.inl N)) .call
            pure (ChainGraph.joinOutput v (a.high N), st')
          else (fun y => (y, st')) <$> testReq U first ⟨X, h⟩ ⟨none, .label (.inl (.inl N))⟩
    else if he : EncRow X then
      let L := Classical.choose he
      let m := Classical.choose (Classical.choose_spec he)
      let ctr := Classical.choose (Classical.choose_spec (Classical.choose_spec he))
      match firstUnknownMsg st.known L with
      | some p => (fun y => (y, st')) <$>
          testReq U first ⟨X, h⟩ ⟨some (.inl p.1, p.2 m), .target (refDigest a L)⟩
      | none => do
          let pairs ← discloseAll U (msgCoords L)
          if m = msgOf L (lookupVal pairs) ∧ PrefixRow a L ctr then do
            tickReq U .call
            pure (prefixValue a L ctr, st')
          else (fun y => (y, st')) <$> testReq U first ⟨X, h⟩ ⟨none, .target (refDigest a L)⟩
    else if IsDigestRow X then
      (fun y => (y, if st.Fresh X then { st' with births := (X, y) :: st.births } else st')) <$> readReq U ⟨X, h⟩ .mass
    else (fun y => (y, st')) <$> readReq U ⟨X, h⟩ .call
  else do
    tickReq U .call
    pure (0, st')

/-- Answer honest public reads (digest search) from the residual table, uncharged. -/
noncomputable def readImpl (a : AuxData) : QueryImpl T3.Spec (OracleComp (RWorld U))
  | .inl (.inl n) => coinReq U n
  | .inl (.inr X) => if h : X ∈ U then readReq U ⟨X, h⟩ .none else pure (0 : HashOutput)
  | .inr c => pure (a.priv c)

/-- The router's signature from disclosed values. -/
def assembleSig (rho : Digest) (N : HashOutput) (v : Coord → Digest) (digitsOf : Wots.LeafAddr → List Nat) :
    Signature :=
  let index := digestIndex N
  let chosen := selections N
  ⟨rho,
    fun i => (((List.range 7).flatMap fun c => ftsOpened index c (chosen.getD c ⟨0, []⟩)).map v).getD i.val 0,
    fun i => (((List.range 7).flatMap fun c => ftsProof index c (chosen.getD c ⟨0, []⟩)).map v).getD i.val 0,
    fun lay => piecesSignature lay ((layerChains digitsOf index lay).map v, (layerPath index lay).map v)⟩

/-- The digest trial rows read by the honest search of `(rho, m)` with result `found`. -/
def trialRows (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : List HashInput :=
  (List.range (match found with | some (c, _) => c.toNat + 1 | none => attemptLimit)).map fun c =>
    pad64 (digestInput rho m (BitVec.ofNat 32 c))

/-- The ghost cache of the reuse test: the answers of the births. -/
def RouterState.cache (st : RouterState) : Sampling.RCache := fun X => st.births.lookup X

/-- The bank ghost after a fresh signing of `m` with nonce `rho` and search result `found` (CC's `core_sign`: the
reuse flag on `Reuse`, otherwise the selection, if any, is exposed). -/
noncomputable def RouterState.signed (st : RouterState) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) :
    RouterState :=
  if CaseC.Reuse st.cache rho m then
    { st with
      trials := st.trials ++ trialRows rho m found
      memo := (m, found) :: st.memo
      reused := true }
  else
    { st with
      trials := st.trials ++ trialRows rho m found
      memo := (m, found) :: st.memo
      exposures := st.exposures ++ (found.map Prod.snd).toList }

theorem RouterState.signed_fields (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (st.signed rho m found).disclosed = st.disclosed ∧ (st.signed rho m found).seen = st.seen ∧
      (st.signed rho m found).calls = st.calls ∧ (st.signed rho m found).births = st.births ∧
      (st.signed rho m found).trials = st.trials ++ trialRows rho m found ∧
      (st.signed rho m found).memo = (m, found) :: st.memo := by
  unfold RouterState.signed
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The end of a signing: disclose the signature's items (successful search, successful route searches). -/
noncomputable def signFinish (a : AuxData) (st : RouterState) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) : OracleComp (RWorld U) (Option Signature × RouterState) :=
  match found with
  | none => pure (none, st)
  | some (_, N) =>
      if RouteOkR a (N.toNat % 2 ^ 31) then do
        let items := signItemsWith (routerDigits a) N
        let pairs ← discloseAll U items
        pure (some (assembleSig rho N (lookupVal pairs) (routerDigits a)),
          { st with disclosed := st.disclosed ++ items })
      else pure (none, st)

/-- **Honest signing by disclosure.** The nonce is a hidden world coordinate (sampled at the first signing of the
message); the digest search reads the residual rows (uncharged); a repeated message reuses its search result. -/
noncomputable def routeSign (a : AuxData) (published : T3.Cache) (st : RouterState)
    (request : SigGolfCandidate.T3.Security.Request) : OracleComp (RWorld U) (Option Signature × RouterState) :=
  if request.cache = published then do
    let rho ← discloseReq U (.inr request.message) .none
    match st.memo.lookup request.message with
    | some found => signFinish U a st rho found
    | none => do
        let found ← simulateQ (readImpl U a) (digestSearch rho request.message 0 attemptLimit)
        signFinish U a (st.signed rho request.message found) rho found
  else pure (none, st)

/-- **The adversary's interaction, routed** (`none`: the budget was exhausted before a charged query). -/
noncomputable def routeInteraction (a : AuxData) (published : T3.Cache) (q : Nat) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    RouterState → OracleComp (RWorld U) (Option ((α × QueryLog Requests) × RouterState)) :=
  OracleComp.construct
    (fun value st => pure (some ((value, []), st)))
    (fun input _ next st => match input, next with
      | .inl (.inl n), next => do
          let c ← coinReq U n
          next c st
      | .inl (.inr X), next =>
          if q ≤ st.calls then pure none else do
            let r ← routeQuery U a st X
            next r.1 r.2
      | .inr request, next => do
          let s ← routeSign U a published st request
          let rest ← next s.1 s.2
          pure (rest.map fun res => ((res.1.1, ⟨request, s.1⟩ :: res.1.2), res.2)))
    program

/-- **The verdict, routed** (public queries only; private coordinates answered from the presampled table). -/
noncomputable def routeVerdict (a : AuxData) (q : Nat) {β : Type} (program : M β) :
    RouterState → OracleComp (RWorld U) (Option (β × RouterState)) :=
  OracleComp.construct
    (fun value st => pure (some (value, st)))
    (fun input _ next st => match input, next with
      | .inl (.inl n), next => do
          let c ← coinReq U n
          next c st
      | .inl (.inr X), next =>
          if q ≤ st.calls then pure none else do
            let r ← routeQuery U a st X
            next r.1 r.2
      | .inr c, next => next (a.priv c) st)
    program

/-- The router after the presampled data: disclose the key, run the adversary and the verdict. -/
noncomputable def routerWith (adversary : Final.AdversaryP) (q : Nat) (a : AuxData) :
    OracleComp (RWorld U) (Option (Bool × RouterState)) := do
  let pairs ← discloseAll U keygenDisclosed
  let v := lookupVal pairs
  let pk := v (.inl (.node (rootNode 0 0)))
  let region := Correctness.cacheRegion fun level node => topValue v level node ^^^ maskOf a level node
  let published : T3.Cache := ⟨macOf a region, region⟩
  let r ← routeInteraction U a published q (adversary pk published) RouterState.initial
  match r with
  | none => pure none
  | some (result, st) => routeVerdict U a q (GameWith.verdict PaddedGame.checker pk result) st

/-- **The router**: presample, disclose the key, run the adversary and the verdict. Its result is the verdict and
the final router state (`none` if the budget is exhausted first). -/
noncomputable def router (adversary : Final.AdversaryP) (q : Nat) : OracleComp (RWorld U) (Option (Bool × RouterState)) :=
  initReq U >>= routerWith U adversary q

end Route

end SigGolfCandidate.T3.Security.LargeResidual
