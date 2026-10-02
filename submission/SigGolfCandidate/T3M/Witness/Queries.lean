import SigGolfCandidate.T3M.Witness.Honest

/-! # Query shapes of the witness-layer programs (stream W)

`verifyP` and `expandN` (and so `expandB`) issue only **public** hash queries (no coins, no private coordinates),
each a nonempty 64-byte-aligned byte list (`Cost.GoodQuery`); `honestProgramB` and the machine pipeline's Core
programs issue only hash queries (`isHash`, CLOSURE's `SourceReplay.isHash`), every public one aligned. With M0's
`Aligned` and `privateInput`'s `pad64`, these give MACH-PLAN's `AllQ Aligned (hrealize sk …)`. -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

/-- A public hash query of a nonempty, 64-byte-aligned input. -/
def PubGood (q : Spec.Domain) : Prop := isPublic q ∧ Cost.GoodQuery q

/-- A hash query (no coins) whose public inputs are nonempty and aligned. -/
def HashGood (q : Spec.Domain) : Prop := isHash q ∧ Cost.GoodQuery q

theorem PubGood.hashGood {q : Spec.Domain} (h : PubGood q) : HashGood q := by
  obtain ⟨hp, hg⟩ := h
  rcases q with (n | input) | c
  · exact hp.elim
  · exact ⟨trivial, hg⟩
  · exact hp.elim

/-! ## Combinators -/

section comb
variable {P : Spec.Domain → Prop}

theorem allQ_pure {α : Type} (a : α) : AllQueriesSatisfy (pure a : M α) P := allQueriesSatisfy_pure _ _

theorem allQ_bind {α β : Type} {p : M α} {f : α → M β} (hp : AllQueriesSatisfy p P)
    (hf : ∀ a, AllQueriesSatisfy (f a) P) : AllQueriesSatisfy (p >>= f) P := allQueriesSatisfy_bind hp hf

theorem allQ_map {α β : Type} (f : α → β) {p : M α} (hp : AllQueriesSatisfy p P) :
    AllQueriesSatisfy (f <$> p) P := by
  rw [map_eq_bind_pure_comp]; exact allQ_bind hp fun _ => allQ_pure _

theorem allQ_ite {α : Type} (c : Prop) [Decidable c] {p q : M α} (hp : AllQueriesSatisfy p P)
    (hq : AllQueriesSatisfy q P) : AllQueriesSatisfy (if c then p else q) P := by
  split <;> assumption

theorem allQ_foldlM {α β : Type} (l : List β) (f : α → β → M α) (h : ∀ a b, AllQueriesSatisfy (f a b) P)
    (init : α) : AllQueriesSatisfy (l.foldlM f init) P := by
  induction l generalizing init with
  | nil => exact allQ_pure _
  | cons b l ih => rw [List.foldlM_cons]; exact allQ_bind (h init b) ih

theorem allQ_mapM {α β : Type} (l : List α) (f : α → M β) (h : ∀ a, AllQueriesSatisfy (f a) P) :
    AllQueriesSatisfy (l.mapM f) P := by
  induction l with
  | nil => exact allQ_pure _
  | cons a l ih => rw [List.mapM_cons]; exact allQ_bind (h a) fun _ => allQ_bind ih fun _ => allQ_pure _

end comb

theorem pubGood_publicHash (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (publicHash input) PubGood :=
  (allQueriesSatisfy_query_iff _ _).mpr ⟨trivial, Cost.pad64_positive input h, Cost.pad64_aligned input⟩

theorem pubGood_shortHash (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (shortHash input) PubGood := by
  unfold shortHash; exact allQ_bind (pubGood_publicHash input h) fun _ => allQ_pure _

/-! ## The primitives -/

theorem pubGood_ftsLeafP (index coord leaf : Nat) (p0 s p1 : Digest) :
    AllQueriesSatisfy (ftsLeafP index coord leaf p0 s p1) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])

theorem pubGood_nodeHashP (tag lay tree heap : Nat) (l p r : Digest) :
    AllQueriesSatisfy (nodeHashP tag lay tree heap l p r) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])

theorem pubGood_nodeHash (tag lay tree heap : Nat) (l r : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap l r) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])

theorem pubGood_ftsLeaf (index coord leaf : Nat) (s : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf s) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length, zero16])

theorem pubGood_chainP (lay : Layer) (tree leaf i start count : Nat) (p0 p1 v : Digest) :
    AllQueriesSatisfy (chainP lay tree leaf i start count p0 p1 v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [chainInputP, bytesLE_length])) _

theorem pubGood_chain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [chainInput, bytesLE_length, zero16])) _

theorem pubGood_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])

theorem pubGood_forestPk (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (forestPk index roots) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])

theorem pubGood_digest (rho : Digest) (m : Message) (c : BitVec 32) :
    AllQueriesSatisfy (digest rho m c) PubGood :=
  pubGood_publicHash _ (by simp [digestInput, bytesLE_length])

theorem pubGood_encoding (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    AllQueriesSatisfy (shortHash (encodingInput lay tree leaf msg c)) PubGood :=
  pubGood_shortHash _ (by simp [encodingInput, bytesLE_length])

/-! ## `verifyP` -/

theorem pubGood_pendingHash (w : WBytes) (index coord : Nat) (node : Digest) (pending : Pending) :
    AllQueriesSatisfy (pendingHash w index coord node pending) PubGood := by
  cases pending <;> unfold pendingHash
  · exact pubGood_ftsLeafP _ _ _ _ _ _
  · exact pubGood_nodeHash _ _ _ _ _ _

theorem pubGood_foldsP (w : WBytes) (index coord ptr a : Nat) (node : Digest) (E : Nat) :
    AllQueriesSatisfy (foldsP w index coord ptr a node E) PubGood := by
  unfold foldsP
  refine allQ_foldlM _ _ (fun st r => ?_) _
  unfold foldStep
  simp only []
  split <;> exact allQ_bind (pubGood_nodeHashP _ _ _ _ _ _ _) fun _ => allQ_pure _

theorem pubGood_segLoop (w : WBytes) (index coord : Nat) : ∀ (stack : List (Digest × Nat)) (pending : Pending)
    (E ptr : Nat) (node : Digest), AllQueriesSatisfy (segLoop w index coord stack pending E ptr node) PubGood := by
  intro stack
  induction stack with
  | nil =>
      intro pending E ptr node
      rw [segLoop.eq_1]
      refine allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) ?_)
      exact allQ_bind (pubGood_pendingHash _ _ _ _ _) fun _ =>
        allQ_bind (pubGood_foldsP _ _ _ _ _ _ _) fun _ => allQ_pure _
  | cons top rest ih =>
      intro pending E ptr node
      obtain ⟨pn, Q⟩ := top
      rw [segLoop.eq_1]
      refine allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) ?_)
      exact allQ_bind (pubGood_pendingHash _ _ _ _ _) fun _ =>
        allQ_bind (pubGood_foldsP _ _ _ _ _ _ _) fun _ =>
          allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) (ih _ _ _ _))

theorem pubGood_ftsCoordP (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat) :
    AllQueriesSatisfy (ftsCoordP w index coord sel ptr) PubGood := by
  unfold ftsCoordP
  refine allQ_bind (pubGood_segLoop _ _ _ _ _ _ _ _) fun r0 => ?_
  rcases r0 with _ | ⟨n0, E0, p0, s0⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_segLoop _ _ _ _ _ _ _ _) fun r1 => ?_
  rcases r1 with _ | ⟨n1, E1, p1, s1⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_segLoop _ _ _ _ _ _ _ _) fun r2 => ?_
  rcases r2 with _ | ⟨n2, E2, p2, s2⟩
  · exact allQ_pure _
  exact allQ_ite _ (allQ_pure _) (allQ_pure _)

theorem pubGood_ftsP (w : WBytes) (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (ftsP w index chosen) PubGood := by
  unfold ftsP
  refine allQ_bind (allQ_foldlM _ _ (fun st c => ?_) _) fun st => ?_
  · rcases st with _ | ⟨roots, ptr⟩
    · exact allQ_pure _
    refine allQ_bind (pubGood_ftsCoordP _ _ _ _ _) fun r => ?_
    rcases r with _ | ⟨root, ptr'⟩ <;> exact allQ_pure _
  · rcases st with _ | ⟨roots, ptr⟩
    · exact allQ_pure _
    exact allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_forestPk _ _) fun _ => allQ_pure _)

theorem pubGood_layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (layerP w index lay digits) PubGood := by
  unfold layerP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chainP _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_nodeHashP _ _ _ _ _ _ _) _

theorem pubGood_layersP (w : WBytes) (index : Nat) : ∀ n root,
    AllQueriesSatisfy (layersP w index n root) PubGood := by
  intro n
  induction n with
  | zero => intro root; exact allQ_pure _
  | succ n ih =>
      intro root
      unfold layersP
      refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_encoding _ _ _ _ _) fun d => ?_)
      split
      · exact allQ_bind (pubGood_layerP _ _ _ _) fun _ => ih _
      · exact allQ_pure _

/-- **Every query of `verifyP` is a public hash of a nonempty aligned input.** -/
theorem pubGood_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) PubGood := by
  rw [verifyP_eq_tail]
  refine allQ_bind ?_ fun r => ?_
  · unfold digestP; exact allQ_ite _ (allQ_pure _) (allQ_map _ (pubGood_digest _ _ _))
  · rcases r with _ | N
    · exact allQ_pure _
    unfold verifyTailP
    refine allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_ftsP _ _ _) fun r => ?_))
    rcases r with _ | root
    · exact allQ_pure _
    refine allQ_bind (pubGood_layersP _ _ _ _) fun r => ?_
    rcases r with _ | root <;> exact allQ_pure _

/-! ## `expandN` -/

theorem pubGood_digestSearch (rho : Digest) (m : Message) : ∀ fuel counter,
    AllQueriesSatisfy (digestSearch rho m counter fuel) PubGood := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact allQ_pure _
  | succ fuel ih =>
      intro counter
      unfold digestSearch
      exact allQ_bind (pubGood_digest _ _ _) fun _ => allQ_ite _ (allQ_pure _) (ih _)

theorem pubGood_counterSearch (lay : Layer) (tree leaf : Nat) (msg : Digest) : ∀ fuel counter,
    AllQueriesSatisfy (counterSearch lay tree leaf msg counter fuel) PubGood := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact allQ_pure _
  | succ fuel ih =>
      intro counter
      unfold counterSearch
      refine allQ_bind (pubGood_encoding _ _ _ _ _) fun a => ?_
      split
      · exact ih _
      · exact allQ_pure _

theorem pubGood_recoverChild (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 118 → Digest) : ∀ level node used,
    AllQueriesSatisfy (recoverChild index coord leaves values proof level node used) PubGood := by
  intro level
  induction level with
  | zero =>
      intro node used
      unfold recoverChild
      refine allQ_ite _ ?_ (allQ_bind (pubGood_ftsLeaf _ _ _ _) fun _ => allQ_pure _)
      split <;> exact allQ_pure _
  | succ level ih =>
      intro node used
      unfold recoverChild
      refine allQ_ite _ ?_ ?_
      · split <;> exact allQ_pure _
      · refine allQ_bind (ih _ _) fun r => ?_
        rcases r with _ | ⟨l, n⟩
        · exact allQ_pure _
        refine allQ_bind (ih _ _) fun r => ?_
        rcases r with _ | ⟨rr, n'⟩
        · exact allQ_pure _
        exact allQ_bind (pubGood_nodeHash _ _ _ _ _ _) fun _ => allQ_pure _

theorem pubGood_recoverFts (sig : Signature) (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (recoverFts sig index chosen) PubGood := by
  unfold recoverFts
  refine allQ_bind (allQ_foldlM _ _ (fun st c => ?_) _) fun st => ?_
  · rcases st with _ | ⟨roots, used⟩
    · exact allQ_pure _
    refine allQ_bind (pubGood_recoverChild _ _ _ _ _ _ _ _) fun r => ?_
    rcases r with _ | ⟨v, n⟩
    · exact allQ_pure _
    refine allQ_bind (allQ_foldlM _ _ (fun st j => ?_) _) fun r => ?_
    · rcases st with _ | ⟨v, u⟩
      · exact allQ_pure _
      simp only []
      split
      · exact allQ_bind (pubGood_nodeHash _ _ _ _ _ _) fun _ => allQ_pure _
      · exact allQ_pure _
    · rcases r with _ | ⟨root, n⟩ <;> exact allQ_pure _
  · rcases st with _ | ⟨roots, used⟩
    · exact allQ_pure _
    exact allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_forestPk _ _) fun _ => allQ_pure _)

theorem pubGood_recoverLayer (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (recoverLayer sig index lay digits) PubGood := by
  unfold recoverLayer
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHash _ _ _ _) fun _ => allQ_foldlM _ _ (fun _ _ => pubGood_nodeHash _ _ _ _ _ _) _

theorem pubGood_expandLayers (sig : Signature) (index : Nat) : ∀ n root,
    AllQueriesSatisfy (expandLayers sig index n root) PubGood := by
  intro n
  induction n with
  | zero => intro root; exact allQ_pure _
  | succ n ih =>
      intro root
      unfold expandLayers
      refine allQ_bind (pubGood_counterSearch _ _ _ _ _ _) fun r => ?_
      rcases r with _ | ⟨c, digits⟩
      · exact allQ_pure _
      refine allQ_bind (pubGood_recoverLayer _ _ _ _) fun _ => allQ_bind (ih _) fun r => ?_
      rcases r with _ | ⟨root', cs⟩ <;> exact allQ_pure _

/-- **Every query of `expandN` is a public hash of a nonempty aligned input.** -/
theorem pubGood_expandN (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expandN m pk σ) PubGood := by
  unfold expandN
  refine allQ_bind (pubGood_digestSearch _ _ _ _) fun r => ?_
  rcases r with _ | ⟨c, N⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_recoverFts _ _ _) fun r => ?_
  rcases r with _ | root
  · exact allQ_pure _
  refine allQ_bind (pubGood_expandLayers _ _ _ _) fun r => ?_
  rcases r with _ | ⟨root', cs⟩
  · exact allQ_pure _
  exact allQ_ite _ (allQ_pure _) (allQ_pure _)

theorem pubGood_expandB (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expandB m pk σ) PubGood := allQ_map _ (pubGood_expandN m pk σ)

/-! ## Monotonicity and the derived shapes -/

theorem allQ_mono {α : Type} {P Q : Spec.Domain → Prop} {p : M α} (h : AllQueriesSatisfy p P)
    (hPQ : ∀ q, P q → Q q) : AllQueriesSatisfy p Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
      rw [allQueriesSatisfy_query_bind_iff] at h ⊢
      exact ⟨hPQ _ h.1, fun u => ih u (h.2 u)⟩

/-- `verifyP` is hash-only (CLOSURE's `SourceReplay.HashOnly` shape). -/
theorem hashOnly_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) isHash :=
  allQ_mono (pubGood_verifyP m pk w) fun _ h => h.hashGood.1

theorem hashOnly_expandN (m : Message) (pk : Digest) (σ : Signature) : AllQueriesSatisfy (expandN m pk σ) isHash :=
  allQ_mono (pubGood_expandN m pk σ) fun _ h => h.hashGood.1

theorem hashOnly_expandB (m : Message) (pk : Digest) (σ : Signature) : AllQueriesSatisfy (expandB m pk σ) isHash :=
  allQ_mono (pubGood_expandB m pk σ) fun _ h => h.hashGood.1

/-- `verifyP` and `expandN` never query a private coordinate (`mrealize sk` of them does not depend on `sk`). -/
theorem publicOnly_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) isPublic :=
  allQ_mono (pubGood_verifyP m pk w) fun _ h => h.1

theorem publicOnly_expandN (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expandN m pk σ) isPublic := allQ_mono (pubGood_expandN m pk σ) fun _ h => h.1

/-- The honest machine-object pipeline is hash-only given that Core's keygen and sign are (CLOSURE's
`SourceReplay.hashOnly_keygen`, `hashOnly_sign`). -/
theorem hashOnly_honestProgramB (hk : AllQueriesSatisfy keygen isHash)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) isHash) (m : Message) :
    AllQueriesSatisfy (honestProgramB m) isHash := by
  unfold honestProgramB
  apply allQ_bind hk
  intro keys
  apply allQ_bind (hs _ _)
  intro sig
  rcases sig with _ | sig
  · exact allQ_pure _
  apply allQ_bind (hashOnly_expandB _ _ _)
  intro wb
  rcases wb with _ | wb
  · exact allQ_pure _
  exact hashOnly_verifyP _ _ _

/-! ## Alignment of the Core programs' queries -/

theorem allQ_of_bound {α : Type} {P : Spec.Domain → Prop} {Post : α → Prop} {k : Nat} {p : M α}
    (h : Cost.Bound P Post k p) : AllQueriesSatisfy p P := by
  induction h with
  | pure a k _ => exact allQueriesSatisfy_pure _ _
  | query q f k hq _ ih =>
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hq, ih⟩

/-- Every public query of Core's keygen is nonempty and aligned (`Cost.bound_keygen`). -/
theorem goodQ_keygen : AllQueriesSatisfy keygen Cost.GoodQuery := allQ_of_bound Cost.bound_keygen

theorem goodQ_sign (cache : Cache) (m : Message) : AllQueriesSatisfy (sign cache m) Cost.GoodQuery :=
  allQ_of_bound (Cost.bound_sign cache m)

theorem goodQ_expand (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expand m pk σ) Cost.GoodQuery := allQ_of_bound (Cost.bound_expand m pk σ)

theorem goodQ_verify (m : Message) (pk : Digest) (w : Witness) :
    AllQueriesSatisfy (verify m pk w) Cost.GoodQuery := allQ_of_bound (Cost.bound_verify m pk w)

theorem goodQ_expandN (m : Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expandN m pk σ) Cost.GoodQuery := allQ_mono (pubGood_expandN m pk σ) fun _ h => h.2

theorem goodQ_verifyP (m : Message) (pk : Digest) (w : WBytes) :
    AllQueriesSatisfy (verifyP m pk w) Cost.GoodQuery := allQ_mono (pubGood_verifyP m pk w) fun _ h => h.2

/-- Realized private inputs are nonempty and aligned (`pad64`). -/
theorem privateInput_positive_aligned (sk : BitVec 256) (c : Coordinate) :
    0 < (privateInput sk c).length ∧ (privateInput sk c).length % 64 = 0 := by
  have h1 := Cost.private_realization_weight sk c
  refine ⟨?_, ?_⟩
  · have hw : 1 ≤ Cost.weight (.inr c) := by rcases c with t | m | r <;> simp [Cost.weight]
    omega
  · unfold privateInput; exact Cost.pad64_aligned _

end SigGolfCandidate.T3M


/-! ## Byte input injectivity and backward security extraction

These lemmas retain the actual witness bytes in public hash queries. They produce
a distinct-input hit with its target position and trace membership; the adaptive
security game supplies the stopping/freshness and probability argument separately.
Unused witness pads (including zero-length chains) remain unconstrained. -/

/-!
Exact input separation for T3's padded verifier. These are equalities of query bytes,
not of hash outputs. Equal outputs of unequal inputs remain a collision event for
security extraction to charge. No hypothesis bounds the adversarial pads.
-/
namespace SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)

/-- Four consecutive 128-bit fields, in their actual little-endian query layout. -/
def block4 (a b c d : Digest) : HashInput :=
  bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c ++ bytesLE 16 d

@[simp] theorem block4_length (a b c d : Digest) : (block4 a b c d).length = 64 := by
  simp [block4, bytesLE_length]

@[simp] theorem pad64_block4 (a b c d : Digest) : pad64 (block4 a b c d) = block4 a b c d := by
  simp [pad64]

theorem block4_injective {a b c d a' b' c' d' : Digest}
    (h : block4 a b c d = block4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  unfold block4 at h
  obtain ⟨h, hd⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨ha, hb⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective ha, bytesLE_injective hb, bytesLE_injective hc, bytesLE_injective hd⟩

@[simp] theorem block4_eq_iff {a b c d a' b' c' d' : Digest} :
    block4 a b c d = block4 a' b' c' d' ↔
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · exact block4_injective
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

private theorem bytesLE_zero : bytesLE 16 (0 : Digest) = zero16 := by decide

/-- The raw query of `ftsLeafP`, before the (vacuous) 64-byte padding. -/
def ftsLeafInputP (index coord leaf : Nat) (pad0 secret pad1 : Digest) : HashInput :=
  block4 pad0 (header 9 coord index 0 leaf) secret pad1

/-- The raw query of `nodeHashP`, for both FTS folds (tag 10) and Merkle nodes (tag 3). -/
def nodeInputP (tag lay tree heap : Nat) (left pad right : Digest) : HashInput :=
  block4 left (header tag lay tree 0 heap) pad right

theorem ftsLeafP_eq_shortHash (index coord leaf : Nat) (pad0 secret pad1 : Digest) :
    ftsLeafP index coord leaf pad0 secret pad1 = shortHash (ftsLeafInputP index coord leaf pad0 secret pad1) := rfl

theorem nodeHashP_eq_shortHash (tag lay tree heap : Nat) (left pad right : Digest) :
    nodeHashP tag lay tree heap left pad right = shortHash (nodeInputP tag lay tree heap left pad right) := rfl

theorem ftsLeaf_eq_shortHash (index coord leaf : Nat) (secret : Digest) :
    ftsLeaf index coord leaf secret = shortHash (ftsLeafInputP index coord leaf 0 secret 0) := by
  simp only [ftsLeaf, ftsLeafInputP, block4, bytesLE_zero]

theorem nodeHash_eq_shortHash (tag lay tree heap : Nat) (left right : Digest) :
    nodeHash tag lay tree heap left right = shortHash (nodeInputP tag lay tree heap left 0 right) := by
  simp only [nodeHash, nodeInputP, block4, bytesLE_zero]

theorem chainInputP_eq_block4 (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 value : Digest) :
    chainInputP lay tree leaf i step pad0 pad1 value =
      block4 pad0 (header 1 lay.val tree (step + 256 * i) leaf) pad1 value := rfl

theorem chainInput_eq_zero (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    chainInput lay tree leaf i step value = chainInputP lay tree leaf i step 0 0 value := by
  simp only [chainInput, chainInputP, bytesLE_zero]

@[simp] theorem pad64_ftsLeafInputP (index coord leaf : Nat) (pad0 secret pad1 : Digest) :
    pad64 (ftsLeafInputP index coord leaf pad0 secret pad1) = ftsLeafInputP index coord leaf pad0 secret pad1 :=
  pad64_block4 _ _ _ _

@[simp] theorem pad64_nodeInputP (tag lay tree heap : Nat) (left pad right : Digest) :
    pad64 (nodeInputP tag lay tree heap left pad right) = nodeInputP tag lay tree heap left pad right :=
  pad64_block4 _ _ _ _

@[simp] theorem pad64_chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 value : Digest) :
    pad64 (chainInputP lay tree leaf i step pad0 pad1 value) = chainInputP lay tree leaf i step pad0 pad1 value :=
  pad64_block4 _ _ _ _

/-- No semantic bounds are needed to extract pads and payload from matching FTS queries. -/
theorem ftsLeafInputP_fields {index coord leaf index' coord' leaf' : Nat}
    {pad0 secret pad1 pad0' secret' pad1' : Digest}
    (h : ftsLeafInputP index coord leaf pad0 secret pad1 =
      ftsLeafInputP index' coord' leaf' pad0' secret' pad1') :
    pad0 = pad0' ∧ header 9 coord index 0 leaf = header 9 coord' index' 0 leaf' ∧
      secret = secret' ∧ pad1 = pad1' := block4_injective h

/-- The shared node query format is injective in its four encoded fields. -/
theorem nodeInputP_fields {tag lay tree heap tag' lay' tree' heap' : Nat}
    {left pad right left' pad' right' : Digest}
    (h : nodeInputP tag lay tree heap left pad right = nodeInputP tag' lay' tree' heap' left' pad' right') :
    left = left' ∧ header tag lay tree 0 heap = header tag' lay' tree' 0 heap' ∧
      pad = pad' ∧ right = right' := block4_injective h

theorem chainInputP_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {pad0 pad1 value pad0' pad1' value' : Digest}
    (h : chainInputP lay tree leaf i step pad0 pad1 value =
      chainInputP lay' tree' leaf' i' step' pad0' pad1' value') :
    pad0 = pad0' ∧ header 1 lay.val tree (step + 256 * i) leaf =
      header 1 lay'.val tree' (step' + 256 * i') leaf' ∧ pad1 = pad1' ∧ value = value' :=
  block4_injective h

/-- Matching any canonical FTS leaf forces both pads to zero, even before proving header bounds. -/
theorem ftsLeafInputP_eq_canonical {index coord leaf index' coord' leaf' : Nat}
    {pad0 secret pad1 secret' : Digest}
    (h : ftsLeafInputP index coord leaf pad0 secret pad1 =
      zero16 ++ bytesLE 16 (header 9 coord' index' 0 leaf') ++ bytesLE 16 secret' ++ zero16) :
    pad0 = 0 ∧ header 9 coord index 0 leaf = header 9 coord' index' 0 leaf' ∧
      secret = secret' ∧ pad1 = 0 := by
  apply ftsLeafInputP_fields
  simpa only [ftsLeafInputP, block4, bytesLE_zero] using h

/-- Matching any canonical Merkle/FTS node forces its pad to zero. -/
theorem nodeInputP_eq_canonical {tag lay tree heap tag' lay' tree' heap' : Nat}
    {left pad right left' right' : Digest}
    (h : nodeInputP tag lay tree heap left pad right = bytesLE 16 left' ++
      bytesLE 16 (header tag' lay' tree' 0 heap') ++ zero16 ++ bytesLE 16 right') :
    left = left' ∧ header tag lay tree 0 heap = header tag' lay' tree' 0 heap' ∧
      pad = 0 ∧ right = right' := by
  apply nodeInputP_fields
  simpa only [nodeInputP, block4, bytesLE_zero] using h

/-- Matching any actual Core chain query forces both pads to zero. -/
theorem chainInputP_eq_canonical {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {pad0 pad1 value value' : Digest}
    (h : chainInputP lay tree leaf i step pad0 pad1 value = chainInput lay' tree' leaf' i' step' value') :
    pad0 = 0 ∧ header 1 lay.val tree (step + 256 * i) leaf =
      header 1 lay'.val tree' (step' + 256 * i') leaf' ∧ pad1 = 0 ∧ value = value' :=
  chainInputP_fields (h.trans (chainInput_eq_zero _ _ _ _ _ _))

/-- Full FTS query injectivity. The header stores 8-bit coordinates, a 40-bit index,
32-bit leaf indices; bounds prevent truncation, not adversarial padding. -/
theorem ftsLeafInputP_injective {index coord leaf index' coord' leaf' : Nat}
    {pad0 secret pad1 pad0' secret' pad1' : Digest}
    (hc : coord < 256) (hi : index < 2^40) (hl : leaf < 2^32)
    (hc' : coord' < 256) (hi' : index' < 2^40) (hl' : leaf' < 2^32)
    (h : ftsLeafInputP index coord leaf pad0 secret pad1 =
      ftsLeafInputP index' coord' leaf' pad0' secret' pad1') :
    index = index' ∧ coord = coord' ∧ leaf = leaf' ∧ pad0 = pad0' ∧ secret = secret' ∧ pad1 = pad1' := by
  obtain ⟨hp0, hh, hs, hp1⟩ := ftsLeafInputP_fields h
  obtain ⟨_, hc, hi, _, hl⟩ := header_injective (by decide) hc hi (by decide) hl
    (by decide) hc' hi' (by decide) hl' hh
  exact ⟨hi, hc, hl, hp0, hs, hp1⟩

/-- Full node query injectivity, including the tag separating FTS (10) from Merkle (3). -/
theorem nodeInputP_injective {tag lay tree heap tag' lay' tree' heap' : Nat}
    {left pad right left' pad' right' : Digest}
    (ht : tag < 256) (hl : lay < 256) (htr : tree < 2^40) (hh : heap < 2^32)
    (ht' : tag' < 256) (hl' : lay' < 256) (htr' : tree' < 2^40) (hh' : heap' < 2^32)
    (h : nodeInputP tag lay tree heap left pad right = nodeInputP tag' lay' tree' heap' left' pad' right') :
    tag = tag' ∧ lay = lay' ∧ tree = tree' ∧ heap = heap' ∧ left = left' ∧ pad = pad' ∧ right = right' := by
  obtain ⟨hleft, he, hpad, hright⟩ := nodeInputP_fields h
  obtain ⟨ht, hl, htr, _, hh⟩ := header_injective ht hl htr (by decide) hh ht' hl' htr' (by decide) hh' he
  exact ⟨ht, hl, htr, hh, hleft, hpad, hright⟩

/-- Separate the chain and step packed into the 32-bit position field. The general
bounds here (24-bit chain, 8-bit step) are much weaker than T3's 58 chains/8 steps. -/
theorem chainInputP_injective {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {pad0 pad1 value pad0' pad1' value' : Digest}
    (ht : tree < 2^40) (hl : leaf < 2^32) (hi : i < 2^24) (hs : step < 256)
    (ht' : tree' < 2^40) (hl' : leaf' < 2^32) (hi' : i' < 2^24) (hs' : step' < 256)
    (h : chainInputP lay tree leaf i step pad0 pad1 value =
      chainInputP lay' tree' leaf' i' step' pad0' pad1' value') :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ i = i' ∧ step = step' ∧
      pad0 = pad0' ∧ pad1 = pad1' ∧ value = value' := by
  obtain ⟨hp0, he, hp1, hv⟩ := chainInputP_fields h
  have hla : lay.val < 256 := lt_trans lay.isLt (by decide)
  have hla' : lay'.val < 256 := lt_trans lay'.isLt (by decide)
  have hp : step + 256 * i < 2^32 := by omega
  have hp' : step' + 256 * i' < 2^32 := by omega
  obtain ⟨_, hla, ht, hpos, hl⟩ := header_injective (by decide) hla ht hp hl
    (by decide) hla' ht' hp' hl' he
  obtain ⟨hs, hi⟩ := pack_nat_injective hs hs' hpos
  exact ⟨Fin.ext hla, ht, hl, hi, hs, hp0, hp1, hv⟩

end SigGolfCandidate.T3M.SecurityInputs



/-! First-divergence extraction for the actual byte-level padded verifier.
The inputs below are byte lists, including free witness bytes; no abstract
replacement encoding or zero-pad assumption is used. -/
namespace SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec SigGolfCandidate.T3
open Correctness (Answers)

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Exact query domains along the deterministic execution. -/
def queried {α : Type} (answers : Answers) (program : M α) : List Spec.Domain :=
  ((simulateQ answers.withLogging program).run).2.map Sigma.fst

@[simp] theorem queried_pure {α : Type} (answers : Answers) (value : α) :
    queried answers (pure value) = [] := rfl

@[simp] theorem queried_query_bind {α : Type} (answers : Answers)
    (q : Spec.Domain) (next : Spec.Range q → M α) :
    queried answers (liftM (Spec.query q) >>= next) =
      q :: queried answers (next (answers q)) := rfl

theorem queried_bind {α β : Type} (answers : Answers) (program : M α) (next : α → M β) :
    queried answers (program >>= next) = queried answers program ++
      queried answers (next (evalWithAnswerFn answers program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind q rest ih =>
      rw [bind_assoc, queried_query_bind, queried_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn answers (liftM (Spec.query q)) = answers q from
          simulateQ_spec_query answers q, List.cons_append]

@[simp] theorem queried_shortHash (answers : Answers) (input : HashInput) :
    queried answers (shortHash input) = [.inl (.inr (pad64 input))] := rfl

theorem eval_shortHash (answers : Answers) (input : HashInput) :
    evalWithAnswerFn answers (shortHash input) =
      (answers (.inl (.inr (pad64 input)))).extractLsb' 0 128 := rfl

/-- A sequence of the verifier's actual short-hash operations. -/
def hashPath (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) : M Digest :=
  (List.range count).foldlM (fun value step => shortHash (input step value)) initial

def pathValue (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) (count : Nat) : Digest :=
  evalWithAnswerFn answers (hashPath input count initial)

def pathInput (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) (step : Nat) : HashInput := input step (pathValue answers input initial step)

theorem hashPath_succ (input : Nat → Digest → HashInput) (count : Nat) (initial : Digest) :
    hashPath input (count + 1) initial =
      (hashPath input count initial >>= fun value => shortHash (input count value)) := by
  simp [hashPath, List.range_succ, List.foldlM_append]

@[simp] theorem pathValue_zero (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) : pathValue answers input initial 0 = initial := rfl

theorem pathValue_succ (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) (step : Nat) :
    pathValue answers input initial (step + 1) =
      evalWithAnswerFn answers (shortHash (pathInput answers input initial step)) := by
  simp only [pathValue, hashPath_succ, evalWithAnswerFn_bind, pathInput]

/-- Every extracted step names a query actually issued by this execution. -/
theorem pathInput_queried (answers : Answers) (input : Nat → Digest → HashInput)
    (initial : Digest) (count step : Nat) (hstep : step < count) :
    .inl (.inr (pad64 (pathInput answers input initial step))) ∈
      queried answers (hashPath input count initial) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [hashPath_succ, queried_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
      · exact List.mem_append_left _ (ih hlt)
      · apply List.mem_append_right
        simp only [queried_shortHash, List.mem_singleton]
        rfl

/-- Different complete oracle inputs with the same 128-bit output. -/
def HashHit (answers : Answers) (honest actual : HashInput) : Prop :=
  actual ≠ honest ∧
    (answers (.inl (.inr actual))).extractLsb' 0 128 =
      (answers (.inl (.inr honest))).extractLsb' 0 128

/-- If a padded hash path reaches an honest target, either every step parses as
the honest step, including its pad conditions, or an actual query hits the honest
output at a different complete oracle input. `parse` is byte-input injectivity;
`reference` is the honest computation's recurrence. -/
theorem hashPath_extract (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValue answers input initial count = target count) :
    (initial = target 0 ∧ ∀ step, step < count → Good step) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers input initial step))) ∈
          queried answers (hashPath input count initial) ∧
        HashHit answers (pad64 (honestInput step)) (pad64 (pathInput answers input initial step)) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (pathInput answers input initial count) = pad64 (honestInput count)
      · obtain ⟨hprev, hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit, hall⟩ | ⟨step, hstep, _, hhit⟩
        · left
          refine ⟨hinit, fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
          · exact hall step hlt
          · exact hgood
        · exact Or.inr ⟨step, by omega, pathInput_queried answers input initial _ _ (by omega), hhit⟩
      · right
        refine ⟨count, by omega, pathInput_queried answers input initial _ _ (by omega), heq, ?_⟩
        rw [pathValue_succ] at reaches
        exact reaches.trans (reference count (by omega)).symm

/-- Shifting a finite natural-number fold preserves the exact oracle program. -/
theorem foldlM_range'_eq_hashPath (input : Nat → Digest → HashInput)
    (start count : Nat) (initial : Digest) :
    (List.range' start count).foldlM (fun value step => shortHash (input step value)) initial =
      hashPath (fun step value => input (start + step) value) count initial := by
  rw [List.range'_eq_map_range, List.foldlM_map]
  rfl

/-- The actual padded chain is the generic extraction path with the absolute
chain-step index offset by `start`. -/
theorem chainP_eq_hashPath (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 initial : Digest) :
    chainP lay tree leaf i start count pad0 pad1 initial =
      hashPath (fun step value => chainInputP lay tree leaf i (start + step) pad0 pad1 value)
        count initial := by
  exact foldlM_range'_eq_hashPath (fun step value => chainInputP lay tree leaf i step pad0 pad1 value)
    start count initial

/-- Finite indices enumerate the same natural indices, in the same order. -/
theorem map_val_finRange (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Exact oracle-program bridge for the actual Merkle fold's `List.finRange`.
No bound or property of the input function is required. -/
theorem foldlM_finRange_eq_hashPath (input : Nat → Digest → HashInput)
    (count : Nat) (initial : Digest) :
    (List.finRange count).foldlM (fun value j => shortHash (input j.val value)) initial =
      hashPath input count initial := by
  unfold hashPath
  rw [← map_val_finRange count, List.foldlM_map]


end SigGolfCandidate.T3M.SecurityExtraction

namespace SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs
open Correctness (Answers TreeLevels treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Padded FTS leaves reaching an honest leaf expose its secret with zero pads,
or give a distinct-input hit on that honest leaf's hash. -/
theorem ftsLeafP_extract (answers : Answers) (index coord leaf : Nat)
    (pad0 secret pad1 honestSecret : Digest)
    (reaches : evalWithAnswerFn answers (ftsLeafP index coord leaf pad0 secret pad1) =
      evalWithAnswerFn answers (ftsLeaf index coord leaf honestSecret)) :
    (pad0 = 0 ∧ secret = honestSecret ∧ pad1 = 0) ∨
      (HashHit answers (ftsLeafInputP index coord leaf 0 honestSecret 0)
        (ftsLeafInputP index coord leaf pad0 secret pad1) ∧
      .inl (.inr (ftsLeafInputP index coord leaf pad0 secret pad1)) ∈
        queried answers (ftsLeafP index coord leaf pad0 secret pad1)) := by
  by_cases heq : ftsLeafInputP index coord leaf pad0 secret pad1 =
      ftsLeafInputP index coord leaf 0 honestSecret 0
  · obtain ⟨h0, _, hs, h1⟩ := ftsLeafInputP_fields heq
    exact Or.inl ⟨h0, hs, h1⟩
  · right
    constructor
    · refine ⟨heq, ?_⟩
      rw [ftsLeafP_eq_shortHash, ftsLeaf_eq_shortHash, eval_shortHash, eval_shortHash,
        pad64_ftsLeafInputP, pad64_ftsLeafInputP] at reaches
      exact reaches
    · rw [ftsLeafP_eq_shortHash, queried_shortHash, pad64_ftsLeafInputP]
      exact List.mem_singleton_self _

/-- The same extraction step covers both FTS folds and Merkle nodes, in their
actual 64-byte query format. -/
theorem nodeHashP_extract (answers : Answers) (tag lay tree heap : Nat)
    (left pad right honestLeft honestRight : Digest)
    (reaches : evalWithAnswerFn answers (nodeHashP tag lay tree heap left pad right) =
      evalWithAnswerFn answers (nodeHash tag lay tree heap honestLeft honestRight)) :
    (left = honestLeft ∧ pad = 0 ∧ right = honestRight) ∨
      (HashHit answers (nodeInputP tag lay tree heap honestLeft 0 honestRight)
        (nodeInputP tag lay tree heap left pad right) ∧
      .inl (.inr (nodeInputP tag lay tree heap left pad right)) ∈
        queried answers (nodeHashP tag lay tree heap left pad right)) := by
  by_cases heq : nodeInputP tag lay tree heap left pad right =
      nodeInputP tag lay tree heap honestLeft 0 honestRight
  · obtain ⟨hl, _, hp, hr⟩ := nodeInputP_fields heq
    exact Or.inl ⟨hl, hp, hr⟩
  · right
    constructor
    · refine ⟨heq, ?_⟩
      rw [nodeHashP_eq_shortHash, nodeHash_eq_shortHash, eval_shortHash, eval_shortHash,
        pad64_nodeInputP, pad64_nodeInputP] at reaches
      exact reaches
    · rw [nodeHashP_eq_shortHash, queried_shortHash, pad64_nodeInputP]
      exact List.mem_singleton_self _

/-- Honest chain prefix values; the seed can be any fixed private-table output. -/
def honestChainValue (answers : Answers) (lay : Layer) (tree leaf i : Nat)
    (seed : Digest) (step : Nat) : Digest :=
  evalWithAnswerFn answers (chain lay tree leaf i 0 step seed)

theorem honestChainValue_succ (answers : Answers) (lay : Layer) (tree leaf i : Nat)
    (seed : Digest) (step : Nat) :
    evalWithAnswerFn answers (shortHash (chainInput lay tree leaf i step
      (honestChainValue answers lay tree leaf i seed step))) =
        honestChainValue answers lay tree leaf i seed (step + 1) := by
  unfold honestChainValue
  rw [Correctness.eval_chain_add]
  simp [chain]

def chainPathInput (lay : Layer) (tree leaf i start : Nat) (pad0 pad1 : Digest) :
    Nat → Digest → HashInput := fun step value =>
  chainInputP lay tree leaf i (start + step) pad0 pad1 value

/-- Chain extraction on the exact padded step inputs. The unused pads of a
zero-length chain are intentionally unconstrained. -/
theorem chainPath_extract (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 value seed : Digest)
    (reaches : pathValue answers (chainPathInput lay tree leaf i start pad0 pad1) value count =
      honestChainValue answers lay tree leaf i seed (start + count)) :
    (value = honestChainValue answers lay tree leaf i seed start ∧
      (0 < count → pad0 = 0 ∧ pad1 = 0)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1) value step))) ∈
          queried answers (hashPath (chainPathInput lay tree leaf i start pad0 pad1) count value) ∧
        HashHit answers
          (pad64 (chainInput lay tree leaf i (start + step)
            (honestChainValue answers lay tree leaf i seed (start + step))))
          (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1) value step)) := by
  have h := hashPath_extract answers (chainPathInput lay tree leaf i start pad0 pad1)
    (fun step => chainInput lay tree leaf i (start + step)
      (honestChainValue answers lay tree leaf i seed (start + step)))
    (fun step => honestChainValue answers lay tree leaf i seed (start + step))
    (fun _ => pad0 = 0 ∧ pad1 = 0) value count
    (fun step _ => by simpa only [Nat.add_assoc] using
      honestChainValue_succ answers lay tree leaf i seed (start + step))
    (fun step _ current heq => by
      simp only [chainPathInput, chainInput_eq_zero, pad64_chainInputP] at heq
      obtain ⟨hp0, _, hp1, hv⟩ := chainInputP_fields heq
      exact ⟨hv, hp0, hp1⟩) reaches
  rcases h with ⟨hvalue, hpads⟩ | hhit
  · exact Or.inl ⟨by simpa using hvalue, fun hcount => hpads 0 hcount⟩
  · exact Or.inr hhit

/-- The chain result applied to `chainP` itself, with the hit in its actual query
trace. No bound on the adversarial pad values is assumed. -/
theorem chainP_extract (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 value seed : Digest)
    (reaches : evalWithAnswerFn answers (chainP lay tree leaf i start count pad0 pad1 value) =
      honestChainValue answers lay tree leaf i seed (start + count)) :
    (value = honestChainValue answers lay tree leaf i seed start ∧
      (0 < count → pad0 = 0 ∧ pad1 = 0)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1) value step))) ∈
          queried answers (chainP lay tree leaf i start count pad0 pad1 value) ∧
        HashHit answers
          (pad64 (chainInput lay tree leaf i (start + step)
            (honestChainValue answers lay tree leaf i seed (start + step))))
          (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1) value step)) := by
  rw [chainP_eq_hashPath] at reaches ⊢
  exact chainPath_extract answers lay tree leaf i start count pad0 pad1 value seed reaches

/-- Merkle authentication input, retaining the machine's heap index and the
witness pad in the middle of its 64-byte block. -/
def merkleInput (tag lay tree height leaf : Nat) (path pads : Nat → Digest)
    (step : Nat) (value : Digest) : HashInput :=
  let pair := if leaf / 2^step % 2 = 0 then (value, path step) else (path step, value)
  nodeInputP tag lay tree (2^(height-step-1) + leaf/2^(step+1)) pair.1 (pads step) pair.2

theorem merkleInput_parse (tag lay tree height leaf step : Nat)
    (path pads honestPath : Nat → Digest) (current target : Digest)
    (heq : pad64 (merkleInput tag lay tree height leaf path pads step current) =
      pad64 (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step target)) :
    current = target ∧ path step = honestPath step ∧ pads step = 0 := by
  unfold merkleInput at heq
  split at heq <;> simp only [pad64_nodeInputP] at heq
  · obtain ⟨hc, _, hp, hs⟩ := nodeInputP_fields heq
    exact ⟨hc, hs, hp⟩
  · obtain ⟨hs, _, hp, hc⟩ := nodeInputP_fields heq
    exact ⟨hc, hs, hp⟩

/-- Backwards extraction for a Merkle authentication path. With no distinct-input
hit, its initial leaf and every sibling are honest and every hashed pad is zero. -/
theorem merklePath_extract (answers : Answers) (tag lay tree height leaf count : Nat)
    (path pads honestPath target : Nat → Digest) (value : Digest)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash
        (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step))) =
          target (step + 1))
    (reaches : pathValue answers (merkleInput tag lay tree height leaf path pads) value count = target count) :
    (value = target 0 ∧ ∀ step, step < count → path step = honestPath step ∧ pads step = 0) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers (merkleInput tag lay tree height leaf path pads) value step))) ∈
          queried answers (hashPath (merkleInput tag lay tree height leaf path pads) count value) ∧
        HashHit answers
          (pad64 (merkleInput tag lay tree height leaf honestPath (fun _ => 0) step (target step)))
          (pad64 (pathInput answers (merkleInput tag lay tree height leaf path pads) value step)) :=
  hashPath_extract answers _ _ target _ value count reference
    (fun step _ current => merkleInput_parse tag lay tree height leaf step path pads honestPath current (target step)) reaches

/-- The first part of the byte verifier's layer: its padded chains and leaf hash. -/
def layerLeafP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (2^width lay i.val - 1 - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wvalue w lay i.val)
  leafHash lay tree leaf ends

/-- Exact program equality, preserving all queries and their order. -/
theorem layerP_eq_hashPath (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerP w index lay digits = (layerLeafP w index lay digits >>= fun value =>
      hashPath (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerklePad w lay)) (height lay) value) := by
  unfold layerP layerLeafP
  rcases route index lay with ⟨leaf, tree⟩
  dsimp only
  rw [bind_assoc]
  congr 1
  funext ends
  congr 1
  funext value
  exact foldlM_finRange_eq_hashPath
    (merkleInput 3 lay.val tree (height lay) leaf (wpath w lay leaf) (wmerklePad w lay)) (height lay) value

/-- Merkle extraction from the actual byte verifier layer. The hit is a query
of `layerP`, including its chain/leaf prefix, and the no-hit case recovers the
honest leaf, siblings and zero Merkle pads. -/
theorem layerP_merkle_extract (answers : Answers) (w : WBytes) (index : Nat)
    (lay : Layer) (digits : List Nat) (honestPath target : Nat → Digest)
    (reference : ∀ step, step < height lay →
      evalWithAnswerFn answers (shortHash
        (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1
          honestPath (fun _ => 0) step (target step))) = target (step + 1))
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) = target (height lay)) :
    (evalWithAnswerFn answers (layerLeafP w index lay digits) = target 0 ∧
      ∀ step, step < height lay →
        wpath w lay (route index lay).1 step = honestPath step ∧ wmerklePad w lay step = 0) ∨
      ∃ step, step < height lay ∧ ∃ actual,
        .inl (.inr actual) ∈ queried answers (layerP w index lay digits) ∧
        HashHit answers
          (pad64 (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1
            honestPath (fun _ => 0) step (target step))) actual := by
  rw [layerP_eq_hashPath, evalWithAnswerFn_bind] at reaches
  have h := merklePath_extract answers 3 lay.val (route index lay).2 (height lay)
    (route index lay).1 (height lay) (wpath w lay (route index lay).1) (wmerklePad w lay)
    honestPath target (evalWithAnswerFn answers (layerLeafP w index lay digits)) reference reaches
  rcases h with hgood | ⟨step, hstep, hquery, hhit⟩
  · exact Or.inl hgood
  · right
    refine ⟨step, hstep, _, ?_, hhit⟩
    rw [layerP_eq_hashPath, queried_bind]
    exact List.mem_append_right _ hquery

/-- The honest reference recurrence required by `merklePath_extract`, now proved
from the stored tree's actual node-hash recurrence. Siblings use xor 1; the heap
index is exactly the one emitted by the machine's verifier. -/
theorem merkleInput_tree_reference (answers : Answers) (tag lay tree height leaf : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree height leaves height levels)
    (hleaf : leaf < 2^height) (step : Nat) (hstep : step < height) :
    evalWithAnswerFn answers (shortHash
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2^j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2^step)))) =
      treeValue levels (step + 1) (leaf / 2^(step + 1)) := by
  unfold merkleInput
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  rw [← nodeHash_eq_shortHash]
  have hparent : leaf / 2^(step + 1) < 2^(height - (step + 1)) := by
    simpa using Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := height) (by omega) (by simpa using hleaf)
  have hp := htree.2.2 step hstep (leaf / 2^(step + 1)) hparent
  simpa only [treeValue, Nat.sub_sub] using hp.symm

/-- The recurrence holds for every step of any prefix of the tree path. -/
theorem merkleInput_tree_reference_prefix (answers : Answers) (tag lay tree height leaf count : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree height leaves height levels)
    (hleaf : leaf < 2^height) (hcount : count ≤ height) :
    ∀ step, step < count → evalWithAnswerFn answers (shortHash
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2^j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2^step)))) =
      treeValue levels (step + 1) (leaf / 2^(step + 1)) := by
  intro step hstep
  exact merkleInput_tree_reference answers tag lay tree height leaf levels leaves htree hleaf step
    (lt_of_lt_of_le hstep hcount)

/-- Direct specialization to the actual deterministic result of `buildLevels`;
no abstract recurrence assumption remains. -/
theorem merkleInput_built_reference (answers : Answers) (tag lay tree height leaf : Nat)
    (leaves : List Digest) (hlen : leaves.length = 2^height)
    (hleaf : leaf < 2^height) (step : Nat) (hstep : step < height) :
    let levels := evalWithAnswerFn answers (buildLevels tag lay tree height leaves)
    evalWithAnswerFn answers (shortHash
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2^j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2^step)))) =
      treeValue levels (step + 1) (leaf / 2^(step + 1)) := by
  exact merkleInput_tree_reference answers tag lay tree height leaf _ leaves
    (Correctness.eval_buildLevels_correct answers tag lay tree height leaves hlen) hleaf step hstep


/-- Actual layer extraction against its source-built honest tree, with no
assumed recurrence. This is the interface needed by the security game's
backwards walk through the hypertree. -/
theorem layerP_built_merkle_extract (answers : Answers) (w : WBytes) (index : Nat)
    (lay : Layer) (digits : List Nat)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      treeValue (Correctness.builtTree answers lay (route index lay).2) (height lay) 0) :
    (evalWithAnswerFn answers (layerLeafP w index lay digits) =
        Correctness.leafRoot answers lay (route index lay).2 (route index lay).1 ∧
      ∀ step, step < height lay →
        wpath w lay (route index lay).1 step =
          treeValue (Correctness.builtTree answers lay (route index lay).2) step
            ((route index lay).1 / 2^step ^^^ 1) ∧ wmerklePad w lay step = 0) ∨
      ∃ step, step < height lay ∧ ∃ actual,
        .inl (.inr actual) ∈ queried answers (layerP w index lay digits) ∧
        HashHit answers
          (pad64 (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1
            (fun j => treeValue (Correctness.builtTree answers lay (route index lay).2) j
              ((route index lay).1 / 2^j ^^^ 1)) (fun _ => 0) step
            (treeValue (Correctness.builtTree answers lay (route index lay).2) step
              ((route index lay).1 / 2^step)))) actual := by
  have h := layerP_merkle_extract answers w index lay digits
    (fun step => treeValue (Correctness.builtTree answers lay (route index lay).2) step
      ((route index lay).1 / 2^step ^^^ 1))
    (fun step => treeValue (Correctness.builtTree answers lay (route index lay).2) step
      ((route index lay).1 / 2^step))
    (merkleInput_tree_reference answers 3 lay.val (route index lay).2 (height lay) (route index lay).1
      _ _ (Correctness.builtTree_correct answers lay (route index lay).2) (route_leaf_bound index lay))
    (by simpa only [Nat.div_eq_of_lt (route_leaf_bound index lay)] using reaches)
  simpa only [pow_zero, Nat.div_one,
    Correctness.builtTree_leaf answers lay _ _ (route_leaf_bound index lay)] using h

end SigGolfCandidate.T3M.SecurityExtraction
