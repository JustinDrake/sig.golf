import SigGolfCandidate.T3.Gate6.FreshProbability
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable

abbrev Output := BitVec 256
abbrev History (Input : Type) := List (Input × Output)

/-- A lazy-RO cache has at most one record per input. -/
structure Cache (Input : Type) where
  entries : List (Input × Output)
  unique : (entries.map Prod.fst).Nodup

def empty {Input : Type} : Cache Input := ⟨[],by simp⟩

def lookup {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input) : Option Output :=
  cache.entries.lookup input

def insert {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input) (output : Output)
    (fresh : lookup cache input=none) : Cache Input :=
  ⟨(input,output)::cache.entries,by
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,cache.unique⟩
    intro hi
    obtain ⟨pair,hpair,heq⟩ := List.mem_map.mp hi
    have h := List.lookup_eq_none_iff.mp fresh pair hpair
    simp [heq] at h⟩

def Matches (mark : MarkedLabel) (output : Output) : Prop :=
  DigestAccepted output ∧ (digestRecord output).1=mark

noncomputable def count {Input : Type} (mark : MarkedLabel) (cache : Cache Input) : Nat :=
  cache.entries.countP (fun pair => decide (Matches mark pair.2))

noncomputable def eRate : ENNReal := acceptance/2^59
noncomputable def rate : ℝ := eRate.toReal

noncomputable def Bad {Input : Type} (cache : Cache Input) : Prop :=
  ∃ mark : MarkedLabel, (cache.entries.length : ℝ)*rate+2^47 < count mark cache

theorem probability_matches (mark : MarkedLabel) :
    Pr[Matches mark | ($ᵗ Output : ProbComp Output)] = eRate := digest_mark_joint_exact mark

theorem eRate_finite : eRate ≠ ⊤ := by unfold eRate acceptance;finiteness

theorem eRate_le_one : eRate ≤ 1 := by
  rw [← probability_matches (0,fun _ => 0)]
  exact probEvent_le_one

theorem rate_value : rate =
    (102487135108565451847281345 : ℝ)/(158456325028528675187087900672*2^59) := by
  norm_num [rate,eRate,acceptance,ENNReal.toReal_div,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,ENNReal.toReal_ofReal]

theorem rate_nonneg : 0≤rate := ENNReal.toReal_nonneg

theorem rate_le_one : rate≤1 := by
  exact (ENNReal.toReal_mono (by finiteness) eRate_le_one).trans_eq ENNReal.toReal_one

theorem count_insert {Input : Type} [DecidableEq Input] (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (output : Output) (fresh : lookup cache input=none) :
    count mark (insert cache input output fresh) = count mark cache + if Matches mark output then 1 else 0 := by
  by_cases h : Matches mark output <;> simp [count,insert,List.countP_cons,h]

theorem insert_length {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input)
    (output : Output) (fresh : lookup cache input=none) :
    (insert cache input output fresh).entries.length=cache.entries.length+1 := rfl

theorem not_bad_empty {Input : Type} : ¬Bad (empty : Cache Input) := by
  rintro ⟨mark,h⟩
  norm_num [empty,count] at h

/-- Query choice may use arbitrary private random coins and the entire
ordered response history. Repeated inputs reuse the cached response and
never insert a record or advance the fresh-query count. The computation
stops at the first exceptional cache, across all marks and all prefixes. -/
noncomputable def run {Input : Type} [DecidableEq Input]
    (policy : History Input → ProbComp Input) : Nat → History Input → Cache Input → ProbComp Bool
  | 0,_,cache => pure (decide (Bad cache))
  | steps+1,history,cache =>
    if Bad cache then pure true else do
      let input ← policy history
      match fresh : lookup cache input with
      | some output => run policy steps ((input,output)::history) cache
      | none => do
          let output ← ($ᵗ Output : ProbComp Output)
          run policy steps ((input,output)::history) (insert cache input output fresh)

end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.count_insert
#print axioms SigGolfResearch.Gate6.Cache.probability_matches
