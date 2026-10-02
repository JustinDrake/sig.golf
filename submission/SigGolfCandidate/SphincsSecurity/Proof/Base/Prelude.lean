import SigGolfCandidate.SphincsSecurity.Compat
import Batteries.Data.Fin.Coding
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.BitVec
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.DeriveFintype
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.ProgramLogic.Relational.ProgrammingOracle
import VCVio.ProgramLogic.Relational.Quantitative


namespace SphincsSecurity.Concrete

theorem fold_node_bound (height level index : Nat) (hlevel : level < height) (hindex : index < 2 ^ height) :
    2 ^ (level + 1) * (index / 2 ^ (level + 1) + 1) ≤ 2 ^ height := by
  have hpow : (2 : Nat) ^ height = 2 ^ (level + 1) * 2 ^ (height - (level + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt hlevel)]
  have hdiv : index / 2 ^ (level + 1) < 2 ^ (height - (level + 1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [hpow, Nat.mul_comm] using hindex
  exact (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hdiv)).trans_eq hpow.symm

end SphincsSecurity.Concrete
