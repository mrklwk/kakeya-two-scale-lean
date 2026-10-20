module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.Bounded

/-!+# Upper Minkowski dimension of bounded Kakeya sets

For N ≥ 4, every bounded subset of Euclidean N-space containing a translated
closed unit segment in every direction has ordinary upper Minkowski dimension
at least 597N/1000. The limsup below is over all positive radii tending to zero.
There is no measurability, closedness, or analytic-estimate hypothesis.
This is the September 10, 2026 argument of Mark Lewko. The deliberately missing
proof in this statement-only module is supplied independently in Solution.
-/

open Filter Metric
noncomputable section
namespace PalomarKakeya

/-- Least cardinality of a finite cover by open Euclidean radius-r balls.
For bounded K and r>0 such covers exist; centers may be anywhere in the space. -/
@[expose] public def coverNumber {N : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin N))) (r : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ C : Finset (EuclideanSpace ℝ (Fin N)),
    K ⊆ ⋃ c ∈ C, ball c r ∧ C.card ≤ m}

/-- Normalized logarithmic cover count. The max supplies the empty-set convention. -/
@[expose] public def coverEntropy {N : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin N))) (r : ℝ) : ℝ :=
  Real.log (max 1 (coverNumber K r : ℝ)) / (-Real.log r)

/-- The ordinary upper Minkowski lower bound for bounded Kakeya sets. -/
public theorem upperMinkowski_lower (N : ℕ) (hN : 4 ≤ N)
    (K : Set (EuclideanSpace ℝ (Fin N))) (hbounded : Bornology.IsBounded K)
    (hK : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → ∃ b,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, b + t • u ∈ K) :
    (597 / 1000 : ℝ) * N ≤
      limsup (coverEntropy K) (nhdsWithin 0 (Set.Ioi 0)) := by
  sorry

end PalomarKakeya
