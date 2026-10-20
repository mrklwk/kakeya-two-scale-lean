module
public import KakeyaTwoScale.KakeyaDependencyClosed

open Filter Metric
noncomputable section
namespace PalomarKakeya

/-- Least cardinality of a finite cover by open Euclidean radius-r balls. -/
@[expose] public def coverNumber {N : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin N))) (r : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ C : Finset (EuclideanSpace ℝ (Fin N)),
    K ⊆ ⋃ c ∈ C, ball c r ∧ C.card ≤ m}

/-- Normalized logarithmic cover count, with the empty-set convention. -/
@[expose] public def coverEntropy {N : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin N))) (r : ℝ) : ℝ :=
  Real.log (max 1 (coverNumber K r : ℝ)) / (-Real.log r)

/-- Proven version of the independently stated Challenge theorem. -/
public theorem upperMinkowski_lower (N : ℕ) (hN : 4 ≤ N)
    (K : Set (EuclideanSpace ℝ (Fin N))) (hbounded : Bornology.IsBounded K)
    (hK : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 → ∃ b,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, b + t • u ∈ K) :
    (597 / 1000 : ℝ) * N ≤
      limsup (coverEntropy K) (nhdsWithin 0 (Set.Ioi 0)) := by
  exact KakeyaTwoScale.kakeya_upperMinkowski_lower N hN K hbounded hK

end PalomarKakeya
#print axioms PalomarKakeya.upperMinkowski_lower
