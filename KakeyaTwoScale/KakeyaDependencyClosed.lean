module
public import KakeyaTwoScale.DependencyClosedZahl
public import KakeyaTwoScale.KakeyaPublished

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- September 10 two-scale upper-Minkowski lower bound, with the actual
published Zahl-cylinder input discharged by the local formal proof chain. -/
theorem kakeya_upperMinkowski_lower (N : ℕ) (hN : 4≤N)
    (K : Set (EuclideanSpace ℝ (Fin N))) (hbounded : Bornology.IsBounded K)
    (hK : ∀u : EuclideanSpace ℝ (Fin N), ‖u‖=1 → ∃b,
      ∀t∈Set.Icc (0:ℝ) 1, b+t • u∈K) :
    (597/1000:ℝ)*N≤limsup (openBallCoverEntropy K) (nhdsWithin 0 (Set.Ioi 0)) :=
  kakeya_upperMinkowski_lower_of_published_zahl N hN
    (published_zahl_cylinder_estimate N (N/2) (by omega) (by omega)) K hbounded hK

end KakeyaTwoScale
#print axioms KakeyaTwoScale.kakeya_upperMinkowski_lower
