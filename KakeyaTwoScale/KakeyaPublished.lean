module
public import KakeyaTwoScale.KakeyaConditional
public import KakeyaTwoScale.PublishedZahlAdapter

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- The actual upper-Minkowski endpoint directly from the audited published
flat-cylinder estimate. No capsule convention is left as an unproved adapter. -/
theorem kakeya_upperMinkowski_lower_of_published_zahl (N : ℕ) (hN : 4≤N)
    (Z : PublishedZahlCylinderEstimate N (N/2))
    (K : Set (EuclideanSpace ℝ (Fin N))) (hbounded : Bornology.IsBounded K)
    (hK : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖=1 → ∃ b,
      ∀ t ∈ Set.Icc (0:ℝ) 1, b+t • u ∈ K) :
    (597/1000:ℝ)*N ≤ limsup (openBallCoverEntropy K) (nhdsWithin 0 (Set.Ioi 0)) :=
  kakeya_upperMinkowski_lower_of_zahl N hN
    (published_zahl_implies_capsule N (N/2) Z) K hbounded hK

end KakeyaTwoScale
#print axioms KakeyaTwoScale.kakeya_upperMinkowski_lower_of_published_zahl
