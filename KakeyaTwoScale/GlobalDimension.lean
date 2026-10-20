module
public import KakeyaTwoScale.BoundedAdmissibility
public import KakeyaTwoScale.RealScaleDimension
public import KakeyaTwoScale.GlobalScaleAssembly

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- The endpoint accepts any fixed fine/coarse envelopes controlled by every
admissible cover exponent. In particular, fixed enlargement and Jacobian
factors do not require identifying the envelopes with unit-radius thickenings. -/
theorem upperBoxDimension_lower_of_envelopes (n : ℕ) (hn : 4≤n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Bornology.IsBounded K)
    (fine coarse : ℕ → ℝ)
    (hupper : ∀ D : ℝ, 0≤D → DyadicCoverGrowth K D → NeighborhoodUpper n D fine coarse)
    (htransfer : BroadTransfer n (n/2:ℕ) fine ∨ NarrowTransfer n (n/2:ℕ) fine coarse) :
    (597/1000:ℝ)*n ≤ upperBoxDimension K := by
  apply le_csInf (bounded_has_dyadicCoverGrowth hK)
  intro D hD
  exact endpoint_nat_of_volume_dichotomy n hn D fine coarse
    (hupper D hD.1 hD.2) htransfer

/-- The same bound in the usual normalized-log covering definition, with
radii tending to zero through every positive real value. -/
theorem upperMinkowski_lower_of_envelopes (n : ℕ) (hn : 4≤n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Bornology.IsBounded K)
    (fine coarse : ℕ → ℝ)
    (hupper : ∀ D : ℝ, 0≤D → DyadicCoverGrowth K D → NeighborhoodUpper n D fine coarse)
    (htransfer : BroadTransfer n (n/2:ℕ) fine ∨ NarrowTransfer n (n/2:ℕ) fine coarse) :
    (597/1000:ℝ)*n ≤ limsup (openBallCoverEntropy K) (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [← upperBoxDimension_eq_radius_limsup hK]
  exact upperBoxDimension_lower_of_envelopes n hn K hK fine coarse hupper htransfer

end KakeyaTwoScale
#print axioms KakeyaTwoScale.upperBoxDimension_lower_of_envelopes
#print axioms KakeyaTwoScale.upperMinkowski_lower_of_envelopes
