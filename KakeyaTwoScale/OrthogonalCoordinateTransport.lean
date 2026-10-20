module
public import KakeyaTwoScale.CylinderRotation
public import Mathlib.Analysis.InnerProductSpace.NormDet

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- An orthogonal Euclidean map expressed in ordinary coordinate functions.
This preserves Euclidean geometry, not the coordinate space's sup norm. -/
def orthogonalCoordinates {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.trans
    (R.toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)))

theorem orthogonalCoordinates_apply {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ) :
    orthogonalCoordinates R x = WithLp.ofLp (R (WithLp.toLp 2 x)) := rfl

theorem orthogonalCoordinates_symm {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (orthogonalCoordinates R).symm = orthogonalCoordinates R.symm := by
  ext x i
  rfl

/-- The coordinate determinant has absolute value one, by algebraic conjugacy.
No assertion about preservation of the Pi sup norm is used. -/
theorem orthogonalCoordinates_abs_det {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    |(orthogonalCoordinates R).toContinuousLinearMap.det| = 1 := by
  let b := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hd := LinearMap.det_conj R.toLinearEquiv.toLinearMap b.toLinearEquiv
  have hn := R.toLinearIsometry.normDet_eq_one
  rw [LinearMap.normDet_eq_abs_det] at hn
  change |LinearMap.det (b.toLinearEquiv.toLinearMap.comp
    (R.toLinearEquiv.toLinearMap.comp b.symm.toLinearEquiv.toLinearMap))| = 1
  exact (congrArg abs hd).trans hn

theorem orthogonalCoordinates_first_axis {n : ℕ}
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    orthogonalCoordinates R (Pi.single 0 1) = WithLp.ofLp (R (EuclideanSpace.single 0 1)) := rfl

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orthogonalCoordinates_abs_det
#print axioms KakeyaTwoScale.orthogonalCoordinates_first_axis
