module
public import KakeyaTwoScale.OrthogonalPolynomialCrossings
public import KakeyaTwoScale.ClosedFiberCountMeasurable

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The count in the projection budget is genuinely Borel measurable,
including infinite fibers. No nonzero-polynomial assumption is needed here. -/
theorem measurable_coordinate_crossing_count {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) : Measurable (coordinateCrossingCount P) := by
  have hc : Continuous (fun z : (Fin n→ℝ)×ℝ => (Fin.cons z.2 z.1 : Fin (n+1)→ℝ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_snd
    · exact (continuous_apply j).comp continuous_fst
  exact measurable_continuous_fiber_count _ (P.continuous_eval.comp hc)

/-- Orthogonal-coordinate crossing counts have the same Borel property. -/
theorem measurable_frame_crossing_count {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    Measurable (frameCrossingCount P R) := by
  have he : frameCrossingCount P R=coordinateCrossingCount
      (polynomialLinearPullback R.toContinuousLinearEquiv.toContinuousLinearMap P) := by
    funext y
    exact frameCrossingCount_eq_coordinate P R y
  rw [he]
  exact measurable_coordinate_crossing_count _

/-- Over a finite-volume transverse base the actual crossing integral is
finite. This is a measurable projection count, not yet directed surface area. -/
theorem frame_crossing_integral_lt_top {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (D : Set (Fin n→ℝ)) (hD : volume D<∞) :
    (∫⁻ y in D, frameCrossingCount P R y)<∞ := by
  apply (frame_crossing_integral_le P hP R D).trans_lt
  exact ENNReal.mul_lt_top (by simp) hD

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurable_coordinate_crossing_count
#print axioms KakeyaTwoScale.measurable_frame_crossing_count
#print axioms KakeyaTwoScale.frame_crossing_integral_lt_top
