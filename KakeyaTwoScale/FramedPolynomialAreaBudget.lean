module
public import KakeyaTwoScale.FramedHypersurfaceArea

@[expose] public section

open MvPolynomial MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Original-polynomial degree budget on any Borel region whose actual framed
projection lies in D. The SAME atlas is localized, and the degree is paid once. -/
theorem polynomial_framed_region_budget {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D)
    (hsupport : ∀ x ∈ {x | eval x P = 0} ∩ K,
      transverseProjection n ((orthogonalCoordinates R).symm x) ∈ D) :
    (A.restrict K hK).directionalArea (orthogonalCoordinates R (Pi.single 0 1)) ≤
      (P.totalDegree : ℝ≥0∞) * volume D := by
  rw [(A.restrict K hK).frame_identity R]
  have hp (y : Fin n → ℝ) : framedLineCount ({x | eval x P = 0} ∩ K) R y ≤
      D.indicator (frameCrossingCount P R) y := by
    by_cases hy : y ∈ D
    · rw [Set.indicator_of_mem hy]
      apply ENat.toENNReal_mono
      apply Set.encard_mono
      intro t ht
      exact ht.1
    · rw [Set.indicator_of_notMem hy]
      have he : {t : ℝ | orthogonalCoordinates R (Fin.cons t y) ∈ {x | eval x P = 0} ∩ K} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        have hs := hsupport _ ht
        rw [(orthogonalCoordinates R).symm_apply_apply] at hs
        exact hy hs
      unfold framedLineCount
      rw [he]
      simp
  calc
    (∫⁻ y, framedLineCount ({x | eval x P = 0} ∩ K) R y) ≤
        ∫⁻ y, D.indicator (frameCrossingCount P R) y := lintegral_mono hp
    _ = ∫⁻ y in D, frameCrossingCount P R y := lintegral_indicator hD _
    _ ≤ _ := frame_crossing_integral_le P hP R D

/-- Every transverse cylinder in every frame has the same original degree budget. -/
theorem polynomial_frame_cylinder_budget {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D) :
    (A.restrict ((fun x => transverseProjection n ((orthogonalCoordinates R).symm x)) ⁻¹' D)
      (hD.preimage ((transverseProjection n).measurable.comp (orthogonalCoordinates R).symm.continuous.measurable))).directionalArea
      (orthogonalCoordinates R (Pi.single 0 1)) ≤ (P.totalDegree : ℝ≥0∞) * volume D := by
  apply polynomial_framed_region_budget P hP A R _ _ D hD
  intro x hx
  exact hx.2

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_framed_region_budget
#print axioms KakeyaTwoScale.polynomial_frame_cylinder_budget
