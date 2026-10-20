module
public import KakeyaTwoScale.ChartIntersectionCount
public import KakeyaTwoScale.MeasurablePolynomialCrossings

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The chart cofactor integral equals the number of geometric intersections.
Injectivity is required only on the measured parameter subset. -/
theorem chart_cofactor_integral_eq_crossings {n : ℕ}
    (φ : (Fin n → ℝ) → (Fin (n+1) → ℝ))
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hinj : InjOn φ S) :
    AEMeasurable (chartLineCount (φ '' S)) volume ∧
      (∫⁻ x in S, ENNReal.ofReal |chartCofactor (fderiv ℝ φ x) (Pi.single 0 1)|) =
        ∫⁻ y, chartLineCount (φ '' S) y := by
  let f := fun x => transverseProjection n (φ x)
  have hcf : ContDiffOn ℝ 1 f U :=
    (transverseProjection n).contDiff.comp_contDiffOn hφ
  obtain ⟨hm, he⟩ := open_c1_jacobian_multiplicity f U hU hcf S hS hSU
  have hc : actualFiberCount f S = chartLineCount (φ '' S) :=
    funext (chart_projection_fiber_count φ S hinj)
  rw [hc] at hm he
  refine ⟨hm, ?_⟩
  rw [← he]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hS] with x hx
  rw [chartCofactor_first_axis]
  have hd := ((hφ.differentiableOn (by simp) x (hSU hx)).differentiableAt
    (hU.mem_nhds (hSU hx))).hasFDerivAt
  have hproj := ((transverseProjection n).hasFDerivAt.comp x hd).fderiv
  change ENNReal.ofReal |((transverseProjection n).comp (fderiv ℝ φ x)).det| =
    ENNReal.ofReal |(fderiv ℝ (fun x => transverseProjection n (φ x)) x).det|
  simp only [Function.comp_def] at hproj
  rw [hproj]

/-- An actual chart in a nonzero polynomial zero set has a degree-controlled
cofactor integral whenever its transverse projection lies in the measurable base D.
No pointwise finite-fiber, regular-polynomial, immersion, or area-bound premise is used. -/
theorem polynomial_chart_cofactor_budget {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (φ : (Fin n → ℝ) → (Fin (n+1) → ℝ))
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hinj : InjOn φ S) (hzero : ∀ x ∈ S, MvPolynomial.eval (φ x) P = 0)
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D)
    (hsupport : ∀ x ∈ S, transverseProjection n (φ x) ∈ D) :
    (∫⁻ x in S, ENNReal.ofReal |chartCofactor (fderiv ℝ φ x) (Pi.single 0 1)|) ≤
      (P.totalDegree : ℝ≥0∞) * volume D := by
  rw [(chart_cofactor_integral_eq_crossings φ U hU hφ S hS hSU hinj).2]
  have hp (y : Fin n → ℝ) : chartLineCount (φ '' S) y ≤
      D.indicator (coordinateCrossingCount P) y := by
    by_cases hy : y ∈ D
    · rw [Set.indicator_of_mem hy]
      apply ENat.toENNReal_mono
      apply Set.encard_mono
      intro t ht
      obtain ⟨x, hx, he⟩ := ht
      change MvPolynomial.eval (Fin.cons t y) P = 0
      rw [← he]
      exact hzero x hx
    · rw [Set.indicator_of_notMem hy]
      have he : {t : ℝ | Fin.cons t y ∈ φ '' S} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        obtain ⟨x, hx, he⟩ := ht
        have hs := hsupport x hx
        rw [he] at hs
        exact hy hs
      unfold chartLineCount
      rw [he]
      simp
  calc
    (∫⁻ y, chartLineCount (φ '' S) y) ≤
        ∫⁻ y, D.indicator (coordinateCrossingCount P) y := lintegral_mono hp
    _ = ∫⁻ y in D, coordinateCrossingCount P y := lintegral_indicator hD _
    _ ≤ _ := coordinate_crossing_integral_le P hP D

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chart_cofactor_integral_eq_crossings
#print axioms KakeyaTwoScale.polynomial_chart_cofactor_budget
