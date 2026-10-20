module
public import KakeyaTwoScale.CoefficientSphereArea

@[expose] public section

open Set MeasureTheory MvPolynomial Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The actual finite localized area seminorm at each coefficient-sphere point.
Boundedness is geometric, and finiteness is derived by the earlier degree budget. -/
def coefficientAreaSeminorm {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (c : CoefficientSphere ι) : Seminorm ℝ (EuclideanSpace ℝ (Fin (n+1))) :=
  polynomialLocalizedAreaSeminorm (coefficientPolynomial m c.val)
    (coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero c))
    (coefficientSphereAtlas m hm c) U hU r hr hbound

theorem coefficientAreaSeminorm_apply {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (c : CoefficientSphere ι) (v : EuclideanSpace ℝ (Fin (n+1))) :
    coefficientAreaSeminorm m hm U hU r hr hbound c v =
      (coefficientSphereArea m hm U hU c (WithLp.ofLp v)).toReal := rfl

/-- Real conversion loses no area: infinity has been ruled out geometrically. -/
theorem coefficientAreaSeminorm_ofReal {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (c : CoefficientSphere ι) (v : EuclideanSpace ℝ (Fin (n+1))) :
    ENNReal.ofReal (coefficientAreaSeminorm m hm U hU r hr hbound c v) =
      coefficientSphereArea m hm U hU c (WithLp.ofLp v) := by
  exact ENNReal.ofReal_toReal (coefficientSphereArea_lt_top m hm U hU r hr hbound c _).ne

/-- Coefficient measurability of the actual finite real area in every direction. -/
theorem measurable_coefficientAreaSeminorm {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    Measurable (fun c => coefficientAreaSeminorm m hm U hU r hr hbound c v) :=
  (measurable_coefficientSphereArea m hm U hU hreg (WithLp.ofLp v)).ennreal_toReal

/-- Uniform real bound, fixed before the coefficient and direction. -/
theorem coefficientAreaSeminorm_uniform_bound {ι : Type*} [Fintype ι] {n D : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (c : CoefficientSphere ι) (v : EuclideanSpace ℝ (Fin (n+1))) :
    coefficientAreaSeminorm m hm U hU r hr hbound c v ≤
      ((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal * ‖v‖ := by
  have ht : ENNReal.ofReal ‖v‖ * ((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (by simp) measure_closedBall_lt_top)).ne
  have hh := ENNReal.toReal_mono ht
    (coefficientSphereArea_uniform_bound m hm hdegree U hU r hr hbound c (WithLp.ofLp v))
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg _)] at hh
  simpa only [coefficientAreaSeminorm_apply,mul_comm] using hh

/-- Actual bounded raw area is integrable against every finite coefficient measure. -/
theorem integrable_coefficientAreaSeminorm {ι : Type*} [Fintype ι] {n D : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (μ : Measure (CoefficientSphere ι)) [IsFiniteMeasure μ]
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    Integrable (fun c => coefficientAreaSeminorm m hm U hU r hr hbound c v) μ := by
  apply (integrable_const (((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal * ‖v‖)).mono'
    (measurable_coefficientAreaSeminorm m hm U hU hreg r hr hbound v).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro c
  rw [coefficientAreaSeminorm_apply,Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact coefficientAreaSeminorm_uniform_bound m hm hdegree U hU r hr hbound c v

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coefficientAreaSeminorm_ofReal
#print axioms KakeyaTwoScale.measurable_coefficientAreaSeminorm
#print axioms KakeyaTwoScale.coefficientAreaSeminorm_uniform_bound
#print axioms KakeyaTwoScale.integrable_coefficientAreaSeminorm
