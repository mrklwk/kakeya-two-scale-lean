module
public import KakeyaTwoScale.CoefficientAreaIntegrability
public import KakeyaTwoScale.ContinuousCapAverage

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Match the norm-equality coefficient subtype with the metric unit sphere. -/
def metricCoefficient {d : ℕ}
    (c : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) : CoefficientSphere (Fin d) :=
  ⟨c.val,mem_sphere_zero_iff_norm.mp c.property⟩

theorem measurable_metricCoefficient {d : ℕ} : Measurable (@metricCoefficient d) :=
  measurable_subtype_coe.subtype_mk

def mollifiedCoefficientArea {d n : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (ε : ℝ) (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
    (v : EuclideanSpace ℝ (Fin (n+1))) : ℝ :=
  sphereCapAverage ε (fun q => coefficientAreaSeminorm m hm U hU r hr hbound (metricCoefficient q) v) p

/-- Actual raw polynomial area is measurable and uniformly bounded on the
intrinsic metric coefficient sphere. No regularity of atlas choices is used. -/
theorem metric_coefficient_area_measurable_bounded {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    Measurable (fun q => coefficientAreaSeminorm m hm U hU r hr hbound (metricCoefficient q) v) ∧
      ∀ q, ‖coefficientAreaSeminorm m hm U hU r hr hbound (metricCoefficient q) v‖ ≤
        ((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal * ‖v‖ := by
  refine ⟨(measurable_coefficientAreaSeminorm m hm U hU hreg r hr hbound v).comp measurable_metricCoefficient,?_⟩
  intro q
  rw [coefficientAreaSeminorm_apply,Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact coefficientAreaSeminorm_uniform_bound m hm hdegree U hU r hr hbound (metricCoefficient q) v

/-- Genuine coefficient continuity of the actual sphere-mollified area.
The degree, spatial region and radius are fixed before all coefficient centers,
directions and smoothing radii. Raw area continuity is neither assumed nor claimed. -/
theorem continuous_mollifiedCoefficientArea {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2)
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    Continuous (fun p => mollifiedCoefficientArea m hm U hU r hr hbound ε p v) := by
  obtain ⟨hf,hb⟩ := metric_coefficient_area_measurable_bounded m hm hdegree U hU hreg r hr hbound v
  exact continuous_sphereCapAverage ε hε hε2 _ hf _
    (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg v)) hb

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurable_metricCoefficient
#print axioms KakeyaTwoScale.metric_coefficient_area_measurable_bounded
#print axioms KakeyaTwoScale.continuous_mollifiedCoefficientArea
