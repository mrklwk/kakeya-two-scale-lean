module
public import KakeyaTwoScale.FiniteSeminormAverage

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

section ActualAverage
variable {d n D : ℕ}
variable (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
variable (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
variable (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
variable (r : ℝ) (hr : 0 ≤ r)
variable (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)

include hdegree hreg

/-- Derived integrability on any finite intrinsic coefficient measure. -/
theorem integrable_metricCoefficientArea
    (μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) [IsFiniteMeasure μ]
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    Integrable (fun q => coefficientAreaSeminorm m hm U hU r hr hbound (metricCoefficient q) v) μ := by
  obtain ⟨hf,hb⟩ := metric_coefficient_area_measurable_bounded m hm hdegree U hU hreg r hr hbound v
  exact (integrable_const _).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- The literal spherical average, now packaged with proved seminorm laws. -/
def mollifiedAreaSeminorm (ε : ℝ) (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin (n+1))) :=
  finiteSeminormAverage
    (((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).restrict (ball p ε))
    (fun q => coefficientAreaSeminorm m hm U hU r hr hbound (metricCoefficient q))
    (fun v => integrable_metricCoefficientArea m hm hdegree U hU hreg r hr hbound _ v)

theorem mollifiedAreaSeminorm_apply (ε : ℝ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (v : EuclideanSpace ℝ (Fin (n+1))) :
    mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p v =
      mollifiedCoefficientArea m hm U hU r hr hbound ε p v := by
  change (∫ q in ball p ε, coefficientAreaSeminorm m hm U hU r hr hbound (metricCoefficient q) v
    ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) /
    (((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).restrict (ball p ε)).real univ = _
  simp only [mollifiedCoefficientArea,sphereCapAverage,Measure.real,Measure.restrict_apply_univ]

/-- The same uniform norm bound survives averaging, independently of the center
and every positive cap radius. No inverse-cap-mass loss remains. -/
theorem mollifiedAreaSeminorm_le (ε : ℝ) (hε : 0 < ε)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (v : EuclideanSpace ℝ (Fin (n+1))) :
    mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p v ≤
      ((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal * ‖v‖ := by
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have hmass : 0 < (μ.restrict (ball p ε)).real univ := by
    rw [Measure.real,Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos (isOpen_ball.measure_ne_zero μ (nonempty_ball.mpr hε)) (measure_ne_top μ _)
  apply finiteSeminormAverage_le _ hmass
  intro q w
  exact coefficientAreaSeminorm_uniform_bound m hm hdegree U hU r hr hbound (metricCoefficient q) w

/-- Uniform directional Lipschitz control, including degenerate and zero seminorms. -/
theorem mollifiedAreaSeminorm_sub_le (ε : ℝ) (hε : 0 < ε)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (v w : EuclideanSpace ℝ (Fin (n+1))) :
    ‖mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p v -
      mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p w‖ ≤
      ((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal * ‖v-w‖ :=
  ((mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p).norm_sub_map_le_sub v w).trans
    (mollifiedAreaSeminorm_le m hm hdegree U hU hreg r hr hbound ε hε p (v-w))

end ActualAverage
end KakeyaTwoScale
#print axioms KakeyaTwoScale.integrable_metricCoefficientArea
#print axioms KakeyaTwoScale.mollifiedAreaSeminorm
#print axioms KakeyaTwoScale.mollifiedAreaSeminorm_apply
#print axioms KakeyaTwoScale.mollifiedAreaSeminorm_le
#print axioms KakeyaTwoScale.mollifiedAreaSeminorm_sub_le
