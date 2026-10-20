module
public import KakeyaTwoScale.MollifiedAreaSeminorm

@[expose] public section

open Set MeasureTheory Metric
noncomputable section
namespace KakeyaTwoScale

/-- A pointwise sum lower bound survives averaging on the same actual cap,
without any loss in its positive finite mass. -/
theorem sphereCapAverage_sum_lower {ι : Type*} [Fintype ι] {d : ℕ}
    (ε : ℝ) (hε : 0 < ε) (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
    (F : ι → sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ)
    (hi : ∀ j, Integrable (F j)
      (((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).restrict (ball p ε)))
    (a : ℝ) (h : ∀ q ∈ ball p ε, a ≤ ∑ j, F j q) :
    a ≤ ∑ j, sphereCapAverage ε (F j) p := by
  classical
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have hmass : 0 < μ.real (ball p ε) :=
    ENNReal.toReal_pos (isOpen_ball.measure_ne_zero μ (nonempty_ball.mpr hε)) (measure_ne_top μ _)
  change a ≤ ∑ j, (∫ q in ball p ε, F j q ∂μ) / μ.real (ball p ε)
  rw [← Finset.sum_div,← integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply (le_div_iff₀ hmass).mpr
  calc
    a * μ.real (ball p ε) = ∫ _q in ball p ε, a ∂μ := by simp [mul_comm]
    _ ≤ _ := integral_mono_ae (integrable_const a)
      (integrable_finsetSum _ (fun j _ => hi j)) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
        exact h q hq)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sphereCapAverage_sum_lower
