module
public import KakeyaTwoScale.MollifiedCoefficientArea

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Normalize the integral of actual seminorms. Zero total mass gives the zero
seminorm by real division; quantitative applications prove positive mass. -/
def finiteSeminormAverage {X E : Type*} [MeasurableSpace X]
    [AddCommGroup E] [Module ℝ E] (μ : Measure X)
    (s : X → Seminorm ℝ E) (hi : ∀ v, Integrable (fun q => s q v) μ) : Seminorm ℝ E :=
  Seminorm.of (fun v => (∫ q, s q v ∂μ) / μ.real Set.univ)
    (by
      intro v w
      have h := integral_mono (hi (v+w)) ((hi v).add (hi w)) (fun q => map_add_le_add (s q) v w)
      simp only [Pi.add_apply] at h
      rw [integral_add (hi v) (hi w)] at h
      simpa only [add_div,Measure.real] using
        div_le_div_of_nonneg_right h (show 0 ≤ μ.real Set.univ from ENNReal.toReal_nonneg))
    (by
      intro c v
      simp only [map_smul_eq_mul,integral_const_mul,mul_div_assoc])

/-- Averaging preserves a uniform norm bound without any factor depending on
measure size, parameter center or smoothing radius. -/
theorem finiteSeminormAverage_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : 0 < μ.real Set.univ)
    (s : X → Seminorm ℝ E) (hi : ∀ v, Integrable (fun q => s q v) μ)
    (C : ℝ) (hb : ∀ q v, s q v ≤ C * ‖v‖) (v : E) :
    finiteSeminormAverage μ s hi v ≤ C * ‖v‖ := by
  change (∫ q, s q v ∂μ) / μ.real Set.univ ≤ _
  apply (div_le_iff₀ hμ).mpr
  have hh := integral_mono (hi v) (integrable_const (C * ‖v‖)) (fun q => hb q v)
  simpa only [integral_const,smul_eq_mul,mul_comm] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finiteSeminormAverage
#print axioms KakeyaTwoScale.finiteSeminormAverage_le
