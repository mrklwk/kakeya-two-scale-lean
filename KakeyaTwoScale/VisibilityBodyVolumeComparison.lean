module
public import KakeyaTwoScale.UniformSeminormFamilies
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
namespace KakeyaTwoScale

/-- Quantitative volume stability follows from body inclusions, without strict
positivity of either seminorm on nonzero vectors. -/
theorem visibilityBody_volume_comparison {n : ℕ}
    (p q : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : ∀ v, |p v - q v| ≤ δ * ‖v‖) :
    ENNReal.ofReal (((1+δ)⁻¹)^n) * volume (seminormVisibilityBody p) ≤ volume (seminormVisibilityBody q) ∧
    volume (seminormVisibilityBody q) ≤ ENNReal.ofReal ((1+δ)^n) * volume (seminormVisibilityBody p) := by
  obtain ⟨hi,ho⟩ := visibilityBody_comparison p q δ hδ he
  constructor
  · have h := measure_mono (μ := volume) hi
    simpa only [Measure.addHaar_smul_of_nonneg volume (by positivity : 0 ≤ (1+δ)⁻¹), finrank_euclideanSpace, Fintype.card_fin] using h
  · have h := measure_mono (μ := volume) ho
    simpa only [Measure.addHaar_smul_of_nonneg volume (by positivity : 0 ≤ 1+δ), finrank_euclideanSpace, Fintype.card_fin] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.visibilityBody_volume_comparison
