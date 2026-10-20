module
public import KakeyaTwoScale.MixedCoordinateMeasure

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Removing the crossed coordinate contributes exactly its one-dimensional
mass. This includes n=0, when the transverse product has a single point. -/
theorem lintegral_coordinate_marginal {n : ℕ}
    (μ : Fin (n+1) → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (j : Fin (n+1)) (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (fun i => w (j.succAbove i)) ∂Measure.pi μ) =
      μ j univ * ∫⁻ v, F v ∂Measure.pi (fun i => μ (j.succAbove i)) := by
  have h := (measurePreserving_piFinSuccAbove μ j).lintegral_comp (hF.comp measurable_snd)
  change _ = ∫⁻ z : ℝ × (Fin n → ℝ), F z.2 ∂((μ j).prod (Measure.pi (fun i => μ (j.succAbove i)))) at h
  change (∫⁻ w, F (fun i => w (j.succAbove i)) ∂Measure.pi μ) = _ at h
  rw [h,lintegral_prod (fun z : ℝ × (Fin n → ℝ) => F z.2) (hF.comp measurable_snd).aemeasurable]
  simp only [lintegral_const]
  rw [mul_comm]

/-- Exact two-stage product-measure identity for the mixed transverse base.
All unused coordinate masses are computed by the measures themselves. -/
theorem lintegral_mixed_transverse {n : ℕ}
    (s : Finset (Fin (n+1))) (μ ν : Fin (n+1) → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (j : Fin (n+1)) (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ),
      F (fun i => if j.succAbove i ∈ s then z.2 (j.succAbove i) else z.1 (j.succAbove i))
      ∂((Measure.pi μ).prod (Measure.pi ν))) =
      (Measure.pi (fun i => if i ∈ s then μ i else ν i)) univ *
        (if j ∈ s then ν j else μ j) univ *
        ∫⁻ v, F v ∂Measure.pi (fun i => if j.succAbove i ∈ s then ν (j.succAbove i) else μ (j.succAbove i)) := by
  let a (i : Fin (n+1)) := if i ∈ s then ν i else μ i
  have (i : Fin (n+1)) : IsFiniteMeasure (a i) := by dsimp [a]; split_ifs <;> infer_instance
  have hm : Measurable (fun w : Fin (n+1) → ℝ => F (fun i => w (j.succAbove i))) :=
    hF.comp (measurable_pi_iff.mpr (fun i => measurable_pi_apply (j.succAbove i)))
  rw [lintegral_mixed_coordinates s μ ν _ hm]
  rw [lintegral_coordinate_marginal a j F hF]
  exact (mul_assoc _ _ _).symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.lintegral_coordinate_marginal
#print axioms KakeyaTwoScale.lintegral_mixed_transverse
