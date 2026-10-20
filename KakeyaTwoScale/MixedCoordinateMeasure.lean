module
public import KakeyaTwoScale.CentralCoordinatePaths

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Swapping selected coordinate pairs transports the two independent product
measures to exactly the mixed and complementary product measures. -/
theorem mixed_coordinate_measurePreserving {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (μ ν : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    MeasurePreserving
      (fun z : (ι → ℝ) × (ι → ℝ) =>
        ((fun i => if i ∈ s then z.2 i else z.1 i),
         (fun i => if i ∈ s then z.1 i else z.2 i)))
      ((Measure.pi μ).prod (Measure.pi ν))
      ((Measure.pi (fun i => if i ∈ s then ν i else μ i)).prod
        (Measure.pi (fun i => if i ∈ s then μ i else ν i))) := by
  let a (i : ι) := if i ∈ s then ν i else μ i
  let b (i : ι) := if i ∈ s then μ i else ν i
  have (i : ι) : IsFiniteMeasure (a i) := by dsimp [a]; split_ifs <;> infer_instance
  have (i : ι) : IsFiniteMeasure (b i) := by dsimp [b]; split_ifs <;> infer_instance
  let F (i : ι) (p : ℝ × ℝ) := if i ∈ s then p.swap else p
  have hF (i : ι) : MeasurePreserving (F i) ((μ i).prod (ν i)) ((a i).prod (b i)) := by
    dsimp [F,a,b]
    split_ifs
    · exact Measure.measurePreserving_swap
    · exact MeasurePreserving.id _
  have h1 := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι μ ν).symm
  have h2 := measurePreserving_pi (fun i => (μ i).prod (ν i)) (fun i => (a i).prod (b i)) hF
  have h3 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι a b
  convert h3.comp (h2.comp h1) using 1
  funext z
  apply Prod.ext <;> funext i <;> simp [Function.comp_def,F,MeasurableEquiv.arrowProdEquivProdArrow] <;> split_ifs <;> rfl

/-- Exact marginal integration after swapping coordinate blocks. The unused
coordinates contribute their full product mass, not an assumed uniform factor. -/
theorem lintegral_mixed_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (μ ν : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (F : (ι → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : (ι → ℝ) × (ι → ℝ), F (fun i => if i ∈ s then z.2 i else z.1 i)
      ∂((Measure.pi μ).prod (Measure.pi ν))) =
      (Measure.pi (fun i => if i ∈ s then μ i else ν i)) univ *
        ∫⁻ w, F w ∂(Measure.pi (fun i => if i ∈ s then ν i else μ i)) := by
  let a (i : ι) := if i ∈ s then ν i else μ i
  let b (i : ι) := if i ∈ s then μ i else ν i
  have (i : ι) : IsFiniteMeasure (a i) := by dsimp [a]; split_ifs <;> infer_instance
  have (i : ι) : IsFiniteMeasure (b i) := by dsimp [b]; split_ifs <;> infer_instance
  have h := (mixed_coordinate_measurePreserving s μ ν).lintegral_comp (hF.comp measurable_fst)
  change _ = ∫⁻ z, F z.1 ∂((Measure.pi a).prod (Measure.pi b)) at h
  dsimp only [Function.comp_def] at h
  rw [h,lintegral_prod (fun z : (ι → ℝ) × (ι → ℝ) => F z.1) (hF.comp measurable_fst).aemeasurable]
  simp only [lintegral_const]
  rw [lintegral_mul_const _ hF, mul_comm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mixed_coordinate_measurePreserving
#print axioms KakeyaTwoScale.lintegral_mixed_coordinates
