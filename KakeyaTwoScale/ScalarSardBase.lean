module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology
noncomputable section
namespace KakeyaTwoScale

/-- Genuine scalar Sard in dimension one, on an arbitrary subset of the
line. The critical image is proved null, not a supplied hypothesis. -/
theorem scalar_critical_values_null (f : ℝ → ℝ) (s : Set ℝ)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    volume (f '' {x | x ∈ s ∧ fderiv ℝ f x=0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (fun x hx => (hf x hx.1).hasFDerivAt.hasFDerivWithinAt)
  intro x hx
  rw [hx.2]
  simp

/-- Every nonempty open interval contains a value regular for the actual
scalar function on the specified set. -/
theorem scalar_exists_regular_value (f : ℝ → ℝ) (s : Set ℝ)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ x ∈ s, f x=t → fderiv ℝ f x ≠ 0 := by
  classical
  have hn := scalar_critical_values_null f s hf
  have hnot : ¬Ioo a b ⊆ f '' {x | x ∈ s ∧ fderiv ℝ f x=0} := by
    intro h
    have he := measure_mono (μ := volume) h
    rw [hn] at he
    exact (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hab)).not_ge he
  obtain ⟨t,ht,hbad⟩ := Set.not_subset.mp hnot
  exact ⟨t,ht,fun x hx he hd => hbad ⟨x,⟨hx,hd⟩,he⟩⟩

/-- Countably many actual differentiable scalar functions admit a common
regular value in every nonempty interval. -/
theorem countable_scalar_exists_common_regular_value {ι : Type*} [Countable ι]
    (f : ι → ℝ → ℝ) (s : ι → Set ℝ)
    (hf : ∀ i x, x ∈ s i → DifferentiableAt ℝ (f i) x)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ i x, x ∈ s i → f i x=t → fderiv ℝ (f i) x ≠ 0 := by
  classical
  let bad := fun i => f i '' {x | x ∈ s i ∧ fderiv ℝ (f i) x=0}
  have hnull : volume (⋃ i, bad i)=0 := by
    apply measure_iUnion_null
    intro i
    exact scalar_critical_values_null (f i) (s i) (hf i)
  have hnot : ¬Ioo a b ⊆ ⋃ i, bad i := by
    intro h
    have he := measure_mono (μ := volume) h
    rw [hnull] at he
    exact (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hab)).not_ge he
  obtain ⟨t,ht,hbad⟩ := Set.not_subset.mp hnot
  refine ⟨t,ht,fun i x hx he hd => ?_⟩
  exact hbad (mem_iUnion.mpr ⟨i,⟨x,⟨hx,hd⟩,he⟩⟩)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.scalar_critical_values_null
#print axioms KakeyaTwoScale.scalar_exists_regular_value
#print axioms KakeyaTwoScale.countable_scalar_exists_common_regular_value
