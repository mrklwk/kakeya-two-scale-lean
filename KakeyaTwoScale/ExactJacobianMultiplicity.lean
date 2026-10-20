module
public import KakeyaTwoScale.ExactImageMultiplicity
public import KakeyaTwoScale.WithinRegularPartition

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Function
noncomputable section
namespace KakeyaTwoScale

/-- Literal extended cardinality of a restricted fiber. -/
def actualFiberCount {α β : Type*} (f : α → β) (S : Set α) (z : β) : ℝ≥0∞ :=
  ({x | x ∈ S ∧ f x = z} : Set α).encard.toENNReal

/-- A null critical image, proved from the actual derivative, not assumed. -/
theorem critical_image_volume_zero {m : ℕ}
    (f : (Fin m → ℝ) → (Fin m → ℝ))
    (Df : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)))
    (S : Set (Fin m → ℝ))
    (hf : ∀ x ∈ S, HasFDerivWithinAt f (Df x) S x) :
    volume (f '' {x | x ∈ S ∧ (Df x).det = 0}) = 0 := by
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (fun x hx => (hf x hx.1).mono (fun _ h => h.1)) (fun _ hx => hx.2)

/-- Exact area formula on a measurable set. The regular locus need only be
measurable; neither a global derivative nor bounded multiplicity is assumed.
Full multiplicity is AE measurable, including potentially infinite critical fibers. -/
theorem exact_jacobian_multiplicity_within {m : ℕ}
    (f : (Fin m → ℝ) → (Fin m → ℝ))
    (Df : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)))
    (S : Set (Fin m → ℝ)) (hS : MeasurableSet S)
    (hf : ∀ x ∈ S, HasFDerivWithinAt f (Df x) S x)
    (hR : MeasurableSet {x | x ∈ S ∧ (Df x).det ≠ 0}) :
    AEMeasurable (actualFiberCount f S) volume ∧
      (∫⁻ x in S, ENNReal.ofReal |(Df x).det|) = ∫⁻ z, actualFiberCount f S z := by
  classical
  let R : Set (Fin m → ℝ) := {x | x ∈ S ∧ (Df x).det ≠ 0}
  obtain ⟨P, hP, hd, hunion, hinj⟩ := regular_injective_partition_within f Df hR
    (fun x hx => (hf x hx.1).mono (fun _ h => h.1)) (fun _ hx => hx.2)
  change (⋃ i, P i) = R at hunion
  have hsub (i : ℕ) : P i ⊆ R := by
    intro x hx
    rw [← hunion]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hder (i : ℕ) : ∀ x ∈ P i, HasFDerivWithinAt f (Df x) (P i) x := by
    intro x hx
    exact (hf x (hsub i hx).1).mono (fun y hy => (hsub i hy).1)
  have him (i : ℕ) : MeasurableSet (f '' P i) :=
    measurable_image_of_fderivWithin (hP i) (hder i) (hinj i)
  have hcount (z) : actualFiberCount f R z =
      ∑' i, (f '' P i).indicator (fun _ => (1 : ℝ≥0∞)) z := by
    rw [image_indicator_tsum_eq_fiber_count f P hd hinj, hunion]
    rfl
  have hmeas : Measurable (actualFiberCount f R) := by
    have he : actualFiberCount f R = fun z =>
        ∑' i, (f '' P i).indicator (fun _ => (1 : ℝ≥0∞)) z := funext hcount
    rw [he]
    exact Measurable.tsum (fun i => measurable_const.indicator (him i))
  have hae : actualFiberCount f S =ᶠ[ae volume] actualFiberCount f R := by
    have hcrit : ∀ᵐ z ∂volume, z ∉ f '' {x | x ∈ S ∧ (Df x).det = 0} := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using critical_image_volume_zero f Df S hf
    filter_upwards [hcrit] with z hz
    apply congrArg ENat.toENNReal
    apply congrArg Set.encard
    ext x
    constructor
    · rintro ⟨hx, he⟩
      exact ⟨⟨hx, fun hd => hz ⟨x, ⟨hx, hd⟩, he⟩⟩, he⟩
    · rintro ⟨hx, he⟩
      exact ⟨hx.1, he⟩
  refine ⟨hmeas.aemeasurable.congr hae.symm, ?_⟩
  have hzero : (∫⁻ x in S, ENNReal.ofReal |(Df x).det|) =
      ∫⁻ x in R, ENNReal.ofReal |(Df x).det| := by
    rw [← lintegral_indicator hS, ← lintegral_indicator hR]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ S <;> by_cases hz : (Df x).det = 0 <;> simp [hx, hz]
  rw [hzero, ← hunion, lintegral_iUnion hP hd]
  calc
    (∑' i, ∫⁻ x in P i, ENNReal.ofReal |(Df x).det|) = ∑' i, volume (f '' P i) := by
      apply tsum_congr
      intro i
      exact lintegral_abs_det_fderiv_eq_addHaar_image volume (hP i) (hder i) (hinj i)
    _ = ∫⁻ z, actualFiberCount f R z := by
      rw [countable_measure_sum_eq_fiber_integral volume f P hd hinj him, hunion]
      rfl
    _ = _ := lintegral_congr_ae hae.symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.critical_image_volume_zero
#print axioms KakeyaTwoScale.exact_jacobian_multiplicity_within
