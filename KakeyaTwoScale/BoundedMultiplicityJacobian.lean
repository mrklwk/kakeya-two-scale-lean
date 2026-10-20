module
public import KakeyaTwoScale.CountableImageMultiplicity

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Function
noncomputable section
namespace KakeyaTwoScale

/-- Actual Jacobian integral bound from a bound on regular fibers only.
Singular fibers may be infinite: their Jacobian is zero, so no Sard premise is used. -/
theorem regular_fiber_jacobian_bound {m : ℕ}
    (f : (Fin m → ℝ) → (Fin m → ℝ))
    (Df : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)))
    (hcDf : Continuous Df) (hf : ∀ x, HasFDerivAt f (Df x) x)
    {S : Set (Fin m → ℝ)} (hS : IsCompact S) (N : ℕ)
    (hmult : ∀ z, ({x | x ∈ S ∧ (Df x).det ≠ 0 ∧ f x=z} : Set (Fin m → ℝ)).encard ≤ N) :
    (∫⁻ x in S, ENNReal.ofReal |(Df x).det|) ≤ (N : ℝ≥0∞) * volume (f '' S) := by
  classical
  let R : Set (Fin m → ℝ) := {x | x ∈ S ∧ (Df x).det ≠ 0}
  have hR : MeasurableSet R := hS.measurableSet.inter
    (isClosed_eq (ContinuousLinearMap.continuous_det.comp hcDf) continuous_const).isOpen_compl.measurableSet
  obtain ⟨P,hP,hd,hunion,hinj⟩ := regular_injective_partition f Df hf hR (fun x hx => hx.2)
  have hsub (i : ℕ) : P i ⊆ R := by
    intro x hx
    rw [← hunion]
    exact mem_iUnion.mpr ⟨i,hx⟩
  have him (i : ℕ) : MeasurableSet (f '' P i) :=
    measurable_image_of_fderivWithin (hP i) (fun x _ => (hf x).hasFDerivWithinAt) (hinj i)
  have hmul : ∀ z, ({x | x ∈ R ∧ f x=z} : Set (Fin m → ℝ)).encard ≤ N := by
    intro z
    simpa only [R, mem_ofPred_eq, and_assoc] using hmult z
  have hzero : (∫⁻ x in S, ENNReal.ofReal |(Df x).det|) =
      ∫⁻ x in R, ENNReal.ofReal |(Df x).det| := by
    rw [← lintegral_indicator hS.measurableSet, ← lintegral_indicator hR]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ S <;> by_cases hd : (Df x).det = 0 <;> simp [R, hx, hd]
  rw [hzero, ← hunion, lintegral_iUnion hP hd]
  calc
    (∑' i, ∫⁻ x in P i, ENNReal.ofReal |(Df x).det|) = ∑' i, volume (f '' P i) := by
      apply tsum_congr
      intro i
      exact lintegral_abs_det_fderiv_eq_addHaar_image volume (hP i)
        (fun x _ => (hf x).hasFDerivWithinAt) (hinj i)
    _ ≤ _ := countable_measure_sum_le_multiplicity volume (fun i => f '' P i) him
      (f '' S) (hS.image (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)).measurableSet
      (fun i => Set.image_mono fun x hx => (hsub i hx).1) N
      (image_piece_multiplicity f P hd R hsub N hmul)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.regular_fiber_jacobian_bound
