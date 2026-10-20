module
public import KakeyaTwoScale.ExactJacobianMultiplicity
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The exact full-fiber area identity for a C1 map on an open domain, localized
to any measurable subset. No extension beyond the domain is constructed or assumed. -/
theorem open_c1_jacobian_multiplicity {m : ℕ}
    (f : (Fin m → ℝ) → (Fin m → ℝ))
    (U : Set (Fin m → ℝ)) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (S : Set (Fin m → ℝ)) (hS : MeasurableSet S) (hSU : S ⊆ U) :
    AEMeasurable (actualFiberCount f S) volume ∧
      (∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ f x).det|) =
        ∫⁻ z, actualFiberCount f S z := by
  have hc : ContinuousOn (fun x => (fderiv ℝ f x).det) U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hreg : IsOpen {x | x ∈ U ∧ (fderiv ℝ f x).det ≠ 0} := by
    exact hc.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have he : {x | x ∈ S ∧ (fderiv ℝ f x).det ≠ 0} =
      S ∩ {x | x ∈ U ∧ (fderiv ℝ f x).det ≠ 0} := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hSU hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
  apply exact_jacobian_multiplicity_within f (fderiv ℝ f) S hS
  · intro x hx
    exact ((hf.differentiableOn (by simp) x (hSU hx)).differentiableAt
      (hU.mem_nhds (hSU hx))).hasFDerivAt.hasFDerivWithinAt
  · rw [he]
    exact hS.inter hreg.measurableSet

end KakeyaTwoScale
#print axioms KakeyaTwoScale.open_c1_jacobian_multiplicity
