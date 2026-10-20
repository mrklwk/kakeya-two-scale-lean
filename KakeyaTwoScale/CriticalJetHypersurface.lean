module
public import KakeyaTwoScale.SmoothHypersurfaceSardChart
public import Mathlib.Analysis.Normed.Module.HahnBanach

@[expose] public section

open Set
open scoped ContDiff
noncomputable section
namespace KakeyaTwoScale

theorem exists_critical_jet_hypersurface {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (a : E) (j : ℕ)
    (hf : ContDiffAt ℝ ∞ f a)
    (hz : iteratedFDeriv ℝ j f a=0)
    (hn : iteratedFDeriv ℝ (j+1) f a≠0) :
    ∃ h : E → ℝ, h a=0 ∧ (fderiv ℝ h a).toLinearMap≠0 ∧
      (∀ x, iteratedFDeriv ℝ j f x=0 → h x=0) ∧
      (∀ x, ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ h x) := by
  let F := iteratedFDeriv ℝ j f
  have hF : ContDiffAt ℝ ∞ F a := hf.iteratedFDeriv_right (by simp)
  have hDF : fderiv ℝ F a≠0 := by
    intro he
    apply hn
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp only [Function.comp_apply]
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) ℝ).symm
      (fderiv ℝ F a)=0
    rw [he]
    exact LinearIsometryEquiv.map_zero _
  obtain ⟨v,hv⟩ : ∃ v, fderiv ℝ F a v≠0 := by
    by_contra hh
    push Not at hh
    exact hDF (ContinuousLinearMap.ext hh)
  obtain ⟨l,_,hl⟩ := exists_dual_vector ℝ (fderiv ℝ F a v) (norm_ne_zero_iff.mpr hv)
  let h := fun x => l (F x)
  have hd : HasFDerivAt h (l.comp (fderiv ℝ F a)) a :=
    l.hasFDerivAt.comp a (hF.differentiableAt (by simp)).hasFDerivAt
  refine ⟨h,?_,?_,?_,?_⟩
  · simp [h,F,hz]
  · intro he
    have he' := congrArg (fun T : E →ₗ[ℝ] ℝ => T v) he
    change fderiv ℝ h a v=0 at he'
    rw [hd.fderiv] at he'
    change l (fderiv ℝ F a v)=0 at he'
    rw [hl] at he'
    exact hv (norm_eq_zero.mp he')
  · intro x hx
    simp [h,F,hx]
  · intro x hx
    exact l.contDiff.contDiffAt.comp x (hx.iteratedFDeriv_right (by simp))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_critical_jet_hypersurface
