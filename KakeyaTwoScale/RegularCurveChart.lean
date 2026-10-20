module
import all Mathlib.Analysis.Calculus.Implicit
public import KakeyaTwoScale.OrthogonalRegularChart
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Topology.Bases

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- An actual one-dimensional differentiable fiber chart, built from the
implicit function theorem and the rank-one derivative kernel. No atlas or
parametrization is supplied. -/
theorem exists_regular_curve_chart {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (a : E) (hf : ContDiffAt ℝ 1 f a)
    (hA : (fderiv ℝ f a).range=⊤)
    (hker : Module.finrank ℝ (fderiv ℝ f a).ker=1) :
    ∃ γ : ℝ → E, ∃ U : Set ℝ, ∃ W : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ a ∈ W ∧ γ 0=a ∧
      (∀ t ∈ U, DifferentiableAt ℝ γ t) ∧
      (∀ t ∈ U, f (γ t)=f a) ∧
      (∀ x ∈ W, f x=f a → ∃ t ∈ U, γ t=x) := by
  let A := fderiv ℝ f a
  have hstrict : HasStrictFDerivAt f A a := hf.hasStrictFDerivAt (by norm_num)
  let d := orthogonalImplicitData f A a hstrict hA
  let e := d.toOpenPartialHomeomorph
  let l : ℝ ≃L[ℝ] A.ker := ContinuousLinearEquiv.ofFinrankEq (by simp [A,hker])
  let γ : ℝ → E := fun t => d.implicitFunction (f a) (l t)
  have hzero : d.rightFun a=0 := by simp [d,orthogonalImplicitData]
  have hpt : (f a,(0:A.ker)) ∈ e.target := by
    have hh := d.map_pt_mem_toOpenPartialHomeomorph_target
    change (f a,d.rightFun a) ∈ e.target at hh
    rwa [hzero] at hh
  have hc : ContDiffAt ℝ 1 d.implicitFunction.uncurry (f a,(0:A.ker)) := by
    have hh := d.contDiffAt_implicitFunction hf
      (by dsimp [d,orthogonalImplicitData]; fun_prop) (by norm_num : (1:ℕ∞ω)≠0)
    simpa only [ImplicitFunctionData.prodFun,d,orthogonalImplicitData,sub_self,map_zero] using hh
  have hγ : ContDiffAt ℝ 1 γ 0 := by
    have hc0 : ContDiffAt ℝ 1 (fun t : ℝ => (f a,l t)) 0 :=
      contDiffAt_const.prodMk l.contDiff.contDiffAt
    have hc1 : ContDiffAt ℝ 1 d.implicitFunction.uncurry (f a,l 0) := by simpa using hc
    have hh := hc1.comp 0 hc0
    exact hh
  have ht : (fun t : ℝ => (f a,l t)) ⁻¹' e.target ∈ 𝓝 0 :=
    (continuous_const.prodMk l.continuous).continuousAt.preimage_mem_nhds
      (by simpa only [map_zero] using e.open_target.mem_nhds hpt)
  have hd : {t | DifferentiableAt ℝ γ t} ∈ 𝓝 0 := by
    filter_upwards [hγ.eventually (by norm_num)] with t h
    exact h.differentiableAt (by norm_num)
  obtain ⟨U,hUsub,hUopen,hUzero⟩ := _root_.mem_nhds_iff.mp (inter_mem ht hd)
  let coord : E → ℝ := fun x => l.symm (d.rightFun x)
  have hcoord : Continuous coord := by dsimp [coord,d,orthogonalImplicitData]; fun_prop
  let W := e.source ∩ coord ⁻¹' U
  have haW : a ∈ W := by
    refine ⟨d.pt_mem_toOpenPartialHomeomorph_source,?_⟩
    simpa only [coord,hzero,map_zero,mem_preimage] using hUzero
  refine ⟨γ,U,W,hUopen,hUzero,e.open_source.inter (hUopen.preimage hcoord),haW,?_,
    fun t ht => (hUsub ht).2,?_,?_⟩
  · have hh := e.left_inv d.pt_mem_toOpenPartialHomeomorph_source
    change e.symm (f a,d.rightFun a)=a at hh
    simpa only [γ,map_zero,ImplicitFunctionData.implicitFunction_apply,hzero] using hh
  · intro t ht
    have hh := e.right_inv (hUsub ht).1
    exact congrArg Prod.fst hh
  · intro x hx hfx
    refine ⟨coord x,hx.2,?_⟩
    change e.symm (f a,l (l.symm (d.rightFun x)))=x
    rw [l.apply_symm_apply,← hfx]
    exact e.left_inv hx.1

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_regular_curve_chart
