module
import all Mathlib.Analysis.Calculus.Implicit
public import KakeyaTwoScale.OrthogonalRegularChart
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- A regular hypersurface chart which is smooth at EVERY parameter whose
image is a smooth point of the defining function. This pointwise conclusion
avoids asserting a common C-infinity neighborhood from ContDiffAt infinity. -/
theorem exists_smooth_hypersurface_sard_chart {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (h : E → ℝ) (a : E) (hh : ContDiffAt ℝ 1 h a)
    (hne : (fderiv ℝ h a).toLinearMap ≠ 0) :
    let K := (fderiv ℝ h a).ker
    ∃ φ : K → E, ∃ U : Set K, ∃ W : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ a ∈ W ∧ φ 0=a ∧
      (∀ t ∈ U, h (φ t)=h a) ∧
      (∀ x ∈ W, h x=h a → ∃ t ∈ U, φ t=x) ∧
      (∀ t ∈ U, ContDiffAt ℝ ∞ h (φ t) → ContDiffAt ℝ ∞ φ t) ∧
      Module.finrank ℝ K+1=Module.finrank ℝ E := by
  dsimp only
  let A := fderiv ℝ h a
  have hs : HasStrictFDerivAt h A a := hh.hasStrictFDerivAt (by norm_num)
  have hA : A.range=⊤ := Module.Dual.range_eq_top_of_ne_zero hne
  let d := orthogonalImplicitData h A a hs hA
  let e := d.toOpenPartialHomeomorph
  let φ := d.implicitFunction (h a)
  have hzero : d.rightFun a=0 := by simp [d,orthogonalImplicitData]
  have hφzero : φ 0=a := by
    have he := e.left_inv d.pt_mem_toOpenPartialHomeomorph_source
    change e.symm (h a,d.rightFun a)=a at he
    simpa only [φ,ImplicitFunctionData.implicitFunction_apply,hzero] using he
  have hprod : ContDiffAt ℝ 1 d.prodFun a := by
    change ContDiffAt ℝ 1 (fun x => (h x,d.rightFun x)) a
    exact hh.prodMk (by dsimp [d,orthogonalImplicitData]; fun_prop)
  have hinv : ∀ᶠ x in 𝓝 a, (fderiv ℝ d.prodFun x).IsInvertible :=
    (hprod.continuousAt_fderiv (by norm_num)).tendsto.eventually
      d.isInvertible_fderiv_prodFun.eventually_nhds
  obtain ⟨W₀,hWsub,hWopen,haW⟩ := mem_nhds_iff.mp hinv
  have hpt : (h a,(0:A.ker)) ∈ e.target := by
    have ht := d.map_pt_mem_toOpenPartialHomeomorph_target
    change (h a,d.rightFun a) ∈ e.target at ht
    rwa [hzero] at ht
  have hφcont : ContinuousAt φ 0 := by
    have hi := e.symm.continuousAt hpt
    have hc : ContinuousAt (fun t : A.ker => (h a,t)) 0 := continuousAt_const.prodMk continuousAt_id
    exact hi.comp hc
  have htarget : (fun t : A.ker => (h a,t)) ⁻¹' e.target ∈ 𝓝 0 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hpt)
  have hpre : φ ⁻¹' W₀ ∈ 𝓝 0 :=
    hφcont.preimage_mem_nhds (by simpa only [hφzero] using hWopen.mem_nhds haW)
  obtain ⟨U,hUsub,hUopen,hUzero⟩ := mem_nhds_iff.mp (inter_mem htarget hpre)
  have hcoord : Continuous d.rightFun := by dsimp [d,orthogonalImplicitData]; fun_prop
  let W := e.source ∩ d.rightFun ⁻¹' U
  have hW : IsOpen W := e.open_source.inter (hUopen.preimage hcoord)
  have hWa : a ∈ W := ⟨d.pt_mem_toOpenPartialHomeomorph_source,by
    simpa only [mem_preimage,hzero] using hUzero⟩
  refine ⟨φ,U,W,hUopen,hUzero,hW,hWa,hφzero,?_,?_,?_,
    Module.Dual.finrank_ker_add_one_of_ne_zero hne⟩
  · intro t ht
    exact congrArg Prod.fst (e.right_inv (hUsub ht).1)
  · intro x hx heq
    refine ⟨d.rightFun x,hx.2,?_⟩
    change e.symm (h a,d.rightFun x)=x
    rw [← heq]
    exact e.left_inv hx.1
  · intro t ht hht
    have hi := hWsub (hUsub ht).2
    obtain ⟨L,hL⟩ := hi
    have hc : ContDiffAt ℝ ∞ d.prodFun (φ t) := by
      change ContDiffAt ℝ ∞ (fun x => (h x,d.rightFun x)) (φ t)
      exact hht.prodMk (by dsimp [d,orthogonalImplicitData]; fun_prop)
    have hder : HasFDerivAt d.prodFun (L:E →L[ℝ] ℝ × A.ker) (φ t) := by
      rw [hL]
      exact (hc.differentiableAt (by simp)).hasFDerivAt
    have hcinv : ContDiffAt ℝ ∞ e.symm (h a,t) :=
      e.contDiffAt_symm (hUsub ht).1 hder hc
    have hcp : ContDiffAt ℝ ∞ (fun u : A.ker => (h a,u)) t :=
      contDiffAt_const.prodMk contDiffAt_id
    have hcφ := hcinv.comp t hcp
    exact hcφ

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_smooth_hypersurface_sard_chart
