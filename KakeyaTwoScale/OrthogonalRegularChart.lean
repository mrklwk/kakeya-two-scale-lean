module
public import KakeyaTwoScale.RegularLocalLipschitzChart
public import KakeyaTwoScale.GraphWallBridge
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import all Mathlib.Analysis.Calculus.Implicit

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace KakeyaTwoScale

/-- Orthogonal choice of transverse coordinates; the chart projection has
norm at most one, independently of the derivative's condition number. -/
def orthogonalImplicitData {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (A : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f A a) (hA : A.range = ⊤) :
    ImplicitFunctionData ℝ E F A.ker where
  leftFun := f
  leftDeriv := A
  rightFun := fun x => A.ker.orthogonalProjectionOnto (x-a)
  rightDeriv := A.ker.orthogonalProjectionOnto
  pt := a
  hasStrictFDerivAt_leftFun := hf
  hasStrictFDerivAt_rightFun := by
    convert A.ker.orthogonalProjectionOnto.hasStrictFDerivAt.comp a
      ((hasStrictFDerivAt_id a).sub_const a) using 1 <;> simp
  range_leftDeriv := hA
  range_rightDeriv := by
    apply LinearMap.range_eq_top.mpr
    intro y
    exact ⟨y,by simp⟩
  isCompl_ker := by
    rw [Submodule.ker_orthogonalProjectionOnto]
    exact A.ker.isCompl_orthogonal

theorem orthogonal_regular_chart {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (A : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f A a) (hA : A.range = ⊤) :
    ∃ π : E → A.ker, ∃ φ : A.ker → E, ∃ V ∈ 𝓝 (0 : A.ker), ∃ U ∈ 𝓝 a,
      LipschitzWith 1 π ∧ π a = 0 ∧ φ 0 = a ∧ LipschitzOnWith 2 φ V ∧
      (∀ y ∈ V, π (φ y) = y ∧ f (φ y) = f a) ∧
      (∀ x ∈ U, f x = f a ↔ ∃ y ∈ V, φ y = x) := by
  let d := orthogonalImplicitData f A a hf hA
  let π := d.rightFun
  let e := d.toOpenPartialHomeomorph
  let φ := d.implicitFunction (f a)
  have hzero : π a = 0 := by simp [π,d,orthogonalImplicitData]
  have hφ : HasStrictFDerivAt φ A.ker.subtypeL 0 := by
    have hh := d.hasStrictFDerivAt_implicitFunction A.ker.subtypeL
      (by ext y; simp [d,orthogonalImplicitData])
      (by ext y; exact y.prop)
    change HasStrictFDerivAt φ A.ker.subtypeL (π a) at hh
    rwa [hzero] at hh
  have hn : ‖A.ker.subtypeL‖₊ < (2 : ℝ≥0) := by
    change ‖A.ker.subtypeL‖ < (2 : ℝ)
    linarith [A.ker.norm_subtypeL_le]
  obtain ⟨V₀,hV₀,hLip⟩ := hφ.exists_lipschitzOnWith_of_nnnorm_lt 2 hn
  have hpt : (f a,(0 : A.ker)) ∈ e.target := by
    have hh := d.map_pt_mem_toOpenPartialHomeomorph_target
    change (f a,π a) ∈ e.target at hh
    rwa [hzero] at hh
  have ht : (fun y : A.ker => (f a,y)) ⁻¹' e.target ∈ 𝓝 0 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds hpt)
  let V := V₀ ∩ (fun y : A.ker => (f a,y)) ⁻¹' e.target
  have hV : V ∈ 𝓝 0 := inter_mem hV₀ ht
  have hcoord : ContinuousAt π a := by
    exact (A.ker.orthogonalProjectionOnto.continuous.comp (continuous_id.sub continuous_const)).continuousAt
  have hU : e.source ∩ π ⁻¹' V ∈ 𝓝 a :=
    inter_mem (e.open_source.mem_nhds d.pt_mem_toOpenPartialHomeomorph_source)
      (hcoord.preimage_mem_nhds (by simpa only [hzero] using hV))
  refine ⟨π,φ,V,hV,_,hU,?_,hzero,?_,hLip.mono inter_subset_left,?_,?_⟩
  · have ht : LipschitzWith 1 (fun x : E => x-a) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp
    simpa only [π,d,orthogonalImplicitData,Function.comp_def,one_mul] using A.ker.lipschitzWith_orthogonalProjectionOnto.comp ht
  · have hh := e.left_inv d.pt_mem_toOpenPartialHomeomorph_source
    change e.symm (f a,π a)=a at hh
    simpa only [φ,ImplicitFunctionData.implicitFunction_apply,hzero] using hh
  · intro y hy
    have hh := e.right_inv hy.2
    exact ⟨congrArg Prod.snd hh,congrArg Prod.fst hh⟩
  · intro x hx
    constructor
    · intro heq
      refine ⟨π x,hx.2,?_⟩
      change e.symm (f a,π x)=x
      rw [← heq]
      exact e.left_inv hx.1
    · rintro ⟨y,hy,rfl⟩
      exact congrArg Prod.fst (e.right_inv hy.2)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orthogonal_regular_chart
