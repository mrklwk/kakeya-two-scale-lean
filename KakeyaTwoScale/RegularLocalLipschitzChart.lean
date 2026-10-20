module
public import Mathlib.Analysis.Calculus.Implicit
import all Mathlib.Analysis.Calculus.Implicit

@[expose] public section

open Set Filter
open scoped Topology NNReal
noncomputable section
namespace KakeyaTwoScale

/-- A surjective strict derivative constructs an actual local parametrization
of its fiber with Lipschitz constant 2 in the inherited norm on the kernel.
The neighborhoods are local; no degree-uniform atlas cardinality is asserted. -/
theorem regular_local_lipschitz_chart {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (A : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f A a) (hA : A.range = ⊤) :
    ∃ φ : A.ker → E, ∃ V ∈ 𝓝 (0 : A.ker), ∃ U ∈ 𝓝 a,
      φ 0 = a ∧ LipschitzOnWith 2 φ V ∧ Set.InjOn φ V ∧
      (∀ y ∈ V, f (φ y) = f a) ∧
      (∀ x ∈ U, f x = f a ↔ ∃ y ∈ V, φ y = x) := by
  let e := hf.implicitToOpenPartialHomeomorph f A hA
  let φ := hf.implicitFunction f A hA (f a)
  have hφ_apply (y : A.ker) : φ y = e.symm (f a, y) := by
    simp only [φ, HasStrictFDerivAt.implicitFunction.eq_def, Function.curry, e]
  have he_fst (x : E) : (e x).1 = f x :=
    hf.implicitToOpenPartialHomeomorph_fst hA x
  have hφ := hf.to_implicitFunction hA
  have hn : ‖A.ker.subtypeL‖₊ < (2 : ℝ≥0) := by
    change ‖A.ker.subtypeL‖ < (2 : ℝ)
    linarith [A.ker.norm_subtypeL_le]
  obtain ⟨V₀, hV₀, hLip⟩ := hφ.exists_lipschitzOnWith_of_nnnorm_lt 2 hn
  have ht : (fun y : A.ker => (f a, y)) ⁻¹' e.target ∈ 𝓝 0 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds (hf.mem_implicitToOpenPartialHomeomorph_target hA))
  let V := V₀ ∩ (fun y : A.ker => (f a, y)) ⁻¹' e.target
  have hV : V ∈ 𝓝 0 := inter_mem hV₀ ht
  have hcoord : ContinuousAt (fun x => (e x).2) a :=
    (e.continuousAt (hf.mem_implicitToOpenPartialHomeomorph_source hA)).snd
  have hzero : (e a).2 = 0 := by
    simp [e]
  have hU : e.source ∩ (fun x => (e x).2) ⁻¹' V ∈ 𝓝 a :=
    inter_mem (e.open_source.mem_nhds (hf.mem_implicitToOpenPartialHomeomorph_source hA))
      (hcoord.preimage_mem_nhds (by simpa only [hzero] using hV))
  refine ⟨φ, V, hV, _, hU, hf.implicitFunction_apply_image hA,
    hLip.mono inter_subset_left, ?_, ?_, ?_⟩
  · intro y hy z hz heq
    have hy' := e.right_inv hy.2
    have hz' := e.right_inv hz.2
    have he : e (φ y) = e (φ z) := congrArg e heq
    rw [hφ_apply, hφ_apply] at he
    rw [hy',hz'] at he
    exact congrArg Prod.snd he
  · intro y hy
    have hh := congrArg Prod.fst (e.right_inv hy.2)
    simpa only [he_fst, ← hφ_apply] using hh
  · intro x hx
    constructor
    · intro heq
      refine ⟨(e x).2,hx.2,?_⟩
      rw [hφ_apply]
      have hfst : (e x).1 = f a := (he_fst x).trans heq
      rw [← hfst]
      exact e.left_inv hx.1
    · rintro ⟨y,hy,rfl⟩
      simpa only [he_fst, ← hφ_apply] using congrArg Prod.fst (e.right_inv hy.2)

end KakeyaTwoScale

#print axioms KakeyaTwoScale.regular_local_lipschitz_chart
