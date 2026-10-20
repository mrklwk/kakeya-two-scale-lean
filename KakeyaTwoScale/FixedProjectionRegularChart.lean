module
import all Mathlib.Analysis.Calculus.Implicit
public import KakeyaTwoScale.OrthogonalRegularChart

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace KakeyaTwoScale

/-- The kernel complement is derived from the actual linear section and
injectivity of projection on the tangent kernel. -/
theorem fixed_projection_kernel_complement {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : E →L[ℝ] F) (π : E →L[ℝ] V) (B : V →L[ℝ] E)
    (hAB : A.comp B = 0) (hπB : π.comp B = ContinuousLinearMap.id ℝ V)
    (hinj : ∀ x, A x = 0 → π x = 0 → x = 0) : IsCompl A.ker π.ker := by
  constructor
  · rw [disjoint_iff_inf_le]
    intro x hx
    exact hinj x hx.1 hx.2
  · rw [codisjoint_iff_le_sup]
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨B (π x), ?_, x - B (π x), ?_, by abel⟩
    · exact congrArg (fun T : V →L[ℝ] F => T (π x)) hAB
    · change π (x - B (π x)) = 0
      rw [map_sub]
      have he := congrArg (fun T : V →L[ℝ] V => T (π x)) hπB
      change π (B (π x)) = π x at he
      rw [he, sub_self]

/-- A fixed projection admits actual quantitative local inverse sections on a
regular fiber. The linear section bound is strict so that the inverse function
theorem supplies the requested Lipschitz constant on a genuine neighborhood.
No successful path lift or preexisting local section is assumed. -/
theorem fixed_projection_regular_chart {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : E → F) (A : E →L[ℝ] F) (π : E →L[ℝ] V) (a : E)
    (hf : HasStrictFDerivAt f A a) (hA : A.range = ⊤)
    (hcompl : IsCompl A.ker π.ker)
    (B : V →L[ℝ] E) (hAB : A.comp B = 0)
    (hπB : π.comp B = ContinuousLinearMap.id ℝ V)
    (L : ℝ≥0) (hB : ‖B‖₊ < L) :
    ∃ σ : V → E, ∃ U ∈ 𝓝 (π a),
      σ (π a) = a ∧ LipschitzOnWith L σ U ∧
      (∀ v ∈ U, f (σ v) = f a ∧ π (σ v) = v) := by
  let d : ImplicitFunctionData ℝ E F V := {
    leftFun := f
    leftDeriv := A
    rightFun := π
    rightDeriv := π
    pt := a
    hasStrictFDerivAt_leftFun := hf
    hasStrictFDerivAt_rightFun := π.hasStrictFDerivAt
    range_leftDeriv := hA
    range_rightDeriv := by
      apply LinearMap.range_eq_top.mpr
      intro v
      refine ⟨B v, ?_⟩
      exact congrArg (fun T : V →L[ℝ] V => T v) hπB
    isCompl_ker := hcompl }
  let σ := d.implicitFunction (f a)
  have hσ : HasStrictFDerivAt σ B (π a) :=
    d.hasStrictFDerivAt_implicitFunction B hπB hAB
  obtain ⟨U₀,hU₀,hLip⟩ := hσ.exists_lipschitzOnWith_of_nnnorm_lt L hB
  let e := d.toOpenPartialHomeomorph
  have ht : (fun v : V => (f a,v)) ⁻¹' e.target ∈ 𝓝 (π a) :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds d.map_pt_mem_toOpenPartialHomeomorph_target)
  refine ⟨σ, U₀ ∩ (fun v : V => (f a,v)) ⁻¹' e.target,
    inter_mem hU₀ ht, ?_, hLip.mono inter_subset_left, ?_⟩
  · exact e.left_inv d.pt_mem_toOpenPartialHomeomorph_source
  · intro v hv
    have hh := e.right_inv hv.2
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩

/-- Shrink the constructed section into an actual open positive barrier region.
The radius is an output and may depend on the point. -/
theorem fixed_projection_positive_chart {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : E → F) (A : E →L[ℝ] F) (π : E →L[ℝ] V) (a : E)
    (hf : HasStrictFDerivAt f A a) (hA : A.range = ⊤)
    (hcompl : IsCompl A.ker π.ker)
    (B : V →L[ℝ] E) (hAB : A.comp B = 0)
    (hπB : π.comp B = ContinuousLinearMap.id ℝ V)
    (L : ℝ≥0) (hB : ‖B‖₊ < L)
    (g : E → ℝ) (hg : ContinuousAt g a) (hga : 0 < g a) :
    ∃ σ : V → E, ∃ r : ℝ, 0 < r ∧ σ (π a) = a ∧
      LipschitzOnWith L σ (ball (π a) r) ∧
      (∀ v ∈ ball (π a) r, f (σ v) = f a ∧ 0 < g (σ v) ∧ π (σ v) = v) := by
  obtain ⟨σ,U,hU,hσa,hLip,hsec⟩ :=
    fixed_projection_regular_chart f A π a hf hA hcompl B hAB hπB L hB
  have hc : ContinuousAt σ (π a) :=
    (hLip.continuousOn.continuousWithinAt (mem_of_mem_nhds hU)).continuousAt hU
  have hgσ : ContinuousAt (fun v => g (σ v)) (π a) := by
    have hbase : ContinuousAt g (σ (π a)) := by simpa only [hσa] using hg
    exact hbase.comp hc
  have hpos : ∀ᶠ v in 𝓝 (π a), 0 < g (σ v) :=
    continuousAt_const.eventually_lt hgσ (by simpa only [hσa] using hga)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hpos)
  refine ⟨σ,r,hr,hσa,hLip.mono (fun v hv => (hsub hv).1),?_⟩
  intro v hv
  exact ⟨(hsec v (hsub hv).1).1,(hsub hv).2,(hsec v (hsub hv).1).2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fixed_projection_regular_chart
#print axioms KakeyaTwoScale.fixed_projection_positive_chart

#print axioms KakeyaTwoScale.fixed_projection_kernel_complement
