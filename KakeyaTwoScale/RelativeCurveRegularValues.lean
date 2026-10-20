module
public import KakeyaTwoScale.ScalarSardBase
public import KakeyaTwoScale.RegularCurveChart

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace KakeyaTwoScale

/-- A genuinely constrained curve has its actual velocity in the kernel of
the constraint derivative. -/
theorem constrained_curve_velocity {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (γ : ℝ → E) (U : Set ℝ) (hU : IsOpen U) {t : ℝ} (ht : t ∈ U)
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : DifferentiableAt ℝ γ t)
    (hzero : ∀ u ∈ U, f (γ u)=0) :
    fderiv ℝ f (γ t) (deriv γ t)=0 := by
  have hc := hf.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
  have he : (fun u => f (γ u)) =ᶠ[𝓝 t] fun _ => (0:F) := by
    filter_upwards [hU.mem_nhds ht] with u hu
    exact hzero u hu
  have hz := (hasDerivAt_const t (0:F)).congr_of_eventuallyEq he
  exact hc.unique hz

/-- The actual curve derivative witnesses nontriviality on the tangent
kernel whenever the composed scalar derivative is nonzero. -/
theorem curve_regular_value_tangent {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (g : E → ℝ) (γ : ℝ → E) (U : Set ℝ) (hU : IsOpen U)
    {t : ℝ} (ht : t ∈ U) (hf : DifferentiableAt ℝ f (γ t))
    (hg : DifferentiableAt ℝ g (γ t)) (hγ : DifferentiableAt ℝ γ t)
    (hzero : ∀ u ∈ U, f (γ u)=0)
    (hreg : fderiv ℝ (g ∘ γ) t ≠ 0) :
    ∃ v : E, fderiv ℝ f (γ t) v=0 ∧ fderiv ℝ g (γ t) v ≠ 0 := by
  refine ⟨deriv γ t,constrained_curve_velocity f γ U hU ht hf hγ hzero,?_⟩
  intro hz
  have hc := hg.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
  apply hreg
  apply ContinuousLinearMap.ext
  intro r
  rw [fderiv_eq_smul_deriv,hc.deriv,hz,smul_zero]
  rfl

/-- Genuine relative regular-level selection on an arbitrary regular
one-dimensional fiber. Both local differentiable charts and their countable
cover are constructed here; critical-image nullity and generic regularity
are NOT supplied assumptions. -/
theorem regular_curve_exists_relative_regular_value {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (g : E → ℝ)
    (hf : ∀ x, f x=0 → ContDiffAt ℝ 1 f x)
    (hg : ∀ x, f x=0 → DifferentiableAt ℝ g x)
    (hA : ∀ x, f x=0 → (fderiv ℝ f x).range=⊤)
    (hker : ∀ x, f x=0 → Module.finrank ℝ (fderiv ℝ f x).ker=1)
    {a b : ℝ} (hab : a < b) :
    ∃ value ∈ Ioo a b, ∀ x : E, f x=0 → g x=value →
      ∃ v : E, fderiv ℝ f x v=0 ∧ fderiv ℝ g x v ≠ 0 := by
  classical
  let Z : Set E := {x | f x=0}
  have hcharts : ∀ x : Z, ∃ γ : ℝ → E, ∃ U : Set ℝ, ∃ W : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ (x:E) ∈ W ∧ γ 0=x ∧
      (∀ t ∈ U, DifferentiableAt ℝ γ t) ∧ (∀ t ∈ U, f (γ t)=f x) ∧
      (∀ y ∈ W, f y=f x → ∃ t ∈ U, γ t=y) := fun x =>
    exists_regular_curve_chart f x (hf x x.property) (hA x x.property) (hker x x.property)
  choose γ U W hU hU0 hW hWa hγ0 hγd hγf hcov using hcharts
  let V : Z → Set Z := fun x => Subtype.val ⁻¹' W x
  have hV : ∀ x : Z, V x ∈ 𝓝 x := fun x =>
    ((hW x).preimage continuous_subtype_val).mem_nhds (hWa x)
  obtain ⟨I,hIc,hcover⟩ := TopologicalSpace.countable_cover_nhds hV
  let : Countable I := hIc.to_subtype
  have hdiff : ∀ i : I, ∀ t ∈ U i.val, DifferentiableAt ℝ (g ∘ γ i.val) t := by
    intro i t ht
    have hz : f (γ i.val t)=0 := (hγf i.val t ht).trans i.val.property
    exact (hg _ hz).comp t (hγd i.val t ht)
  obtain ⟨value,hvalue,hreg⟩ := countable_scalar_exists_common_regular_value
    (fun i : I => g ∘ γ i.val) (fun i : I => U i.val) hdiff hab
  refine ⟨value,hvalue,fun x hx hval => ?_⟩
  have hcovered : (⟨x,hx⟩ : Z) ∈ ⋃ z ∈ I, V z := by rw [hcover]; trivial
  obtain ⟨z,hzI,hxz⟩ := mem_iUnion₂.mp hcovered
  obtain ⟨t,ht,heq⟩ := hcov z x hxz (hx.trans z.property.symm)
  have hreg' : fderiv ℝ (g ∘ γ z) t ≠ 0 :=
    hreg ⟨z,hzI⟩ t ht (by simpa only [Function.comp_apply,heq] using hval)
  have hzero : ∀ u ∈ U z, f (γ z u)=0 := fun u hu => (hγf z u hu).trans z.property
  have hh := curve_regular_value_tangent f g (γ z) (U z) (hU z) ht
    ((hf _ (hzero t ht)).differentiableAt (by norm_num)) (hg _ (hzero t ht))
    (hγd z t ht) hzero hreg'
  simpa only [heq] using hh

/-- The full relative critical-value set is null on a regular curve. This is
a proved induction base for scalar Sard, not only a dense-level assertion. -/
theorem regular_curve_critical_values_null {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (g : E → ℝ)
    (hf : ∀ x, f x=0 → ContDiffAt ℝ 1 f x)
    (hg : ∀ x, f x=0 → DifferentiableAt ℝ g x)
    (hA : ∀ x, f x=0 → (fderiv ℝ f x).range=⊤)
    (hker : ∀ x, f x=0 → Module.finrank ℝ (fderiv ℝ f x).ker=1) :
    volume (g '' {x | f x=0 ∧ ∀ v : E, fderiv ℝ f x v=0 → fderiv ℝ g x v=0})=0 := by
  classical
  let Z : Set E := {x | f x=0}
  have hcharts : ∀ x : Z, ∃ γ : ℝ → E, ∃ U : Set ℝ, ∃ W : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ (x:E) ∈ W ∧ γ 0=x ∧
      (∀ t ∈ U, DifferentiableAt ℝ γ t) ∧ (∀ t ∈ U, f (γ t)=f x) ∧
      (∀ y ∈ W, f y=f x → ∃ t ∈ U, γ t=y) := fun x =>
    exists_regular_curve_chart f x (hf x x.property) (hA x x.property) (hker x x.property)
  choose γ U W hU hU0 hW hWa hγ0 hγd hγf hcov using hcharts
  let V : Z → Set Z := fun x => Subtype.val ⁻¹' W x
  have hV : ∀ x : Z, V x ∈ 𝓝 x := fun x =>
    ((hW x).preimage continuous_subtype_val).mem_nhds (hWa x)
  obtain ⟨I,hIc,hcover⟩ := TopologicalSpace.countable_cover_nhds hV
  let : Countable I := hIc.to_subtype
  let bad := fun i : I => (g ∘ γ i.val) ''
    {t | t ∈ U i.val ∧ fderiv ℝ (g ∘ γ i.val) t=0}
  have hn : volume (⋃ i, bad i)=0 := by
    apply measure_iUnion_null
    intro i
    apply scalar_critical_values_null
    intro t ht
    exact (hg _ ((hγf i.val t ht).trans i.val.property)).comp t (hγd i.val t ht)
  apply measure_mono_null _ hn
  rintro value ⟨x,⟨hx,hcrit⟩,rfl⟩
  have hcovered : (⟨x,hx⟩ : Z) ∈ ⋃ z ∈ I, V z := by rw [hcover]; trivial
  obtain ⟨z,hzI,hxz⟩ := mem_iUnion₂.mp hcovered
  obtain ⟨t,ht,heq⟩ := hcov z x hxz (hx.trans z.property.symm)
  apply mem_iUnion.mpr
  refine ⟨⟨z,hzI⟩,t,⟨ht,?_⟩,by simp only [Function.comp_apply,heq]⟩
  by_contra hne
  have hzero : ∀ u ∈ U z, f (γ z u)=0 := fun u hu => (hγf z u hu).trans z.property
  obtain ⟨v,hvf,hvg⟩ := curve_regular_value_tangent f g (γ z) (U z) (hU z) ht
    ((hf _ (hzero t ht)).differentiableAt (by norm_num)) (hg _ (hzero t ht))
    (hγd z t ht) hzero hne
  rw [heq] at hvf hvg
  exact hvg (hcrit v hvf)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.constrained_curve_velocity
#print axioms KakeyaTwoScale.curve_regular_value_tangent
#print axioms KakeyaTwoScale.regular_curve_exists_relative_regular_value

#print axioms KakeyaTwoScale.regular_curve_critical_values_null
