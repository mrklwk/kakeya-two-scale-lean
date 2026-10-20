module
import all Mathlib.Analysis.Calculus.Implicit
public import KakeyaTwoScale.OrthogonalRegularChart
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import KakeyaTwoScale.PolynomialCurveRegularValues
public import KakeyaTwoScale.ScalarSardSmooth

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- A regular fiber chart in arbitrary dimension which is smooth at EVERY parameter whose
image is a smooth point of the defining function. This pointwise conclusion
avoids asserting a common C-infinity neighborhood from ContDiffAt infinity. -/
theorem exists_smooth_fiber_sard_chart {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (h : E → F) (a : E) (hh : ContDiffAt ℝ 1 h a)
    (hA : (fderiv ℝ h a).range = ⊤) :
    let K := (fderiv ℝ h a).ker
    ∃ φ : K → E, ∃ U : Set K, ∃ W : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ a ∈ W ∧ φ 0=a ∧
      (∀ t ∈ U, h (φ t)=h a) ∧
      (∀ x ∈ W, h x=h a → ∃ t ∈ U, φ t=x) ∧
      (∀ t ∈ U, ContDiffAt ℝ ∞ h (φ t) → ContDiffAt ℝ ∞ φ t) := by
  dsimp only
  let A := fderiv ℝ h a
  have hs : HasStrictFDerivAt h A a := hh.hasStrictFDerivAt (by norm_num)
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
  refine ⟨φ,U,W,hUopen,hUzero,hW,hWa,hφzero,?_,?_,?_⟩
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
    have hder : HasFDerivAt d.prodFun (L:E →L[ℝ] F × A.ker) (φ t) := by
      rw [hL]
      exact (hc.differentiableAt (by simp)).hasFDerivAt
    have hcinv : ContDiffAt ℝ ∞ e.symm (h a,t) :=
      e.contDiffAt_symm (hUsub ht).1 hder hc
    have hcp : ContDiffAt ℝ ∞ (fun u : A.ker => (h a,u)) t :=
      contDiffAt_const.prodMk contDiffAt_id
    have hcφ := hcinv.comp t hcp
    exact hcφ

/-- The differential of any actual parametrization of a constraint fiber
lands in the actual tangent kernel. No atlas or tangent identification is
assumed. -/
theorem constrained_chart_derivative {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (f : E → F) (φ : K → E) (U : Set K) (hU : IsOpen U)
    (c : F) {t : K} (ht : t ∈ U)
    (hf : DifferentiableAt ℝ f (φ t)) (hφ : DifferentiableAt ℝ φ t)
    (hconst : ∀ u ∈ U, f (φ u)=c) (v : K) :
    fderiv ℝ f (φ t) (fderiv ℝ φ t v)=0 := by
  have hc := hf.hasFDerivAt.comp t hφ.hasFDerivAt
  have he : (fun u => f (φ u)) =ᶠ[𝓝 t] fun _ => c := by
    filter_upwards [hU.mem_nhds ht] with u hu
    exact hconst u hu
  have hz := (hasFDerivAt_const (𝕜 := ℝ) c t).congr_of_eventuallyEq he
  have hd := hc.unique hz
  exact congrArg (fun L : K →L[ℝ] F => L v) hd

/-- An actual relative critical point remains critical in every smooth
fiber chart. -/
theorem relative_critical_chart_derivative {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (f : E → F) (g : E → ℝ) (φ : K → E) (U : Set K)
    (hU : IsOpen U) (c : F) {t : K} (ht : t ∈ U)
    (hf : DifferentiableAt ℝ f (φ t)) (hg : DifferentiableAt ℝ g (φ t))
    (hφ : DifferentiableAt ℝ φ t) (hconst : ∀ u ∈ U, f (φ u)=c)
    (hcrit : ∀ v : E, fderiv ℝ f (φ t) v=0 → fderiv ℝ g (φ t) v=0) :
    fderiv ℝ (g ∘ φ) t=0 := by
  rw [fderiv_comp t hg hφ]
  ext v
  exact hcrit _ (constrained_chart_derivative f φ U hU c ht hf hφ hconst v)

/-- Relative scalar Sard on an arbitrary-dimensional regular constraint
fiber. The countable smooth chart cover is constructed by the IFT. -/
theorem smooth_fiber_critical_values_null {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (g : E → ℝ) (c : F)
    (hf : ∀ x, f x=c → ContDiffAt ℝ ∞ f x)
    (hg : ∀ x, f x=c → ContDiffAt ℝ ∞ g x)
    (hA : ∀ x, f x=c → (fderiv ℝ f x).range=⊤) :
    volume (g '' {x | f x=c ∧ ∀ v : E, fderiv ℝ f x v=0 → fderiv ℝ g x v=0})=0 := by
  classical
  let Z : Set E := {x | f x=c}
  have hcharts : ∀ x : Z,
      ∃ φ : (fderiv ℝ f (x:E)).ker → E,
      ∃ U : Set (fderiv ℝ f (x:E)).ker, ∃ W : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen W ∧ (x:E) ∈ W ∧ φ 0=x ∧
      (∀ t ∈ U, f (φ t)=f x) ∧
      (∀ y ∈ W, f y=f x → ∃ t ∈ U, φ t=y) ∧
      (∀ t ∈ U, ContDiffAt ℝ ∞ f (φ t) → ContDiffAt ℝ ∞ φ t) := fun x =>
    exists_smooth_fiber_sard_chart f x ((hf x x.property).of_le (by simp)) (hA x x.property)
  choose φ U W hU hU0 hW hWa hφ0 hφf hcov hφd using hcharts
  let V : Z → Set Z := fun x => Subtype.val ⁻¹' W x
  have hV : ∀ x : Z, V x ∈ 𝓝 x := fun x =>
    ((hW x).preimage continuous_subtype_val).mem_nhds (hWa x)
  obtain ⟨I,hIc,hcover⟩ := TopologicalSpace.countable_cover_nhds hV
  let : Countable I := hIc.to_subtype
  let bad := fun i : I => (g ∘ φ i.val) ''
    {t | t ∈ U i.val ∧ fderiv ℝ (g ∘ φ i.val) t=0}
  have hn : volume (⋃ i, bad i)=0 := by
    apply measure_iUnion_null
    intro i
    apply scalar_sard_of_contDiffAt
    · intro t ht
      have hz : f (φ i.val t)=c := (hφf i.val t ht.1).trans i.val.property
      exact (hg _ hz).comp t (hφd i.val t ht.1 (hf _ hz))
    · intro t ht
      exact ht.2
  apply measure_mono_null _ hn
  rintro value ⟨x,⟨hx,hcrit⟩,rfl⟩
  have hcovered : (⟨x,hx⟩ : Z) ∈ ⋃ z ∈ I, V z := by rw [hcover]; trivial
  obtain ⟨z,hzI,hxz⟩ := mem_iUnion₂.mp hcovered
  obtain ⟨t,ht,heq⟩ := hcov z x hxz (hx.trans z.property.symm)
  apply mem_iUnion.mpr
  refine ⟨⟨z,hzI⟩,t,⟨ht,?_⟩,by simp only [Function.comp_apply,heq]⟩
  have hconst : ∀ u ∈ U z, f (φ z u)=c := fun u hu => (hφf z u hu).trans z.property
  apply relative_critical_chart_derivative f g (φ z) (U z) (hU z) c ht
    ((hf _ (hconst t ht)).differentiableAt (by simp))
    ((hg _ (hconst t ht)).differentiableAt (by simp))
    ((hφd z t ht (hf _ (hconst t ht))).differentiableAt (by simp)) hconst
  simpa only [heq] using hcrit

/-- Every open interval contains a level genuinely regular relative to the
fixed smooth constraint fiber. -/
theorem smooth_fiber_exists_relative_regular_value {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (g : E → ℝ) (c : F)
    (hf : ∀ x, f x=c → ContDiffAt ℝ ∞ f x)
    (hg : ∀ x, f x=c → ContDiffAt ℝ ∞ g x)
    (hA : ∀ x, f x=c → (fderiv ℝ f x).range=⊤)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ x : E, f x=c → g x=t →
      ∃ v : E, fderiv ℝ f x v=0 ∧ fderiv ℝ g x v ≠ 0 := by
  classical
  have hn := smooth_fiber_critical_values_null f g c hf hg hA
  have hnot : ¬Ioo a b ⊆ g '' {x | f x=c ∧ ∀ v : E,
      fderiv ℝ f x v=0 → fderiv ℝ g x v=0} := by
    intro h
    have he := measure_mono (μ := volume) h
    rw [hn] at he
    exact (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hab)).not_ge he
  obtain ⟨t,ht,hbad⟩ := Set.not_subset.mp hnot
  refine ⟨t,ht,fun x hx hxt => ?_⟩
  by_contra h
  push Not at h
  exact hbad ⟨x,⟨hx,h⟩,hxt⟩

/-- The selected scalar level raises the actual constraint rank by one.
There is no dimension-one hypothesis and no supplied Sard or atlas premise. -/
theorem smooth_fiber_exists_transverse_level {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (g : E → ℝ) (c : F)
    (hf : ∀ x, f x=c → ContDiffAt ℝ ∞ f x)
    (hg : ∀ x, f x=c → ContDiffAt ℝ ∞ g x)
    (hA : ∀ x, f x=c → (fderiv ℝ f x).range=⊤)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ x : E, f x=c → g x=t →
      (fderiv ℝ (fun y => (f y,g y-t)) x).range=⊤ := by
  obtain ⟨t,ht,hreg⟩ := smooth_fiber_exists_relative_regular_value f g c hf hg hA hab
  refine ⟨t,ht,fun x hx hxt => ?_⟩
  obtain ⟨v,hvA,hvB⟩ := hreg x hx hxt
  have hpair := constraint_pair_surjective (fderiv ℝ f x) (fderiv ℝ g x) (hA x hx) v hvA hvB
  have hdf := (hf x hx).differentiableAt (by simp)
  have hdg := (hg x hx).differentiableAt (by simp)
  have hder := hdf.hasFDerivAt.prodMk (hdg.hasFDerivAt.sub_const t)
  rw [hder.fderiv]
  exact hpair

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_smooth_fiber_sard_chart

#print axioms KakeyaTwoScale.constrained_chart_derivative
#print axioms KakeyaTwoScale.relative_critical_chart_derivative

#print axioms KakeyaTwoScale.smooth_fiber_critical_values_null
#print axioms KakeyaTwoScale.smooth_fiber_exists_relative_regular_value
#print axioms KakeyaTwoScale.smooth_fiber_exists_transverse_level
