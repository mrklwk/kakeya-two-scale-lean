module
public import KakeyaTwoScale.RelativeCurveRegularValues
public import KakeyaTwoScale.PolynomialHypersurfaceCharts
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open Set MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A scalar functional nonzero on the tangent kernel increases the
constraint rank by one. The witness is used to solve the joint equations. -/
theorem constraint_pair_surjective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (B : E →L[ℝ] ℝ) (hA : A.range=⊤)
    (v : E) (hvA : A v=0) (hvB : B v ≠ 0) : (A.prod B).range=⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro y
  obtain ⟨u,hu⟩ := LinearMap.range_eq_top.mp hA y.1
  change A u=y.1 at hu
  refine ⟨u+((y.2-B u)/B v) • v,?_⟩
  apply Prod.ext
  · change A (u+((y.2-B u)/B v) • v)=y.1
    simpa only [map_add,map_smul,hvA,smul_zero,add_zero] using hu
  · change B (u+((y.2-B u)/B v) • v)=y.2
    simp only [map_add,map_smul,smul_eq_mul]
    field_simp
    ring

/-- The actual selected level is transverse jointly with all old constraints,
not merely a regular hypersurface in ambient space. -/
theorem regular_curve_exists_transverse_level {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (g : E → ℝ)
    (hf : ∀ x, f x=0 → ContDiffAt ℝ 1 f x)
    (hg : ∀ x, f x=0 → DifferentiableAt ℝ g x)
    (hA : ∀ x, f x=0 → (fderiv ℝ f x).range=⊤)
    (hker : ∀ x, f x=0 → Module.finrank ℝ (fderiv ℝ f x).ker=1)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ x : E, f x=0 → g x=t →
      (fderiv ℝ (fun y => (f y,g y-t)) x).range=⊤ := by
  obtain ⟨t,ht,hreg⟩ := regular_curve_exists_relative_regular_value f g hf hg hA hker hab
  refine ⟨t,ht,fun x hx hxt => ?_⟩
  obtain ⟨v,hvA,hvB⟩ := hreg x hx hxt
  have hpair := constraint_pair_surjective (fderiv ℝ f x) (fderiv ℝ g x) (hA x hx) v hvA hvB
  have hdf := (hf x hx).differentiableAt (by norm_num)
  have hder := hdf.hasFDerivAt.prodMk ((hg x hx).hasFDerivAt.sub_const t)
  rw [hder.fderiv]
  exact hpair

/-- Surjective n constraints in n+1 Euclidean dimensions have the rank-one
kernel used by the constructed curve charts. -/
theorem euclidean_constraint_kernel_dimension {n : ℕ}
    (A : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] (Fin n → ℝ))
    (hA : A.range=⊤) : Module.finrank ℝ A.ker=1 := by
  have h := A.toLinearMap.finrank_range_add_finrank_ker
  rw [hA] at h
  simp only [finrank_top,Module.finrank_fin_fun,finrank_euclideanSpace_fin] at h
  omega

/-- Actual constant-shift regular-value selection for arbitrary polynomial
complete-intersection CURVES. The input constraints are fixed. The new
polynomial is precisely q-C t, so its degree is not enlarged. -/
theorem polynomial_curve_exists_transverse_level {n : ℕ}
    (P : Fin n → MvPolynomial (Fin (n+1)) ℝ)
    (q : MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ x : EuclideanSpace ℝ (Fin (n+1)),
      (∀ i, eval (fun j => x j) (P i)=0) →
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (n+1)) =>
        fun i => eval (fun j => y j) (P i)) x).range=⊤)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, (q-C t).totalDegree ≤ q.totalDegree ∧
      ∀ x : EuclideanSpace ℝ (Fin (n+1)),
        (∀ i, eval (fun j => x j) (P i)=0) → eval (fun j => x j) (q-C t)=0 →
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (n+1)) =>
          ((fun i => eval (fun j => y j) (P i)),eval (fun j => y j) (q-C t))) x).range=⊤ := by
  let f : EuclideanSpace ℝ (Fin (n+1)) → (Fin n → ℝ) :=
    fun x i => eval (fun j => x j) (P i)
  let g : EuclideanSpace ℝ (Fin (n+1)) → ℝ := fun x => eval (fun j => x j) q
  have hf : ContDiff ℝ 1 f := contDiff_pi.mpr (fun i => polynomial_eval_contDiff (P i) 1)
  have hg : ContDiff ℝ 1 g := polynomial_eval_contDiff q 1
  have hsurj : ∀ x, f x=0 → (fderiv ℝ f x).range=⊤ := by
    intro x hx
    apply hP x
    intro i
    exact congrFun hx i
  obtain ⟨t,ht,hreg⟩ := regular_curve_exists_transverse_level f g
    (fun x _ => hf.contDiffAt) (fun x _ => hg.differentiable (by norm_num) x)
    hsurj (fun x hx => euclidean_constraint_kernel_dimension _ (hsurj x hx)) hab
  refine ⟨t,ht,(totalDegree_sub q (C t)).trans (by simp),fun x hx hqx => ?_⟩
  have hfx : f x=0 := funext hx
  have hgx : g x=t := by simpa only [map_sub,eval_C,sub_eq_zero] using hqx
  simpa only [f,g,map_sub,eval_C] using hreg x hfx hgx

end KakeyaTwoScale
#print axioms KakeyaTwoScale.constraint_pair_surjective
#print axioms KakeyaTwoScale.regular_curve_exists_transverse_level
#print axioms KakeyaTwoScale.euclidean_constraint_kernel_dimension
#print axioms KakeyaTwoScale.polynomial_curve_exists_transverse_level
