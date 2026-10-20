module
public import KakeyaTwoScale.PolynomialHypersurfaceCharts
public import KakeyaTwoScale.BufferedRegularChart

@[expose] public section

open MvPolynomial Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace KakeyaTwoScale

theorem polynomial_euclidean_fderiv_ne_zero {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (a : EuclideanSpace ℝ (Fin n)) (hr : ∃ j, eval a (pderiv j P) ≠ 0) :
    (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => eval y P) a).toLinearMap ≠ 0 := by
  have hs := (polynomial_eval_contDiff P 1).differentiable (by norm_num)
  have ht : Differentiable ℝ (fun y : Fin n → ℝ => WithLp.toLp 2 y) :=
    (PiLp.contDiff_toLp (p := (2 : ENNReal)) (𝕜 := ℝ) (n := 1)).differentiable (by norm_num)
  intro hz
  have hzero : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => eval y P) a = 0 := by
    ext v
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ => L v) hz
  have hc := (hs a).hasFDerivAt.comp (fun j => a j) (ht (fun j => a j)).hasFDerivAt
  rw [hzero,ContinuousLinearMap.zero_comp] at hc
  have hpi : fderiv ℝ (fun y : Fin n → ℝ => eval y P) (fun j => a j) = 0 := hc.fderiv
  exact polynomial_scalar_fderiv_ne_zero P (fun j => a j) hr
    (congrArg ContinuousLinearMap.toLinearMap hpi)

/-- Every point of a nonzero hypersurface, including a singular point, has
an actual buffered Euclidean graph on one of a fixed bounded derivative family.
The graph contains the point but can contain points outside the original zero set. -/
theorem polynomial_zero_buffered_cover {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P ≠ 0) (hD : P.totalDegree ≤ D)
    (a : EuclideanSpace ℝ (Fin n)) (ha : eval a P = 0) :
    ∃ Q ∈ derivativeCoverFamily P D, Q.totalDegree ≤ D ∧
      let f := fun y : EuclideanSpace ℝ (Fin n) => eval y Q
      let A := fderiv ℝ f a
      Module.finrank ℝ A.ker + 1 = n ∧
      ∃ π : EuclideanSpace ℝ (Fin n) → A.ker,
      ∃ φ : A.ker → EuclideanSpace ℝ (Fin n), ∃ r : ℝ, 0 < r ∧
        LipschitzWith 1 π ∧ π a = 0 ∧ φ 0 = a ∧
        LipschitzOnWith 2 φ (ball 0 (2*r)) ∧
        (∀ y ∈ ball 0 (2*r), π (φ y)=y ∧ f (φ y)=0) ∧
        (∃ U ∈ 𝓝 a, ∀ x ∈ U, π x ∈ ball 0 r ∧ (f x=0 ↔ φ (π x)=x)) ∧
        (∀ Z : Set A.ker, ∀ η ρ : ℝ, η+ρ ≤ r → ∀ x,
          x ∈ thickening η (φ '' ball 0 r) → π x ∈ thickening ρ Z →
          x ∈ thickening (3*η+2*ρ) ({z | f z=0} ∩ π ⁻¹' Z)) := by
  obtain ⟨Q,hQ,hQa,hr⟩ := derivativeCoverFamily_covers P hP hD (fun j => a j) ha
  refine ⟨Q,hQ,(derivativeCoverFamily_degree P Q hQ).trans hD,?_⟩
  dsimp only
  have hne := polynomial_euclidean_fderiv_ne_zero Q a hr
  refine ⟨?_,?_⟩
  · simpa using Module.Dual.finrank_ker_add_one_of_ne_zero hne
  · simpa only [hQa] using orthogonal_regular_buffered_chart
      (fun y : EuclideanSpace ℝ (Fin n) => eval y Q)
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => eval y Q) a) a
      ((polynomial_eval_contDiff Q 1).hasStrictFDerivAt (by norm_num))
      (Module.Dual.range_eq_top_of_ne_zero hne)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_euclidean_fderiv_ne_zero
#print axioms KakeyaTwoScale.polynomial_zero_buffered_cover
