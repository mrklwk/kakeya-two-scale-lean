module
public import KakeyaTwoScale.RegularLocalLipschitzChart
public import KakeyaTwoScale.PolynomialDerivativeDescent
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open MvPolynomial Set Filter
open scoped Topology
noncomputable section
namespace KakeyaTwoScale

theorem polynomial_scalar_fderiv_coordinate {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (fun y => eval y P) x (Pi.single j 1) = eval x (pderiv j P) := by
  have hs : ContDiff ℝ 1 (fun y : Fin n → ℝ => eval y P) :=
    (polynomial_eval_contDiff P 1).comp (PiLp.contDiff_toLp (p := (2 : ENNReal)))
  have hd := (hs.differentiable (by norm_num) x).hasFDerivAt
  have hd' : HasFDerivAt (fun y => eval y P) (fderiv ℝ (fun y => eval y P) x)
      (Function.update x j (x j)) := by simpa using hd
  have hc := hd'.comp_hasDerivAt (x j) (hasDerivAt_update x j (x j))
  have he : HasDerivAt (fun t => eval (Function.update x j t) P)
      (fderiv ℝ (fun y => eval y P) x (Pi.single j 1)) (x j) := by
    simpa [Function.comp_def] using hc
  exact he.unique (by simpa using polynomial_coordinate_hasDerivAt P x j (x j))

theorem polynomial_scalar_fderiv_ne_zero {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (a : Fin n → ℝ) (hr : ∃ j, eval a (pderiv j P) ≠ 0) :
    (fderiv ℝ (fun y => eval y P) a).toLinearMap ≠ 0 := by
  obtain ⟨j,hj⟩ := hr
  intro hz
  have hh := polynomial_scalar_fderiv_coordinate P a j
  have hzero := congrArg (fun L : (Fin n → ℝ) →ₗ[ℝ] ℝ => L (Pi.single j 1)) hz
  exact hj (hh.symm.trans hzero)

/-- Exact linear dimension of the local chart parameter space. -/
theorem polynomial_hypersurface_parameter_dimension {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
    (hr : ∃ j, eval a (pderiv j P) ≠ 0) :
    Module.finrank ℝ (fderiv ℝ (fun y => eval y P) a).ker + 1 = n := by
  simpa using Module.Dual.finrank_ker_add_one_of_ne_zero
    (polynomial_scalar_fderiv_ne_zero P a hr)

/-- An actual injective local Lipschitz chart at a regular hypersurface point.
The parameter norm is the inherited norm on the derivative kernel. -/
theorem polynomial_hypersurface_local_chart {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (a : Fin n → ℝ) (ha : eval a P = 0) (hr : ∃ j, eval a (pderiv j P) ≠ 0) :
    let A := fderiv ℝ (fun y => eval y P) a
    ∃ φ : A.ker → (Fin n → ℝ), ∃ V ∈ 𝓝 (0 : A.ker), ∃ U ∈ 𝓝 a,
      φ 0 = a ∧ LipschitzOnWith 2 φ V ∧ Set.InjOn φ V ∧
      (∀ y ∈ V, eval (φ y) P = 0) ∧
      (∀ x ∈ U, eval x P = 0 ↔ ∃ y ∈ V, φ y = x) := by
  dsimp only
  have hs : ContDiff ℝ 1 (fun y : Fin n → ℝ => eval y P) :=
    (polynomial_eval_contDiff P 1).comp (PiLp.contDiff_toLp (p := (2 : ENNReal)))
  have hne := polynomial_scalar_fderiv_ne_zero P a hr
  have hsurj := Module.Dual.range_eq_top_of_ne_zero hne
  simpa only [ha] using regular_local_lipschitz_chart (fun y => eval y P)
    (fderiv ℝ (fun y => eval y P) a) a (hs.hasStrictFDerivAt (by norm_num)) hsurj

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_scalar_fderiv_coordinate
#print axioms KakeyaTwoScale.polynomial_hypersurface_local_chart

#print axioms KakeyaTwoScale.polynomial_scalar_fderiv_ne_zero
#print axioms KakeyaTwoScale.polynomial_hypersurface_parameter_dimension
