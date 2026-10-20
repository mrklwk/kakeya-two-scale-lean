module
public import KakeyaTwoScale.PolynomialSliceMultiplicity
public import KakeyaTwoScale.RegularMultiplicityLineSweep

@[expose] public section

open MeasureTheory Set MvPolynomial
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual polynomial-map Jacobian bound with explicit degree multiplicity.
Neither injectivity nor a finite-fiber premise is supplied. -/
theorem polynomial_jacobian_bound {m D : ℕ}
    (P : Fin m → MvPolynomial (Fin m) ℝ) (hP : ∀ j, (P j).totalDegree ≤ D)
    {S : Set (Fin m → ℝ)} (hS : IsCompact S) :
    (∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ (polynomialMapPi P) x).det|) ≤
      (((4*D+1)^m : ℕ) : ℝ≥0∞) * volume (polynomialMapPi P '' S) := by
  have hc := polynomialMapPi_contDiff P 1
  have hd := fun x => (hc.differentiable (by norm_num) x).hasFDerivAt
  apply regular_fiber_jacobian_bound (polynomialMapPi P) (fderiv ℝ (polynomialMapPi P))
    (hc.continuous_fderiv (by norm_num)) hd hS ((4*D+1)^m)
  intro z
  exact regular_polynomial_restricted_fiber_encard_le P hP
    (fderiv ℝ (polynomialMapPi P)) hd S z

/-- The actual polynomial-chart HRZ direction/sweep inequality. All regular
fiber and smoothness hypotheses are discharged from polynomial coefficients.
The degree factor is coarse but uniform: (4D+1)^m, independent of coefficients,
time, S and L. General semialgebraic parametrization is a separate dependency. -/
theorem polynomialLineSweep_direction_volume (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ)
      (P Q : Fin m → MvPolynomial (Fin m) ℝ),
      (∀ j, (P j).totalDegree ≤ D) → (∀ j, (Q j).totalDegree ≤ D) →
      ∀ (S : Set (Fin m → ℝ)), IsCompact S → ∀ a L : ℝ, 0 < L →
      volume (polynomialMapPi Q '' S) * ENNReal.ofReal (L^(m+1)) ≤
        (ENNReal.ofReal C * (((4*D+1)^m : ℕ) : ℝ≥0∞)) *
          (volume.prod volume)
            (differentiableLineSweep (polynomialMapPi P) (polynomialMapPi Q) S a L) := by
  obtain ⟨C,hC,h⟩ := regularMultiplicityLineSweep_direction_volume m
  refine ⟨C,hC,?_⟩
  intro D P Q hP hQ S hS a L hL
  have hcP := polynomialMapPi_contDiff P 1
  have hcQ := polynomialMapPi_contDiff Q 1
  have hdP := fun x => (hcP.differentiable (by norm_num) x).hasFDerivAt
  have hdQ := fun x => (hcQ.differentiable (by norm_num) x).hasFDerivAt
  apply h (polynomialMapPi P) (polynomialMapPi Q)
    (fderiv ℝ (polynomialMapPi P)) (fderiv ℝ (polynomialMapPi Q))
    (hcP.continuous_fderiv (by norm_num)) (hcQ.continuous_fderiv (by norm_num))
    hdP hdQ S hS a L hL ((4*D+1)^m)
  intro t _ z
  exact polynomialSlice_regular_encard_le P Q hP hQ _ _ hdP hdQ S t z

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_jacobian_bound
#print axioms KakeyaTwoScale.polynomialLineSweep_direction_volume
