module
public import KakeyaTwoScale.DeterminantPencilExtrapolation
public import KakeyaTwoScale.PolynomialHRZVolume

@[expose] public section

open MeasureTheory Set MvPolynomial
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual fixed-time slice volume controlled by the full swept volume,
including extrapolation outside the swept interval, for differentiable
position and slope maps with continuous derivatives and bounded regular fibers in each time slice.
No Jacobian integral or volume comparison is assumed. -/
theorem regularMultiplicityLineSweep_slice_volume (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀
      (F G : (Fin m → ℝ) → (Fin m → ℝ))
      (DF DG : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ))),
      Continuous DF → Continuous DG →
      (∀ y, HasFDerivAt F (DF y) y) → (∀ y, HasFDerivAt G (DG y) y) →
      ∀ (S : Set (Fin m → ℝ)), IsCompact S → ∀ a L t₀ : ℝ, 0 < L →
      ∀ N : ℕ,
      (∀ t ∈ Icc a (a+L), ∀ z,
        ({y | y∈S ∧ (DF y+t • DG y).det≠0 ∧ F y+t • G y=z} : Set (Fin m → ℝ)).encard ≤ N) →
      volume ((fun y => F y+t₀ • G y) '' S) * ENNReal.ofReal L ≤
        (ENNReal.ofReal (C*(max 1 |(t₀-a)/L|)^m) * N) * (volume.prod volume) (differentiableLineSweep F G S a L) := by
  obtain ⟨C,hC,h⟩ := clm_pencil_extrapolation m
  refine ⟨C,hC,?_⟩
  intro F G DF DG hcDF hcDG hF hG S hS a L t₀ hL N hmult
  have hpoint (y : Fin m → ℝ) :
      ENNReal.ofReal |(DF y+t₀ • DG y).det| * ENNReal.ofReal L ≤
      ENNReal.ofReal (C*(max 1 |(t₀-a)/L|)^m) * ∫⁻ t in Icc a (a+L), ENNReal.ofReal |(DF y+t • DG y).det| := by
    have hc : Continuous (fun t : ℝ => |(DF y+t • DG y).det|) :=
      (ContinuousLinearMap.continuous_det.comp
        (continuous_const.add (continuous_id.smul continuous_const))).abs
    have hp := ENNReal.ofReal_le_ofReal (h (DF y) (DG y) a L t₀ hL)
    rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (mul_nonneg hC.le (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) m))] at hp
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)] at hp
    exact hp
  have hj : AEMeasurable (fun z : (Fin m → ℝ) × ℝ =>
      ENNReal.ofReal |(DF z.1+z.2 • DG z.1).det|)
      ((volume.restrict S).prod (volume.restrict (Icc a (a+L)))) := by
    exact (ENNReal.continuous_ofReal.comp (ContinuousLinearMap.continuous_det.comp
      ((hcDF.comp continuous_fst).add (continuous_snd.smul (hcDG.comp continuous_fst)))).abs).measurable.aemeasurable
  calc
    volume ((fun y => F y+t₀ • G y) '' S) * ENNReal.ofReal L ≤
        (∫⁻ y in S, ENNReal.ofReal |(DF y+t₀ • DG y).det|) * ENNReal.ofReal L := by
      exact mul_le_mul (addHaar_image_le_lintegral_abs_det_fderiv volume hS.measurableSet
        (fun y _ => ((hF y).add ((hG y).const_smul t₀)).hasFDerivWithinAt)) le_rfl zero_le zero_le
    _ = ∫⁻ y in S, ENNReal.ofReal |(DF y+t₀ • DG y).det| * ENNReal.ofReal L := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y in S, ENNReal.ofReal (C*(max 1 |(t₀-a)/L|)^m) *
        ∫⁻ t in Icc a (a+L), ENNReal.ofReal |(DF y+t • DG y).det| := lintegral_mono hpoint
    _ = ENNReal.ofReal (C*(max 1 |(t₀-a)/L|)^m) * ∫⁻ t in Icc a (a+L),
        ∫⁻ y in S, ENNReal.ofReal |(DF y+t • DG y).det| := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hj]
    _ ≤ ENNReal.ofReal (C*(max 1 |(t₀-a)/L|)^m) * ((N : ℝ≥0∞) *
        (volume.prod volume) (differentiableLineSweep F G S a L)) :=
      mul_le_mul le_rfl (regularMultiplicityLineSweep_jacobian F G DF DG hcDF hcDG hF hG hS a L N hmult)
        zero_le zero_le
    _ = _ := by rw [mul_assoc]

/-- The polynomial-chart slice estimate in the HRZ interval-volume argument.
Smoothness and regular-fiber multiplicity are proved from the actual coefficients;
no nonzero determinant, injectivity, or finite-fiber premise is assumed. -/
theorem polynomialLineSweep_slice_volume (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (D : ℕ) (P Q : Fin m → MvPolynomial (Fin m) ℝ),
      (∀ j, (P j).totalDegree≤D) → (∀ j, (Q j).totalDegree≤D) →
      ∀ (S : Set (Fin m → ℝ)), IsCompact S → ∀ a L t₀ : ℝ, 0<L →
      volume ((fun y => polynomialMapPi P y+t₀ • polynomialMapPi Q y) '' S) * ENNReal.ofReal L ≤
        (ENNReal.ofReal (C*(max 1 |(t₀-a)/L|)^m) * (((4*D+1)^m : ℕ) : ℝ≥0∞)) *
          (volume.prod volume)
            (differentiableLineSweep (polynomialMapPi P) (polynomialMapPi Q) S a L) := by
  obtain ⟨C,hC,h⟩ := regularMultiplicityLineSweep_slice_volume m
  refine ⟨C,hC,?_⟩
  intro D P Q hP hQ S hS a L t₀ hL
  have hcP := polynomialMapPi_contDiff P 1
  have hcQ := polynomialMapPi_contDiff Q 1
  have hdP := fun x => (hcP.differentiable (by norm_num) x).hasFDerivAt
  have hdQ := fun x => (hcQ.differentiable (by norm_num) x).hasFDerivAt
  apply h (polynomialMapPi P) (polynomialMapPi Q)
    (fderiv ℝ (polynomialMapPi P)) (fderiv ℝ (polynomialMapPi Q))
    (hcP.continuous_fderiv (by norm_num)) (hcQ.continuous_fderiv (by norm_num))
    hdP hdQ S hS a L t₀ hL ((4*D+1)^m)
  intro t _ z
  exact polynomialSlice_regular_encard_le P Q hP hQ _ _ hdP hdQ S t z

end KakeyaTwoScale
#print axioms KakeyaTwoScale.regularMultiplicityLineSweep_slice_volume

#print axioms KakeyaTwoScale.polynomialLineSweep_slice_volume
