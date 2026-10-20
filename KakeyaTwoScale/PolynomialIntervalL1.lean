module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Polynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

private def coefficientPolynomial (m : ℕ) (c : Fin (m+1) → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

private theorem coefficientPolynomial_coeff (m : ℕ) (c : Fin (m+1) → ℝ)
    (i : Fin (m+1)) : (coefficientPolynomial m c).coeff i = c i := by
  classical
  simp [coefficientPolynomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, ← Fin.ext_iff]

private def unitMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

private theorem polynomial_unit_integrable (p : Polynomial ℝ) :
    Integrable (fun x => p.eval x) unitMeasure :=
  p.continuous.integrableOn_Icc

private def coefficientL1 (m : ℕ) : (Fin (m+1) → ℝ) →ₗ[ℝ] Lp ℝ 1 unitMeasure where
  toFun c := (polynomial_unit_integrable (coefficientPolynomial m c)).toL1 _
  map_add' c d := by
    apply Lp.ext
    filter_upwards [Integrable.coeFn_toL1 (polynomial_unit_integrable (coefficientPolynomial m (c+d))),
      Integrable.coeFn_toL1 (polynomial_unit_integrable (coefficientPolynomial m c)),
      Integrable.coeFn_toL1 (polynomial_unit_integrable (coefficientPolynomial m d)),
      Lp.coeFn_add ((polynomial_unit_integrable (coefficientPolynomial m c)).toL1 _)
        ((polynomial_unit_integrable (coefficientPolynomial m d)).toL1 _)] with x h₁ h₂ h₃ h₄
    simp_all [coefficientPolynomial, Finset.sum_add_distrib, add_mul]
  map_smul' r c := by
    apply Lp.ext
    filter_upwards [Integrable.coeFn_toL1 (polynomial_unit_integrable (coefficientPolynomial m (r • c))),
      Integrable.coeFn_toL1 (polynomial_unit_integrable (coefficientPolynomial m c)),
      Lp.coeFn_smul r ((polynomial_unit_integrable (coefficientPolynomial m c)).toL1 _)] with x h₁ h₂ h₃
    simp only [RingHom.id_apply]
    rw [h₁, h₃]
    simp only [Pi.smul_apply, smul_eq_mul, h₂]
    simp only [coefficientPolynomial, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

private theorem coefficientL1_injective (m : ℕ) : Function.Injective (coefficientL1 m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have he : (fun x => (coefficientPolynomial m c).eval x) =ᵐ[unitMeasure] 0 := by
    have h := Integrable.coeFn_toL1 (polynomial_unit_integrable (coefficientPolynomial m c))
    change (coefficientL1 m c : ℝ → ℝ) =ᵐ[unitMeasure] _ at h
    rw [hc] at h
    exact h.symm.trans (Lp.coeFn_zero _ _ _)
  have hp : coefficientPolynomial m c = 0 := by
    by_contra hp
    have hn : unitMeasure {x | (coefficientPolynomial m c).eval x = 0} = 0 := by
      apply le_antisymm _ zero_le
      calc
        unitMeasure {x | (coefficientPolynomial m c).eval x = 0} ≤
            volume {x | (coefficientPolynomial m c).eval x = 0} := Measure.restrict_apply_le _ _
        _ = 0 := (Polynomial.finite_setOfPred_isRoot hp).measure_zero volume
    have hne : ∀ᵐ x ∂unitMeasure, (coefficientPolynomial m c).eval x ≠ 0 := by
      simpa only [ae_iff, not_not] using hn
    have hf : ∀ᵐ x ∂unitMeasure, False := by
      filter_upwards [he, hne] with x hx hn
      exact hn hx
    have hu := ae_iff.mp hf
    simp [unitMeasure] at hu

  funext i
  have h := congrArg (fun p : Polynomial ℝ => p.coeff i) hp
  simpa [coefficientPolynomial_coeff] using h

/-- On the unit interval, all coefficients of a bounded-degree real polynomial
are controlled by its actual Lebesgue L1 norm. The constant depends only on m. -/
theorem polynomial_unit_interval_L1 (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Polynomial ℝ, p.natDegree ≤ m →
      ∀ i : Fin (m+1), |p.coeff i| ≤ C * ∫ x in (0:ℝ)..1, |p.eval x| := by
  obtain ⟨K, hK, hbound⟩ := (coefficientL1 m).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr (coefficientL1_injective m))
  refine ⟨K, by exact_mod_cast hK, ?_⟩
  intro p hp i
  let c : Fin (m+1) → ℝ := fun i => p.coeff i
  have hpoly : coefficientPolynomial m c = p := by
    simp only [coefficientPolynomial, c]
    rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (p.coeff k) * Polynomial.X ^ k)]
    exact (p.as_sum_range_C_mul_X_pow' (by omega)).symm
  have hn : ‖coefficientL1 m c‖ = ∫ x in (0:ℝ)..1, |p.eval x| := by
    rw [L1.norm_eq_integral_norm]
    calc
      (∫ x, ‖(coefficientL1 m c) x‖ ∂unitMeasure) = ∫ x, |p.eval x| ∂unitMeasure := by
        apply integral_congr_ae
        filter_upwards [Integrable.coeFn_toL1 (polynomial_unit_integrable
          (coefficientPolynomial m c))] with x hx
        change ‖((polynomial_unit_integrable (coefficientPolynomial m c)).toL1 _) x‖ = _
        rw [hx, hpoly, Real.norm_eq_abs]
      _ = _ := by rw [unitMeasure, intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  calc
    |p.coeff i| = ‖c i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖c‖ := norm_le_pi_norm c i
    _ ≤ (K : ℝ) * ‖coefficientL1 m c‖ := ZeroHomClass.bound_of_antilipschitz
      (coefficientL1 m) hbound c
    _ = _ := by rw [hn]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_unit_interval_L1
