module
public import KakeyaTwoScale.PolynomialGrowth

@[expose] public section

open Set MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Explicit radius bound for the nonnegative superlevel of the perturbation.
The coefficient norm is that of P²; no generic choice of ε is required. -/
theorem coercivePolynomialPerturbation_superlevel_norm_le {n D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D) (ε : ℝ) (hε : 0 < ε)
    (x : Fin n → ℝ) (hx : 0 ≤ eval x (coercivePolynomialPerturbation P D ε)) :
    ‖x‖ ≤ max 1 (polynomialCoefficientNorm (P^2) / ε) := by
  by_cases hnorm : ‖x‖ ≤ 1
  · exact hnorm.trans (le_max_left _ _)
  have hnorm1 : 1 ≤ ‖x‖ := le_of_not_ge hnorm
  have hnorm0 : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hnorm1
  have hn : 0 < n := by
    by_contra! h
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero h
    subst n
    have hx0 : x = 0 := Subsingleton.elim _ _
    rw [hx0,norm_zero] at hnorm0
    exact lt_irrefl 0 hnorm0
  let C := polynomialCoefficientNorm (P^2)
  have hbound : ‖eval x (P^2)‖ ≤ C * ‖x‖^(2*D) :=
    polynomial_eval_norm_le (P^2) ((totalDegree_pow P 2).trans (Nat.mul_le_mul_left 2 hP))
      x ‖x‖ hnorm1 (norm_le_pi_norm x)
  have heven : Even (2*D+2) := ⟨D+1,by omega⟩
  have hsum := even_power_sum_ge_norm hn heven x
  have hF : ε * (1 + ∑ i, x i ^ (2*D+2)) ≤ eval x (P^2) := by
    simpa only [coercivePolynomialPerturbation,map_sub,map_mul,map_add,eval_C,map_one,
      map_sum,map_pow,eval_X,sub_nonneg] using hx
  have hp : ε * ‖x‖^(2*D+2) ≤ C * ‖x‖^(2*D) := by
    calc
      _ ≤ ε * (1 + ∑ i, x i ^ (2*D+2)) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ ≤ eval x (P^2) := hF
      _ ≤ ‖eval x (P^2)‖ := le_abs_self _
      _ ≤ _ := hbound
  have hcancel : ε * ‖x‖^2 ≤ C := by
    apply (mul_le_mul_iff_left₀ (pow_pos hnorm0 (2*D))).mp
    rw [pow_add] at hp
    convert hp using 1
    ring
  have hsq : ‖x‖ ≤ ‖x‖^2 := by nlinarith
  apply le_trans _ (le_max_right _ _)
  apply (le_div_iff₀ hε).mpr
  nlinarith

/-- Every nonnegative-threshold superlevel is genuinely compact. -/
theorem coercivePolynomialPerturbation_superlevel_isCompact {n D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) (ha : 0 ≤ a) :
    IsCompact {x : Fin n → ℝ | a ≤ eval x (coercivePolynomialPerturbation P D ε)} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le continuous_const (coercivePolynomialPerturbation P D ε).continuous_eval
  · apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨max 1 (polynomialCoefficientNorm (P^2) / ε),?_⟩
    intro x hx
    exact coercivePolynomialPerturbation_superlevel_norm_le P hP ε hε x (ha.trans hx)

/-- Positive values of the perturbation lie in the original polynomial's
complement, including at singular zeroes of P. -/
theorem coercivePolynomialPerturbation_pos_nonzero {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (D : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Fin n → ℝ) (hx : 0 < eval x (coercivePolynomialPerturbation P D ε)) :
    eval x P ≠ 0 := by
  intro hz
  have heven : Even (2*D+2) := ⟨D+1,by omega⟩
  have hsum : 0 ≤ ∑ i : Fin n, x i ^ (2*D+2) :=
    Finset.sum_nonneg (fun i _ => heven.pow_nonneg _)
  simp only [coercivePolynomialPerturbation,map_sub,map_mul,map_add,map_pow,eval_C,
    map_one,map_sum,eval_X,hz,zero_pow (by omega : (2:ℕ) ≠ 0),zero_sub] at hx
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coercivePolynomialPerturbation_superlevel_norm_le
#print axioms KakeyaTwoScale.coercivePolynomialPerturbation_superlevel_isCompact
#print axioms KakeyaTwoScale.coercivePolynomialPerturbation_pos_nonzero
