module
public import KakeyaTwoScale.PolynomialIntervalL1
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

open MeasureTheory Polynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Evaluation, including outside the interval, controlled by actual unit-interval L1. -/
theorem polynomial_unit_extrapolation_L1 (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ p : Polynomial ℝ, p.natDegree≤m → ∀ t : ℝ,
      |p.eval t| ≤ C * (max 1 |t|)^m * ∫ x in (0:ℝ)..1, |p.eval x| := by
  obtain ⟨K,hK,h⟩ := polynomial_unit_interval_L1 m
  refine ⟨(m+1)*K, mul_pos (by positivity) hK, ?_⟩
  intro p hp t
  let H := ∫ x in (0:ℝ)..1, |p.eval x|
  have hH : 0≤H := intervalIntegral.integral_nonneg zero_le_one (fun x _ => abs_nonneg _)
  have hM : 1≤max 1 |t| := le_max_left _ _
  have he : p.eval t = ∑ i ∈ Finset.range (m+1), p.coeff i*t^i := by
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree<m+1)]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [he]
  calc
    |∑ i ∈ Finset.range (m+1), p.coeff i*t^i| ≤
        ∑ i ∈ Finset.range (m+1), |p.coeff i*t^i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (m+1), (K*H)*(max 1 |t|)^m := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i≤m := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [abs_mul, abs_pow]
      exact mul_le_mul (h p hp ⟨i,Finset.mem_range.mp hi⟩)
        ((pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) i).trans (pow_le_pow_right₀ hM him))
        (by positivity) (mul_nonneg hK.le hH)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- Exact affine rescaling: evaluation at any point costs the m-th power of
its normalized distance, while interval integration contributes one length. -/
theorem polynomial_interval_extrapolation_L1 (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ p : Polynomial ℝ, p.natDegree≤m → ∀ a L t₀ : ℝ, 0<L →
      |p.eval t₀| *L ≤ C*(max 1 |(t₀-a)/L|)^m * ∫ t in a..(a+L), |p.eval t| := by
  obtain ⟨C,hC,h⟩ := polynomial_unit_extrapolation_L1 m
  refine ⟨C,hC,?_⟩
  intro p hp a L t₀ hL
  let q := p.comp (Polynomial.C L*Polynomial.X+Polynomial.C a)
  have hq : q.natDegree≤m := by
    have ha : (Polynomial.C L*Polynomial.X+Polynomial.C a).natDegree≤1 := by compute_degree
    exact Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hp ha).trans (by simp))
  have he (s : ℝ) : q.eval s=p.eval (a+L*s) := by simp [q, add_comm]
  have hval : q.eval ((t₀-a)/L)=p.eval t₀ := by
    rw [he]
    congr 1
    field_simp
    ring
  have hi : L*(∫ s in (0:ℝ)..1, |q.eval s|)=∫ t in a..(a+L), |p.eval t| := by
    simp_rw [he]
    simpa using intervalIntegral.smul_integral_comp_add_mul
      (fun t => |p.eval t|) (a := (0:ℝ)) (b := 1) L a
  have hh := mul_le_mul_of_nonneg_right (h q hq ((t₀-a)/L)) hL.le
  rw [hval] at hh
  calc
    |p.eval t₀| *L ≤ (C*(max 1 |(t₀-a)/L|)^m * ∫ s in (0:ℝ)..1, |q.eval s|)*L := hh
    _ = _ := by rw [← hi]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_unit_extrapolation_L1
#print axioms KakeyaTwoScale.polynomial_interval_extrapolation_L1
