module
public import KakeyaTwoScale.DyadicPrimeProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

/-- The sublinear error in the binomial prime-count argument. -/
theorem binomial_log_error_eventually : ∀ᶠ x : ℝ in atTop,
    Real.log x + Real.sqrt (2*x)*Real.log (2*x) ≤ (Real.log 4/6)*x := by
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have h1 := Real.isLittleO_log_id_atTop.def (show 0 < Real.log (4:ℝ)/12 by positivity)
  have h2 := (isLittleO_log_rpow_atTop (r := (1/2:ℝ)) (by norm_num)).def
    (show 0 < Real.log (4:ℝ)/24 by positivity)
  have ht : Tendsto (fun x : ℝ => 2*x) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [h1,ht.eventually h2,eventually_ge_atTop (0:ℝ)] with x h1 h2 hx
  simp only [Real.norm_eq_abs,id_eq] at h1 h2
  rw [abs_of_nonneg hx] at h1
  rw [← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg _)] at h2
  have hh1 : Real.log x ≤ Real.log 4/12*x := (le_abs_self _).trans h1
  have hh2 : Real.sqrt (2*x)*Real.log (2*x) ≤ (Real.log 4/12)*x := by
    have h := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) (Real.sqrt_nonneg (2*x))
    have hs := Real.mul_self_sqrt (show 0 ≤ 2*x by positivity)
    nlinarith
  linarith

/-- Finite logarithmic inequality, retaining every rounding error in the
binomial estimate. -/
theorem dyadic_prime_log_bound (n : ℕ) (hn : 4 ≤ n) :
    (n:ℝ)*Real.log 4 ≤ Real.log n + Real.sqrt (2*n)*Real.log (2*n) +
      (2*(n:ℝ)/3)*Real.log 4 + ((dyadicPrimes n).card:ℝ)*Real.log (2*n) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h2n : 0 < (2*n:ℝ) := by positivity
  have hb := centralBinom_le_dyadic_prime_count n (by omega)
  have hl := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have hnat : 4^n ≤ n*((2*n)^Nat.sqrt (2*n)*4^(2*n/3)*(2*n)^(dyadicPrimes n).card) :=
    hl.le.trans (Nat.mul_le_mul_left n hb)
  have hr : (4:ℝ)^n ≤ (n:ℝ)*((2*(n:ℝ))^Nat.sqrt (2*n)*4^(2*n/3)*
      (2*(n:ℝ))^(dyadicPrimes n).card) := by exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<4^n) hr
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hlog
  simp only [Real.log_pow] at hlog
  have hs : (Nat.sqrt (2*n):ℝ) ≤ Real.sqrt (2*(n:ℝ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Real.nat_sqrt_le_real_sqrt (a := 2*n))
  have hd : ((2*n/3:ℕ):ℝ) ≤ 2*(n:ℝ)/3 := by
    exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := 2*n) (n := 3))
  have hlog2 : 0 ≤ Real.log (2*(n:ℝ)) := Real.log_nonneg (by
    have hthree : (4:ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  have hlog4 : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hs hlog2,mul_le_mul_of_nonneg_right hd hlog4]

/-- A positive quantitative dyadic prime-density bound, obtained without PNT. -/
theorem dyadic_prime_density_eventually : ∀ᶠ n : ℕ in atTop,
    (Real.log 4/6)*(n:ℝ) ≤ ((dyadicPrimes n).card:ℝ)*Real.log (2*n) := by
  have he := tendsto_natCast_atTop_atTop.eventually binomial_log_error_eventually
  filter_upwards [he,eventually_ge_atTop (4:ℕ)] with n he hn
  have h := dyadic_prime_log_bound n (by omega)
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.binomial_log_error_eventually
#print axioms KakeyaTwoScale.dyadic_prime_log_bound
#print axioms KakeyaTwoScale.dyadic_prime_density_eventually
