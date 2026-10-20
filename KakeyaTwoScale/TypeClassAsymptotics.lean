module
public import KakeyaTwoScale.TypeClassCounting
public import KakeyaTwoScale.FiniteEntropyChain
public import Mathlib.Analysis.SpecialFunctions.Stirling

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Filter
open scoped Topology BigOperators

/-- The normalized logarithmic Stirling error tends to zero. -/
theorem factorial_log_remainder_tendsto :
    Tendsto (fun n : ℕ => (Real.log (n.factorial:ℝ)-(n:ℝ)*Real.log n+n)/(n:ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n => Real.log (Stirling.stirlingSeq n)) atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hnat
  have htwo : Tendsto (fun n : ℕ => Real.log (2:ℝ)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have ht := (hs.div_atTop hnat).add ((htwo.add hlog).const_mul (1/2:ℝ))
  simp only [zero_add,mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hf := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) (ne_of_gt hnR),
    Real.log_div (ne_of_gt hnR) (by positivity),Real.log_exp] at hf
  field_simp
  nlinarith only [hf]

/-- The logarithm of a factorial along a fixed integer multiple, after
removing the common c log k term. Zero multiplicities are included. -/
theorem scaled_factorial_log_tendsto (c : ℕ) :
    Tendsto (fun k : ℕ => Real.log ((c*k).factorial:ℝ)/(k:ℝ)-(c:ℝ)*Real.log k)
      atTop (𝓝 ((c:ℝ)*Real.log c-c)) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hcp : 0 < c := Nat.pos_of_ne_zero hc
  have hcR : (0:ℝ) < c := by exact_mod_cast hcp
  have hseq : Tendsto (fun k : ℕ => c*k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k hcp) tendsto_id
  have hh := ((factorial_log_remainder_tendsto.comp hseq).const_mul (c:ℝ)).add_const
    ((c:ℝ)*Real.log c-c)
  simp only [mul_zero,zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  simp only [Function.comp_def,Nat.cast_mul]
  rw [Real.log_mul (ne_of_gt hcR) (ne_of_gt hkR)]
  field_simp
  ring

/-- Logarithmic multinomial asymptotics for fixed symbol counts. This is
an analytic theorem about the exact factorial ratio, not an assumed type
class entropy estimate. -/
theorem multinomial_log_tendsto {A : Type*} (S : Finset A) (c : A → ℕ) :
    Tendsto (fun k : ℕ =>
      (Real.log (((∑ a ∈ S, c a)*k).factorial:ℝ)-
        ∑ a ∈ S, Real.log ((c a*k).factorial:ℝ))/(k:ℝ)) atTop
      (𝓝 (((∑ a ∈ S, c a):ℝ)*Real.log (∑ a ∈ S, c a)-
        ∑ a ∈ S, (c a:ℝ)*Real.log (c a))) := by
  have hs := tendsto_finsetSum S (fun a _ => scaled_factorial_log_tendsto (c a))
  have hh := (scaled_factorial_log_tendsto (∑ a ∈ S, c a)).sub hs
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_div,← Nat.cast_sum] at hh
  convert hh using 1
  · funext k
    ring
  · congr 1
    push_cast
    ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.factorial_log_remainder_tendsto
#print axioms KakeyaTwoScale.scaled_factorial_log_tendsto
#print axioms KakeyaTwoScale.multinomial_log_tendsto
