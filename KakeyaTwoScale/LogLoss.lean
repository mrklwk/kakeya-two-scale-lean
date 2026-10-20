module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Comparison of exponents after taking logarithms at dyadic scales.
The frequently version supports a broad subsequence as well as eventual bounds. -/
open Filter
namespace KakeyaTwoScale

 theorem log_over_nat_tendsto :
    Tendsto (fun q : ℕ => Real.log (q : ℝ) / (q : ℝ)) atTop (nhds 0) := by
  simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

 theorem constant_over_nat_tendsto (C : ℝ) :
    Tendsto (fun q : ℕ => C / (q : ℝ)) atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using tendsto_const_nhds.mul
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))

 /-- A linear exponent gap cannot be paid for by a logarithmic loss,
 even if the estimate holds only on an unbounded set of natural scales. -/
 theorem exponent_le_of_frequently_log_bound (A B C L : ℝ)
    (h : ∃ᶠ q : ℕ in atTop, A*(q:ℝ) ≤ B*q+C+L*Real.log q) : A ≤ B := by
  have ht : Tendsto (fun q : ℕ => B + C/(q:ℝ) + L*(Real.log q/(q:ℝ)))
      atTop (nhds (B+0+L*0)) :=
    (tendsto_const_nhds.add (constant_over_nat_tendsto C)).add
      (tendsto_const_nhds.mul log_over_nat_tendsto)
  have hf : ∃ᶠ q : ℕ in atTop,
      A ≤ B + C/(q:ℝ) + L*(Real.log q/(q:ℝ)) := by
    apply (h.and_eventually (eventually_gt_atTop 0)).mono
    rintro q ⟨hq, hpos⟩
    have hp : (0:ℝ) < q := by exact_mod_cast hpos
    have hq := (le_div_iff₀ hp).2 hq
    convert hq using 1
    field_simp
  simpa using ge_of_tendsto_of_frequently ht hf

 theorem exponent_le_of_eventually_log_bound (A B C L : ℝ)
    (h : ∀ᶠ q : ℕ in atTop, A*(q:ℝ) ≤ B*q+C+L*Real.log q) : A ≤ B :=
  exponent_le_of_frequently_log_bound A B C L h.frequently

 /-- Remove an arbitrarily small loss after the scale limit. -/
 theorem le_of_forall_positive_loss (A B c : ℝ) (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → A-c*ε ≤ B) : A ≤ B := by
  by_contra! hAB
  have hp : 0 < (A-B)/(2*c) := div_pos (sub_pos.mpr hAB) (by positivity)
  have hh := h ((A-B)/(2*c)) hp
  have he : c*((A-B)/(2*c)) = (A-B)/2 := by field_simp
  rw [he] at hh
  linarith
theorem dyadic_power_eq_exp (q : ℕ) (E : ℝ) :
    ((2:ℝ)^(-(q:ℝ)))^E = Real.exp (-Real.log 2*E*q) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), ← Real.exp_mul]
  congr 1
  ring

/-- Dyadic power bounds with an arbitrary fixed power of q as loss.
At rho=2^(-q), exp(-log(2)*E*q) is rho^E. No regularity of V is needed. -/
theorem exponent_le_of_dyadic_envelopes (V : ℕ → ℝ) (A B c C L : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (h : ∃ᶠ q : ℕ in atTop,
      c * Real.exp (-Real.log 2 * B * q) / (q:ℝ)^L ≤ V q ∧
      V q ≤ C * Real.exp (-Real.log 2 * A * q)) : A ≤ B := by
  have hg : ∃ᶠ q : ℕ in atTop,
      (Real.log 2*A)*(q:ℝ) ≤ (Real.log 2*B)*q +
        (Real.log C-Real.log c) + L*Real.log q := by
    apply (h.and_eventually (eventually_gt_atTop 0)).mono
    rintro q ⟨⟨hl,hu⟩,hq⟩
    have hp : (0:ℝ) < q := by exact_mod_cast hq
    have hlog := Real.log_le_log (by positivity :
      0 < c * Real.exp (-Real.log 2 * B * q) / (q:ℝ)^L) (hl.trans hu)
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (ne_of_gt hc) (by positivity),
      Real.log_mul (ne_of_gt hC) (by positivity),
      Real.log_rpow hp, Real.log_exp, Real.log_exp] at hlog
    linarith
  have he := exponent_le_of_frequently_log_bound _ _ _ _ hg
  exact (mul_le_mul_iff_right₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).1 he

end KakeyaTwoScale

#print axioms KakeyaTwoScale.exponent_le_of_frequently_log_bound
#print axioms KakeyaTwoScale.le_of_forall_positive_loss

#print axioms KakeyaTwoScale.exponent_le_of_dyadic_envelopes
