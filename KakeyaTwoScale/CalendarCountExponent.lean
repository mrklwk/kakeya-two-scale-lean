module
public import KakeyaTwoScale.NestedCountCancellation

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- Fixed-calendar absorption preserves the exact dimension exponent. The
calendar and its depth budget are fixed before delta. -/
theorem calendar_count_exponent (n r R : ℕ) (K Q delta T : ℝ)
    (hK : 0≤K) (hQ : 1≤Q) (hd : 0<delta) (hT : 0<T) (hr : r≤R) :
    K*(Q*delta+delta)^r/(delta^n*T)≤
      (K*(Q+1)^R)*delta^((r:ℤ)-(n:ℤ))/T := by
  have he : Q*delta+delta=(Q+1)*delta := by ring
  rw [he,mul_pow,zpow_sub₀ hd.ne',zpow_natCast,zpow_natCast]
  have hp : (Q+1)^r≤(Q+1)^R := pow_le_pow_right₀ (by linarith) hr
  have hh := mul_le_mul_of_nonneg_left hp hK
  have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh (pow_nonneg hd.le r))
    (show 0≤delta^n*T by positivity)
  convert hh' using 1 <;> ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.calendar_count_exponent
