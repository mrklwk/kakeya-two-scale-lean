module
public import KakeyaTwoScale.RootLossPower

@[expose] public section

namespace KakeyaTwoScale

theorem root_band_epsilon_factor {B C k eta a L eps rate q : ℝ}
    (hB : 1<B) (hC : 0<C) (hq : 0≤q)
    (hbudget : k*eta+a*L*eps≤rate*(B-1)) :
    (C*(2:ℝ)^(k*eta*q)*Real.exp (a*L*(eps*q*Real.log 2)))^(1/(B-1)) ≤
      C^(1/(B-1))*(2:ℝ)^(rate*q) := by
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_rpow,Real.log_mul,Real.log_exp]
  have hh := mul_le_mul_of_nonneg_right hbudget (show 0≤q*Real.log 2 by positivity)
  apply (mul_le_mul_iff_of_pos_right (show 0<B-1 by linarith)).mp
  field_simp [show B-1≠0 by linarith]
  simp only [mul_div_cancel_left₀ _ (show B-1≠0 by linarith)]
  nlinarith only [hh]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.root_band_epsilon_factor
