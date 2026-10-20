module
public import KakeyaTwoScale.HRZLogClosure

@[expose] public section

namespace KakeyaTwoScale

/-- Exact logarithmic conversion of the nested-count and common effective
length inequalities. The complete denominator error is kept explicit. -/
theorem long_prefix_log_constraint (n r : ℕ)
    {N P G delta Lprod ell Lambda E K weighted upper : ℝ}
    (hN : 0<N) (hP : 0<P) (hG : 0<G) (hd : 0<delta)
    (hLp : 0<Lprod) (hell : 0<ell) (hLambda : 0<Lambda) (hE : 0<E) (hK : 0<K)
    (hcount : N*P/G≤K*delta^((r:ℤ)-(n:ℤ))/Lprod)
    (hlength : Lambda≤E*ell*P)
    (hprod : (r:ℝ)*Real.log ell+weighted-upper≤Real.log Lprod) :
    Real.log (N*delta^n)+(r:ℝ)*Real.log (Lambda/delta)-
      (Real.log K+(r:ℝ)*Real.log E+upper) ≤
        Real.log G+((r:ℝ)-1)*Real.log P-weighted := by
  have hc := Real.log_le_log (div_pos (mul_pos hN hP) hG) hcount
  rw [Real.log_div (mul_ne_zero hN.ne' hP.ne') hG.ne',Real.log_mul hN.ne' hP.ne',
    Real.log_div (mul_ne_zero hK.ne' (zpow_ne_zero _ hd.ne')) hLp.ne',
    Real.log_mul hK.ne' (zpow_ne_zero _ hd.ne'),Real.log_zpow] at hc
  push_cast at hc
  have hl := Real.log_le_log hLambda hlength
  rw [Real.log_mul (mul_ne_zero hE.ne' hell.ne') hP.ne',Real.log_mul hE.ne' hell.ne'] at hl
  have hr : (0:ℝ)≤r := Nat.cast_nonneg _
  have hrl := mul_le_mul_of_nonneg_left hl hr
  rw [Real.log_mul hN.ne' (pow_ne_zero _ hd.ne'),Real.log_pow,
    Real.log_div hLambda.ne' hd.ne']
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.long_prefix_log_constraint
