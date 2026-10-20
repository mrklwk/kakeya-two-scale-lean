module
public import KakeyaTwoScale.GeometricOriginalCountMass

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Cancel only strictly positive geometric factors. The count is a natural
number, so no infinity is lost in converting the proved outer-measure bound. -/
theorem nested_count_cancel (n r N : ℕ) (K radius delta L T a H : ℝ)
    (hK : 0<K) (hr : 0<radius) (hd : 0<delta) (hL : 0<L) (hT : 0<T)
    (ha : 0<a) (hH : 0<H)
    (hmass : ((N:ℝ≥0∞)*ENNReal.ofReal ((2*(delta/(a*H)))^n))*
      ENNReal.ofReal ((L/a)^(n+1))≤ENNReal.ofReal (K*(radius^r*L^n/T))) :
    (N:ℝ)≤(K*(a*H/2)^n*a^(n+1))*radius^r/(delta^n*(L*T)) := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (show 0≤(2*(delta/(a*H)))^n by positivity),
    ENNReal.toReal_ofReal (show 0≤(L/a)^(n+1) by positivity),
    ENNReal.toReal_ofReal (show 0≤K*(radius^r*L^n/T) by positivity)] at hh
  have hm : (N:ℝ)≤(K*(radius^r*L^n/T))/((2*(delta/(a*H)))^n*(L/a)^(n+1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hh]
  refine hm.trans_eq ?_
  simp only [pow_succ,mul_pow,div_pow]
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.nested_count_cancel
