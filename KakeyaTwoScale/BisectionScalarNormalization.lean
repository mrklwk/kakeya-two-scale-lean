module
public import KakeyaTwoScale.UniformCoordinateArea

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Scalar normalization of the actual assembled bisection inequality. Infinite
area is discharged separately; all real conversions then have proved finiteness. -/
theorem bisection_scalar_normalization (s t V W A : ℝ≥0∞) (M : ℝ)
    (hV : 0 < V) (hVf : V ≠ ∞) (hW : 0 < W) (hWf : W ≠ ∞) (hM : 0 < M)
    (hsV : s ≤ V) (htV : t ≤ V)
    (hs : (3/10:ℝ)*V.toReal ≤ s.toReal) (ht : (3/10:ℝ)*V.toReal ≤ t.toReal)
    (h : s*t*W ≤ (t+s)*ENNReal.ofReal M*A) :
    ENNReal.ofReal ((9/100:ℝ)*W.toReal/(2*M))*V ≤ A := by
  by_cases hAf : A=∞
  · simp [hAf]
  have hsf : s ≠ ∞ := ne_top_of_le_ne_top hVf hsV
  have htf : t ≠ ∞ := ne_top_of_le_ne_top hVf htV
  have hv : 0 < V.toReal := ENNReal.toReal_pos hV.ne' hVf
  have hw : 0 < W.toReal := ENNReal.toReal_pos hW.ne' hWf
  have hsr : s.toReal ≤ V.toReal := ENNReal.toReal_mono hVf hsV
  have htr : t.toReal ≤ V.toReal := ENNReal.toReal_mono hVf htV
  have hupperfinite : (t+s)*ENNReal.ofReal M*A ≠ ∞ := by finiteness
  have hh := ENNReal.toReal_mono hupperfinite h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_add htf hsf,ENNReal.toReal_ofReal hM.le] at hh
  have hlow := mul_le_mul hs ht (by positivity : 0 ≤ (3/10:ℝ)*V.toReal) ENNReal.toReal_nonneg
  have hlow' := mul_le_mul_of_nonneg_right hlow hw.le
  have hup := mul_le_mul_of_nonneg_right (show t.toReal+s.toReal ≤ 2*V.toReal by linarith)
    (mul_nonneg hM.le (ENNReal.toReal_nonneg (a := A)))
  have hn : (9/100:ℝ)*V.toReal*W.toReal ≤ 2*M*A.toReal := by
    by_contra! hn
    have hbad := mul_pos hv (sub_pos.mpr hn)
    nlinarith
  have hc : 0 ≤ (9/100:ℝ)*W.toReal/(2*M) := by positivity
  rw [← ENNReal.ofReal_toReal hVf,← ENNReal.ofReal_mul hc,← ENNReal.ofReal_toReal hAf]
  apply ENNReal.ofReal_le_ofReal
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 2*M)).mpr
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.bisection_scalar_normalization
