module
public import KakeyaTwoScale.RestrictedIndexParameters

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

theorem tail_power_domination (x δ : ℝ) (D : ℕ) (hx : 0 < x)
    (hgap : (2:ℝ)^(2*D+1) ≤ x^(2*(D:ℝ)*δ-1)) :
    2*x ≤ (x^δ/2)^(2*D) := by
  have h := mul_le_mul_of_nonneg_right hgap hx.le
  have he : x^(2*(D:ℝ)*δ-1)*x = x^(2*(D:ℝ)*δ) := by
    calc
      _ = x^(2*(D:ℝ)*δ-1)*x^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx]; congr 1; ring
  rw [he] at h
  rw [div_pow,← Real.rpow_natCast,← Real.rpow_mul hx.le]
  apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(2*D))).mpr
  convert h using 1 <;> simp only [pow_succ,Nat.cast_mul,Nat.cast_ofNat] <;> ring_nf

/-- Scalar absorption of the exceptional and Fourier-tail energy losses. -/
theorem pz_budget_absorption (m n l E t A c B X Y : ℝ)
    (hm : 0 ≤ m) (hn : 0 < n) (_ht : 0 < t) (hA : 0 < A) (hc : 0 < c)
    (hB : 0 < B) (hX : 0 < X)
    (hdensity : c*m ≤ n*l) (hE : E ≤ 5*B*X) (htail : 2*m/t ≤ 1)
    (hY : 10*A ≤ Y) (hlog : l ≤ c/(20*A*B)*(Y/X)) :
    A*(4*n+2*m*E+2*m*n/t) ≤ Y*n := by
  have hE1 := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2*m by positivity)
  have hE2 := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ 10*B*X/c by positivity)
  have hE3 : 2*m*E ≤ n*(10*B*X/c*l) := by
    have he : (10*B*X/c)*(c*m) = 2*m*(5*B*X) := by field_simp; ring
    rw [he] at hE2
    nlinarith
  have ht1 := mul_le_mul_of_nonneg_left htail hn.le
  have hbracket : 4*n+2*m*E+2*m*n/t ≤ 5*n+n*(10*B*X/c*l) := by
    have he : n*(2*m/t) = 2*m*n/t := by ring
    rw [he] at ht1
    linarith
  have hlog1 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ A*(10*B*X/c) by positivity)
  have he : A*(10*B*X/c)*(c/(20*A*B)*(Y/X)) = Y/2 := by field_simp; ring
  rw [he] at hlog1
  have hmain := mul_le_mul_of_nonneg_left hbracket hA.le
  have hlast := mul_le_mul_of_nonneg_left hlog1 hn.le
  nlinarith

theorem pz_count_absorption (m n l c X Y : ℝ) (hn : 0 ≤ n) (hc : 0 < c)
    (hX : 1 ≤ X) (hY : 0 ≤ Y) (hdensity : c*m ≤ n*l)
    (hlog : l ≤ (c/2)*(Y/X)) : 2*m ≤ Y*n := by
  have hXpos : 0 < X := by linarith
  have hquot : Y/X ≤ Y := (div_le_self hY hX)
  have hl : l ≤ (c/2)*Y := hlog.trans (mul_le_mul_of_nonneg_left hquot (by positivity))
  have h := hdensity.trans (mul_le_mul_of_nonneg_left hl hn)
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tail_power_domination
#print axioms KakeyaTwoScale.pz_budget_absorption
#print axioms KakeyaTwoScale.pz_count_absorption
