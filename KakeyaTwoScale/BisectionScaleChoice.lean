module
public import KakeyaTwoScale.BisectionCrossingCheckpoint
public import Mathlib.Algebra.Order.Ring.Pow

@[expose] public section

open Set MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- All geometric scales are selected using dimension only, before the polynomial. -/
theorem exists_bisection_scales (N : ℕ) (hN : 1 ≤ N) :
    ∃ α b : ℝ, 0 < α ∧ α < 1 ∧ 0 < b ∧ b ≤ 1 ∧
      α^2+(N:ℝ)*b^2 < 1 ∧ (9/10:ℝ) < α^N := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ) < N := by linarith
  let h : ℝ := 1/(20*(N:ℝ))
  have hh : 0 < h := by dsimp [h]; positivity
  have hh20 : h ≤ 1/20 := by
    dsimp [h]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hNh : (N:ℝ)*h = 1/20 := by dsimp [h]; field_simp
  let α : ℝ := 1-h
  let b : ℝ := h/(2*((N:ℝ)+1))
  have ha : 0 < α := by dsimp [α]; linarith
  have ha1 : α < 1 := by dsimp [α]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hNb : ((N:ℝ)+1)*b = h/2 := by dsimp [b]; field_simp
  have hbh : b ≤ h := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ N) hb.le]
  have hNb' : (N:ℝ)*b ≤ h/2 := by nlinarith
  have hsq : (N:ℝ)*b^2 ≤ h^2/2 := by
    have h1 := mul_le_mul_of_nonneg_right hNb' hb.le
    have h2 := mul_le_mul_of_nonneg_left hbh (by positivity : 0 ≤ h/2)
    nlinarith
  have hbern := one_add_mul_sub_le_pow (by linarith : -1 ≤ α) N
  refine ⟨α,b,ha,ha1,hb,by linarith,?_,?_⟩
  · dsimp [α]
    nlinarith
  · dsimp [α] at hbern
    nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_bisection_scales
