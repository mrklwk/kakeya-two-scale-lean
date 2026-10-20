module
public import KakeyaTwoScale.CapturedWorkingSegment

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

def recursionKappa (n : ℕ) : ℝ := 1/(4*(n+2:ℝ))
def recursionBeta (n : ℕ) : ℝ := recursionKappa n/8
def recursionDilation (n : ℕ) (B : ℝ) : ℝ := 8*(B+2)/recursionKappa n

theorem recursionKappa_pos (n : ℕ) : 0<recursionKappa n := by unfold recursionKappa; positivity
theorem recursionKappa_le_one (n : ℕ) : recursionKappa n≤1 := by
  unfold recursionKappa
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]
theorem recursionBeta_pos (n : ℕ) : 0<recursionBeta n := div_pos (recursionKappa_pos n) (by norm_num)
theorem recursionBeta_le_one (n : ℕ) : recursionBeta n≤1 := by
  have := recursionKappa_le_one n
  unfold recursionBeta
  linarith

theorem recursionDilation_beta (n : ℕ) (B : ℝ) :
    recursionDilation n B*recursionBeta n=B+2 := by
  unfold recursionDilation recursionBeta
  field_simp [ne_of_gt (recursionKappa_pos n)]

theorem recursionDilation_ge_one (n : ℕ) (B : ℝ) (hB : 0≤B) : 1≤recursionDilation n B := by
  unfold recursionDilation
  apply (le_div_iff₀ (recursionKappa_pos n)).mpr
  have := recursionKappa_le_one n
  linarith

/-- All scale inequalities needed by actual thickness and volume iteration. -/
theorem recursion_scale_conditions (n : ℕ) (B L l rho : ℝ)
    (hB : 0≤B) (hl : 0<l) (hlL : l≤L) (hrho : 0<rho) (hrhol : rho≤l/4) :
    0<recursionBeta n*rho ∧ recursionBeta n*rho≤recursionKappa n*l ∧
    1≤recursionDilation n B*L/l ∧
    1≤(recursionDilation n B*L/l)*recursionBeta n ∧ recursionBeta n*rho≤rho := by
  have hk := recursionKappa_pos n
  have hb := recursionBeta_pos n
  have hD := recursionDilation_ge_one n B hB
  have hDa : recursionDilation n B≤recursionDilation n B*L/l := by
    apply (le_div_iff₀ hl).mpr
    exact mul_le_mul_of_nonneg_left hlL (by linarith)
  refine ⟨mul_pos hb hrho,?_,hD.trans hDa,?_,?_⟩
  · unfold recursionBeta
    have hh := mul_le_mul_of_nonneg_left hrhol hk.le
    nlinarith [mul_pos hk hl]
  · have hh := mul_le_mul_of_nonneg_right hDa hb.le
    rw [recursionDilation_beta] at hh
    linarith
  · exact mul_le_of_le_one_left hrho.le (recursionBeta_le_one n)

/-- The fixed dilation is large enough to absorb nonnested midpoint shifts. -/
theorem recursion_axial_margin (n : ℕ) (B L l : ℝ)
    (hB : 0≤B) (hL : 0<L) (hl : 0<l) :
    2*(B+1)*L+recursionKappa n*L/2 <
      (recursionDilation n B*L/l)*(recursionKappa n*l)/2 := by
  have he : (recursionDilation n B*L/l)*(recursionKappa n*l)/2=4*(B+2)*L := by
    unfold recursionDilation
    field_simp [ne_of_gt (recursionKappa_pos n)]
    ring
  rw [he]
  have hk := mul_le_mul_of_nonneg_right (recursionKappa_le_one n) hL.le
  nlinarith [mul_nonneg hB hL.le]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.recursion_scale_conditions
#print axioms KakeyaTwoScale.recursion_axial_margin
