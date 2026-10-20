module
public import KakeyaTwoScale.RealCornerComparison
public import KakeyaTwoScale.IterationLogAlgebra

@[expose] public section

namespace KakeyaTwoScale

/-- Take logarithms of the proved finite comparison, preserving both SD
constants and both applications of the exponent beta. -/
theorem comparison_log (β C N W H L0 L1 d J : ℝ)
    (hβ : 1 < β) (hC : 0 < C) (hN : 0 < N) (hW : 0 < W) (hH : 0 < H)
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hd : 0 < d) (hJ : 0 < J)
    (hcomp : (C*(4*(4*J+1)*N*(W/(C*((8*d*J)/L1)^β)^(-1/(β-1)))/H)^β)^(-1/(β-1)) ≤ N*L0) :
    β*(β-1)*Real.log H+β^2*Real.log L1 ≤
      β*(β-1)*Real.log W+((2*β-1)*(β-1))*Real.log N+(β-1)^2*Real.log L0+
      β^2*Real.log (8*d*J)+(2*β-1)*Real.log C+β*(β-1)*Real.log (4*(4*J+1)) := by
  have hb : 0 < β-1 := by linarith
  let A := (C*((8*d*J)/L1)^β)^(-1/(β-1))
  have hA : 0 < A := by dsimp [A]; positivity
  have hinner : 0 < C*((8*d*J)/L1)^β := by positivity
  have hlogA : Real.log A = -(Real.log C+β*(Real.log (8*d*J)-Real.log L1))/(β-1) := by
    dsimp [A]
    rw [Real.log_rpow hinner,Real.log_mul (ne_of_gt hC) (by positivity),
      Real.log_rpow (by positivity),Real.log_div (by positivity) (ne_of_gt hL1)]
    ring
  let T := C*(4*(4*J+1)*N*(W/A)/H)^β
  have hT : 0 < T := by dsimp [T]; positivity
  have hlogT : Real.log T = Real.log C+β*(Real.log (4*(4*J+1))+Real.log N+Real.log W-Real.log A-Real.log H) := by
    dsimp [T]
    rw [Real.log_mul (ne_of_gt hC) (by positivity),Real.log_rpow (by positivity),
      Real.log_div (by positivity) (ne_of_gt hH),
      Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (ne_of_gt hN),
      Real.log_div (ne_of_gt hW) (ne_of_gt hA)]
    ring
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hT (-1/(β-1))) hcomp
  change Real.log (T^(-1/(β-1))) ≤ Real.log (N*L0) at hl
  rw [Real.log_rpow hT,hlogT,hlogA,Real.log_mul (ne_of_gt hN) (ne_of_gt hL0)] at hl
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (β-1))
  have hid : (β-1)^2 * ((-1/(β-1))*(Real.log C+β*(Real.log (4*(4*J+1))+Real.log N+
      Real.log W- (-(Real.log C+β*(Real.log (8*d*J)-Real.log L1))/(β-1))-Real.log H))) =
      β*(β-1)*Real.log H+β^2*Real.log L1-β*(β-1)*Real.log W-
      β*(β-1)*Real.log N-β^2*Real.log (8*d*J)-(2*β-1)*Real.log C-
      β*(β-1)*Real.log (4*(4*J+1)) := by
    field_simp [ne_of_gt hb]
    ring
  rw [hid] at hm
  nlinarith only [hm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.comparison_log
