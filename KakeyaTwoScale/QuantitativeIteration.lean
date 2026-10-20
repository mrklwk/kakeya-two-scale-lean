module
public import KakeyaTwoScale.ComparisonLog

@[expose] public section

namespace KakeyaTwoScale
noncomputable def iterationBoundConstant (β C p J : ℝ) : ℝ :=
  Real.exp ((β*(β-1)*(Real.log (4*p)+Real.log 2+Real.log (4*(4*J+1)))+
    (β-1)^2*Real.log 2+β^2*Real.log (16*J)+(2*β-1)*(Real.log C+Real.log (4*p^2)))/
      (β^2+3*β-2))

/-- Quantitative exponent extraction from the finite comparison and the
proved mass/scale bounds. The loss is explicitly at most 102/M. -/
theorem quantitative_iteration_bound (β C p J M ρ g N W l E H L0 L1 d : ℝ)
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hM : 0 < M) (hρ : 0 ≤ ρ)
    (hC : 0 < C) (hp : 0 < p) (hJ : 0 < J) (hg : 0 < g) (hN : 1 ≤ N)
    (hW : 0 < W) (hl : 0 < l) (hE : 0 < E) (hH : 0 < H)
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hd : 0 < d)
    (hcomp : (C*(4*(4*J+1)*N*(W/(C*((8*d*J)/L1)^β)^(-1/(β-1)))/H)^β)^(-1/(β-1)) ≤ N*L0)
    (hcorner : l*E ≤ 2*H) (heps : N^(-2/M)*W ≤ E)
    (hnext : W*N^(ρ-100/M-2) ≤ L1) (hcurrent : L0 ≤ 2*W*N^(ρ-2))
    (hpop : d ≤ 2*N^(100/M)) (hwing : g ≤ 4*p*N*l) (hmass : g^2 ≤ 4*p^2*N*W) :
    g ≤ iterationBoundConstant β C p J * N^(realArithmeticStep β+102/M) := by
  have hNp : 0 < N := by linarith
  have hf := comparison_log β C N W H L0 L1 d J hβ hC hNp hW hH hL0 hL1 hd hJ hcomp
  have hh : Real.log l+Real.log E-Real.log 2 ≤ Real.log H := by
    have h := Real.log_le_log (mul_pos hl hE) hcorner
    rw [Real.log_mul (ne_of_gt hl) (ne_of_gt hE),Real.log_mul (by norm_num) (ne_of_gt hH)] at h
    linarith
  have he : Real.log W-2/M*Real.log N ≤ Real.log E := by
    have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hNp _) hW) heps
    rw [Real.log_mul (by positivity) (ne_of_gt hW),Real.log_rpow hNp] at h
    rw [neg_div] at h
    linarith
  have hnxt : Real.log W+(ρ-100/M-2)*Real.log N ≤ Real.log L1 := by
    have h := Real.log_le_log (mul_pos hW (Real.rpow_pos_of_pos hNp _)) hnext
    rwa [Real.log_mul (ne_of_gt hW) (by positivity),Real.log_rpow hNp] at h
  have hcur : Real.log L0 ≤ Real.log 2+Real.log W+(ρ-2)*Real.log N := by
    have h := Real.log_le_log hL0 hcurrent
    rwa [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (ne_of_gt hW),Real.log_rpow hNp] at h
  have hkd : Real.log (8*d*J) ≤ Real.log (16*J)+100/M*Real.log N := by
    have hm := mul_le_mul_of_nonneg_left hpop (show 0 ≤ 8*J by positivity)
    have hmul : 8*d*J ≤ (16*J)*N^(100/M) := by nlinarith only [hm]
    have h := Real.log_le_log (by positivity : 0 < 8*d*J) hmul
    rwa [Real.log_mul (show 16*J ≠ 0 by positivity) (by positivity),Real.log_rpow hNp] at h
  have hlg : Real.log g-Real.log (4*p)-Real.log N ≤ Real.log l := by
    have h := Real.log_le_log hg hwing
    rw [Real.log_mul (by positivity) (ne_of_gt hl),Real.log_mul (by positivity) (ne_of_gt hNp)] at h
    linarith
  have hwg : 2*Real.log g-Real.log (4*p^2)-Real.log N ≤ Real.log W := by
    have h := Real.log_le_log (sq_pos_of_pos hg) hmass
    rw [Real.log_pow,Real.log_mul (by positivity) (ne_of_gt hW),Real.log_mul (by positivity) (ne_of_gt hNp)] at h
    norm_num at h
    linarith
  have hx := iteration_log_elimination β M ρ (Real.log g) (Real.log N) (Real.log W)
    (Real.log l) (Real.log E) (Real.log H) (Real.log L0) (Real.log L1)
    (Real.log (8*d*J)) (Real.log (4*(4*J+1))) (Real.log C) (Real.log (4*p))
    (Real.log (4*p^2)) (Real.log 2) (Real.log (16*J)) hβ hβ2 hM hρ
    (Real.log_nonneg hN) hf hh he hnxt hcur hkd hlg hwg
  have hh := Real.exp_le_exp.mpr hx
  rw [Real.exp_log hg,Real.exp_add] at hh
  simpa only [iterationBoundConstant,Real.rpow_def_of_pos hNp,mul_comm (Real.log N)] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.quantitative_iteration_bound
