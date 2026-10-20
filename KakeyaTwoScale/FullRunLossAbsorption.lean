module
public import KakeyaTwoScale.LogLoss
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Filter
namespace KakeyaTwoScale

/-- Entire fixed polylogarithmic loss, including every finite normalization
round, is absorbed after progress/accuracy parameters have been fixed. -/
theorem eventually_log_loss_absorbed (C J : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, C+J*Real.log q ≤ ε*q := by
  have ht : Tendsto (fun q : ℕ => C/(q:ℝ)+J*(Real.log q/(q:ℝ))) atTop (nhds (0+J*0)) :=
    (constant_over_nat_tendsto C).add (tendsto_const_nhds.mul log_over_nat_tendsto)
  have he : ∀ᶠ q : ℕ in atTop, C/(q:ℝ)+J*(Real.log q/(q:ℝ)) < ε := by
    exact (tendsto_order.mp ht).2 ε (by simpa using hε)
  filter_upwards [he,eventually_gt_atTop 0] with q hq hq0
  have hpos : (0:ℝ) < q := by exact_mod_cast hq0
  have hh := (div_lt_iff₀ hpos).mp (show (C+J*Real.log q)/(q:ℝ) < ε by
    simpa only [add_div,mul_div_assoc] using hq)
  exact hh.le

theorem eventually_full_polylog_absorbed {C ε : ℝ} (hC : 0 < C) (J : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, C*(q:ℝ)^J ≤ Real.exp (ε*q) := by
  filter_upwards [eventually_log_loss_absorbed (Real.log C) J hε,eventually_gt_atTop 0] with q hq hq0
  have hpos : (0:ℝ) < q := by exact_mod_cast hq0
  have hh := Real.exp_le_exp.mpr hq
  rw [Real.exp_add,Real.exp_log hC] at hh
  simpa only [Real.rpow_def_of_pos hpos,mul_comm J] using hh

/-- Ordered accuracy choice: total genuine per-round error is budgeted AFTER
the number T of rounds is known. Progress tau is not forced equal to gamma. -/
theorem ordered_accuracy_budget {ε B C T : ℝ} (hε : 0 < ε) (hB : 0 < B)
    (hC : 0 < C) (hT : 0 < T) :
    0 < ε/(16*B*C*T) ∧
      B*C*T*(ε/(16*B*C*T)) = ε/16 := by
  constructor
  · positivity
  · field_simp

/-- A uniform round bound follows from a positive macroscopic dyadic drop;
this is independent of the scale once tau is fixed. -/
theorem macroscopic_round_bound {R d B k : ℕ} {tau : ℝ} (htau : 0 < tau)
    (hB : 0 < B) (hdrop : tau*(B:ℝ)/2 ≤ d)
    (hbudget : R*d ≤ k*B+d*k) (hd : 0 < d) :
    (R:ℝ) ≤ 2*k/tau+k := by
  have hb : (0:ℝ) < B := by exact_mod_cast hB
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hbudget' : (R:ℝ)*d ≤ k*B+d*k := by exact_mod_cast hbudget
  have hdiv : (B:ℝ)/(d:ℝ) ≤ 2/tau := by
    apply (div_le_div_iff₀ hd' htau).mpr
    linarith
  have hr : (R:ℝ) ≤ (k:ℝ)*((B:ℝ)/d)+k := by
    have hh := (le_div_iff₀ hd').mpr hbudget'
    convert hh using 1
    field_simp
  have hk := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg (α:=ℝ) k)
  have he : (k:ℝ)*(2/tau)=2*k/tau := by ring
  rw [he] at hk
  linarith


/-- One explicit drop choice controls BOTH termination and the reset ceiling.
The small-scale threshold tau*N>=2 makes the natural floor positive. -/
theorem floor_drop_bounds {tau : ℝ} {N : ℕ} (hscale : 2 ≤ tau*(N:ℝ)) :
    0 < ⌊tau*(N:ℝ)⌋₊ ∧ tau*(N:ℝ)/2 ≤ (⌊tau*(N:ℝ)⌋₊:ℝ) ∧
      (⌊tau*(N:ℝ)⌋₊:ℝ) ≤ tau*(N:ℝ) := by
  have hlo := Nat.lt_floor_add_one (tau*(N:ℝ))
  refine ⟨Nat.floor_pos.mpr (by linarith),by linarith,Nat.floor_le (by linarith)⟩

theorem floor_drop_reset_bound {tau : ℝ} {N : ℕ} (hscale : 2 ≤ tau*(N:ℝ)) :
    (2:ℝ)^(⌊tau*(N:ℝ)⌋₊+1) ≤ 2*(2:ℝ)^(tau*(N:ℝ)) := by
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (floor_drop_bounds hscale).2.2
  rw [Real.rpow_natCast] at hh
  rw [pow_succ]
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_log_loss_absorbed
#print axioms KakeyaTwoScale.eventually_full_polylog_absorbed
#print axioms KakeyaTwoScale.ordered_accuracy_budget
#print axioms KakeyaTwoScale.macroscopic_round_bound

#print axioms KakeyaTwoScale.floor_drop_bounds
#print axioms KakeyaTwoScale.floor_drop_reset_bound
