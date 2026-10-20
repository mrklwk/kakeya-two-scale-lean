module
public import KakeyaTwoScale.ArchiveComplexityCalendar

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Uniform upper-factor error for actual stages, with polynomial degree and
calendar fixed before scale. This is separate from retained mass: it pays the
cellular cancellation and the single macroscopic reset explicitly. -/
theorem eventually_actual_stage_upper (b c k A M J t R : ℕ) (hb : 0<b) (ht : 2 ≤ t)
    {tau epsilon : ℝ} (htau : 0<tau)
    (hrate : (M:ℝ)*(calendarRemainder b+
        Real.log (2*((bufferedStageOrientations b c).card:ℝ))/(b:ℝ))/((b*t:ℕ)-1:ℝ)+
        tau*Real.log 2<epsilon) :
    ∀ᶠ q : ℕ in atTop, ∀ (B Lh depth : ℕ) (T C O : Type) [DecidableEq T] [DecidableEq C]
      (I : BufferedStageInput b c k A B Lh J (b*t) depth T C O)
      (N : Fin k → ℝ) (P U : ℝ)
      (Z : ActualNormalizedBufferedStage I N P U ⌊tau*(q:ℝ)⌋₊),
      (∀ j ∈ Finset.range (b*t), I.D j=partitionBoxDegree b j) →
      depth ≤ B/(b*t-1)+1 → B ≤ M*q → Lh ≤ q → Z.rounds ≤ R → 1 ≤ U →
      Z.upperFactor ≤ U*Real.exp (epsilon*q) := by
  let m := (bufferedStageOrientations b c).card
  let rate := (M:ℝ)*(calendarRemainder b+Real.log (2*(m:ℝ))/(b:ℝ))/((b*t:ℕ)-1:ℝ)
  let E := max J (max (2*c*(J-1)) (b*(∑ j ∈ Finset.range (b*t), partitionBoxDegree b j)))
  let C0 := Real.log (2*(algebraicAxisCoverBudget (b+c) E:ℝ))+calendarRemainder b+
    (Real.log 2+seedLogConstant m (b*t) (b+c) k A M)/(b:ℝ)
  let poly : ℝ := (4*k+4)/(b:ℝ)
  have hg : 0<epsilon-(rate+tau*Real.log 2) := sub_pos.mpr hrate
  filter_upwards [eventually_log_succ_loss_absorbed (|C0|+(R+2:ℝ)*Real.log 2) poly hg] with q hq
  intro B Lh depth T C O _ _ I N P U Z hcalendar hd hB hLh hR hU
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hs : 2 ≤ b*t := by nlinarith
  have hsR : (2:ℝ) ≤ (b*t:ℕ) := by exact_mod_cast hs
  have hm : 1 ≤ Z.seed.orientations.card := Finset.card_pos.mpr Z.seed.orientations_nonempty
  have hmR : (1:ℝ) ≤ m := by simpa [m,Z.seed.orientations_canonical] using (show (1:ℝ) ≤ Z.seed.orientations.card by exact_mod_cast hm)
  have hlogm : 0 ≤ Real.log (2*(m:ℝ)) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hrem : 0 ≤ calendarRemainder b := by
    have hh : 0 ≤ Real.log (2*(b:ℝ)^2+1) := Real.log_nonneg (by nlinarith [sq_nonneg (b:ℝ)])
    unfold calendarRemainder
    positivity
  have hrate0 : 0 ≤ rate := by dsimp [rate]; exact div_nonneg (by positivity) (by linarith)
  have hpoly : 0 ≤ poly := by dsimp [poly]; positivity
  have hlogq : 0 ≤ Real.log (q+1:ℕ) := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 q)
  have hsum := Finset.sum_congr rfl hcalendar
  have hseed := Z.seed.log_normalizationUpper_le M q t ht rfl hcalendar hd hB hLh (show 0<U by linarith)
  rw [Z.seed.orientations_canonical,hsum] at hseed
  change Real.log (Z.seed.normalizationUpper U) ≤ Real.log U+rate*q+C0+poly*Real.log (q+1:ℕ) at hseed
  let K := rate*q+|C0|+poly*Real.log (q+1:ℕ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hseed' : Real.log (Z.seed.normalizationUpper U) ≤ Real.log U+K := by
    dsimp [K]
    linarith [le_abs_self C0]
  have hupper := Z.log_upperFactor_le_of_seed hU hK hseed'
  have ha : (⌊tau*(q:ℝ)⌋₊:ℝ) ≤ tau*(q:ℝ) := Nat.floor_le (by positivity)
  have hRR : (Z.rounds:ℝ) ≤ R := by exact_mod_cast hR
  have hreset := mul_le_mul_of_nonneg_right (add_le_add hRR ha) hlog2
  have hfinal : Real.log Z.upperFactor ≤ Real.log U+epsilon*q := by
    dsimp [K] at hupper
    push_cast at hupper hq
    nlinarith
  have hh := Real.exp_le_exp.mpr hfinal
  rwa [Real.exp_log Z.upperFactor_pos,Real.exp_add,Real.exp_log (show 0<U by linarith)] at hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_actual_stage_upper
