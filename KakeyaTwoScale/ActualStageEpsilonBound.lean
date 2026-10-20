module
public import KakeyaTwoScale.ExplicitEpsilonCalendar

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- A uniform theorem about every actual normalized stage, not a supplied
loss oracle. The threshold precedes the finite data, polynomial degree,
original cardinality, heights and the constructed stage. -/
theorem eventually_actual_stage_retention (b c k A M s R : ℕ)
    {epsilon : ℝ} (hs : 2 ≤ s)
    (hrate : (M:ℝ)*Real.log (2*((bufferedStageOrientations b c).card:ℝ))/((s:ℝ)-1)<epsilon) :
    ∀ᶠ q : ℕ in atTop, ∀ (B Lh J depth a : ℕ) (T C O : Type)
      [DecidableEq T] [DecidableEq C]
      (I : BufferedStageInput b c k A B Lh J s depth T C O)
      (N : Fin k → ℝ) (P U : ℝ) (Z : ActualNormalizedBufferedStage I N P U a),
      depth ≤ B/(s-1)+1 → B ≤ M*q → Lh ≤ q → Z.rounds ≤ R →
      Z.retentionLoss ≤ Real.exp (epsilon*q) := by
  let m := (bufferedStageOrientations b c).card
  let C0 := seedLogConstant m s (b+c) k A M+
    (R:ℝ)*(k*Real.log 3+(b+c)*Real.log (2*(A+(b+c)+5)+1:ℕ)+(k+1)*Real.log (M+1:ℕ))
  let J0 : ℝ := 4*k+4+R*(k+1)
  filter_upwards [eventually_uniform_log_envelope
    ((M:ℝ)*Real.log (2*(m:ℝ))/((s:ℝ)-1)) C0 J0 epsilon hrate] with q hq
  intro B Lh J depth a T C O _ _ I N P U Z hd hB hLh hR
  apply hq Z.retentionLoss Z.retentionLoss_pos
  have h := Z.log_retentionLoss_le M q R hs hd hB hLh hR
  simpa only [Z.seed.orientations_canonical] using h

namespace ActualNormalizedBufferedStage
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {I : BufferedStageInput b c k A B Lh J s depth T C O} {N : Fin k → ℝ} {P U : ℝ} {a : ℕ}

/-- Reset is paid once per dimension stage. It is not multiplied by the
number of normalization rounds. K is the displayed seed logarithmic ledger. -/
theorem log_upperFactor_le_of_seed (Z : ActualNormalizedBufferedStage I N P U a)
    {K : ℝ} (hU : 1 ≤ U) (hK : 0 ≤ K)
    (hseed : Real.log (Z.seed.normalizationUpper U) ≤ Real.log U+K) :
    Real.log Z.upperFactor ≤ Real.log U+K+(Z.rounds+a+2:ℝ)*Real.log 2 := by
  have hlog : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  have hcross : 0<Z.seed.crossing := by
    dsimp [ActualSynchronizedBufferedSeed.crossing,algebraicAxisCoverBudget]
    positivity
  have hloss := Z.seed.loss_pos
  have hcap := Z.seed.capFactor_pos
  have hnorm : 0<Z.seed.normalizationUpper U := by
    dsimp [ActualSynchronizedBufferedSeed.normalizationUpper]
    positivity
  rw [upperFactor,Real.log_mul (by positivity) (by positivity),Real.log_pow]
  rcases le_total (Z.seed.normalizationUpper U) ((2:ℝ)^(a+1)) with h | h
  · rw [max_eq_right h,Real.log_pow]
    push_cast
    nlinarith
  · rw [max_eq_left h]
    push_cast
    nlinarith

end ActualNormalizedBufferedStage
end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_actual_stage_retention
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.log_upperFactor_le_of_seed
