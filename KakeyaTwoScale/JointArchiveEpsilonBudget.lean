module
public import KakeyaTwoScale.ActualArchiveUpperEpsilon

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- Universal dimension-only numerator used before choosing the partition
calendar. It dominates both mass and normalized upper-count scale rates. -/
def archiveRateNumerator (n : ℕ) : ℝ :=
  Real.log (2*(n:ℝ)^2+1)+Real.log 2+Real.log (2*(archiveOrientationCount n:ℝ))

theorem archive_local_rates_le (b c n : ℕ) (hb : 0<b) (hn : b+c=n) :
    Real.log (2*((bufferedStageOrientations b c).card:ℝ)) ≤ archiveRateNumerator n ∧
    calendarRemainder b+Real.log (2*((bufferedStageOrientations b c).card:ℝ))/(b:ℝ) ≤ archiveRateNumerator n := by
  let L := Real.log (2*(archiveOrientationCount n:ℝ))
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hbn : (b:ℝ) ≤ n := by exact_mod_cast (show b ≤ n by omega)
  have hb0 : (0:ℝ)<b := by linarith
  have hm : 1 ≤ archiveOrientationCount n := by unfold archiveOrientationCount; omega
  have hmR : (1:ℝ) ≤ archiveOrientationCount n := by exact_mod_cast hm
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hnlog : 0 ≤ Real.log (2*(n:ℝ)^2+1) := Real.log_nonneg (by nlinarith [sq_nonneg (n:ℝ)])
  have hlocal : Real.log (2*((bufferedStageOrientations b c).card:ℝ)) ≤ L := by
    by_cases hz : (bufferedStageOrientations b c).card=0
    · simpa only [hz,Nat.cast_zero,mul_zero,Real.log_zero] using hL
    · apply Real.log_le_log (by positivity)
      have hc : ((bufferedStageOrientations b c).card:ℝ) ≤ archiveOrientationCount n := by
        exact_mod_cast orientation_count_le b c n hn
      linarith
  have hdiv : Real.log (2*((bufferedStageOrientations b c).card:ℝ))/(b:ℝ) ≤ L := by
    apply (div_le_iff₀ hb0).mpr
    nlinarith
  have hdiv2 : Real.log 2/(b:ℝ) ≤ Real.log 2 := by
    apply (div_le_iff₀ hb0).mpr
    nlinarith
  have hblog : Real.log (2*(b:ℝ)^2+1) ≤ Real.log (2*(n:ℝ)^2+1) :=
    Real.log_le_log (by positivity) (by nlinarith)
  dsimp [archiveRateNumerator,calendarRemainder]
  dsimp [L] at hlocal hdiv hL
  constructor <;> linarith

 theorem uniform_depth_rate_le (M b t : ℕ) {X V : ℝ} (hb : 0<b) (ht : 2 ≤ t)
    (hX : X ≤ V) (hV : 0 ≤ V) :
    (M:ℝ)*X/((b*t:ℕ)-1:ℝ) ≤ (M:ℝ)*V/((t:ℝ)-1) := by
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have htR : (2:ℝ) ≤ t := by exact_mod_cast ht
  have hd : (0:ℝ)<(t:ℝ)-1 := by linarith
  have hdd : (t:ℝ)-1 ≤ (b*t:ℕ)-1 := by push_cast; nlinarith
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg M))
    (hd.le.trans hdd)).trans (div_le_div_of_nonneg_left (by positivity) hd hdd)

/-- A single explicit epsilon allocation simultaneously controls retained
mass and upper factors at every possible dimension stage. -/
theorem exists_joint_archive_precision (n M : ℕ) {e : ℝ} (he : 0<e) :
    ∃ tau : ℝ, 0<tau ∧ ∃ t : ℕ, 2 ≤ t ∧
      ∀ b c : ℕ, 0<b → b+c=n →
        (M:ℝ)*Real.log (2*((bufferedStageOrientations b c).card:ℝ))/((b*t:ℕ)-1:ℝ)<e ∧
        (M:ℝ)*(calendarRemainder b+Real.log (2*((bufferedStageOrientations b c).card:ℝ))/(b:ℝ))/
          ((b*t:ℕ)-1:ℝ)+tau*Real.log 2<e := by
  let V := archiveRateNumerator n
  have hV : 0 ≤ V := by
    unfold V archiveRateNumerator
    have hm : 1 ≤ archiveOrientationCount n := by unfold archiveOrientationCount; omega
    have hmR : (1:ℝ) ≤ archiveOrientationCount n := by exact_mod_cast hm
    have h1 : 0 ≤ Real.log (2*(n:ℝ)^2+1) := Real.log_nonneg (by nlinarith [sq_nonneg (n:ℝ)])
    have h2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ Real.log (2*(archiveOrientationCount n:ℝ)) := Real.log_nonneg (by linarith)
    positivity
  let tau := e/(4*Real.log 2)
  have htau : 0<tau := by dsimp [tau]; exact div_pos he (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  obtain ⟨t,ht⟩ := exists_nat_gt (2+4*(M:ℝ)*V/e)
  have ht2 : 2 ≤ t := by
    have h0 : 0 ≤ 4*(M:ℝ)*V/e := by positivity
    have : (2:ℝ)<t := by linarith
    exact_mod_cast this.le
  have hden : (0:ℝ)<(t:ℝ)-1 := by
    have hh : (2:ℝ) ≤ t := by exact_mod_cast ht2
    linarith
  have hsmall : (M:ℝ)*V/((t:ℝ)-1)<e/4 := by
    apply (div_lt_iff₀ hden).mpr
    have hh := (div_lt_iff₀ he).mp (show 4*(M:ℝ)*V/e<(t:ℝ)-1 by linarith)
    nlinarith
  have hreset : tau*Real.log 2=e/4 := by
    dsimp [tau]
    field_simp
  refine ⟨tau,htau,t,ht2,?_⟩
  intro b c hb hn
  have hl := archive_local_rates_le b c n hb hn
  have hmass := uniform_depth_rate_le M b t hb ht2 hl.1 hV
  have hupper := uniform_depth_rate_le M b t hb ht2 hl.2 hV
  rw [hreset]
  constructor <;> linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.archive_local_rates_le
#print axioms KakeyaTwoScale.uniform_depth_rate_le
#print axioms KakeyaTwoScale.exists_joint_archive_precision
