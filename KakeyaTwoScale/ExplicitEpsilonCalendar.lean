module
public import KakeyaTwoScale.ActualSeedUpperLedger
public import KakeyaTwoScale.ActualNormalizationLossLedger

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- A shifted polylogarithm is absorbed only after its full fixed coefficient
has been specified. No uniformity in C or J is claimed or needed. -/
theorem eventually_log_succ_loss_absorbed (C J : ℝ) {epsilon : ℝ} (he : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, C+J*Real.log (q+1:ℕ) ≤ epsilon*q := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp (eventually_log_loss_absorbed C J (half_pos he))
  apply eventually_atTop.mpr
  refine ⟨max Q 1,?_⟩
  intro q hq
  have hq1 : 1 ≤ q := (le_max_right _ _).trans hq
  have h := hQ (q+1) (by omega)
  push_cast at h
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq1
  push_cast
  nlinarith

/-- The threshold is shared by every geometric object with the displayed
fixed ledger. This quantifier order prevents data-dependent absorption. -/
theorem eventually_uniform_log_envelope (rate C J epsilon : ℝ) (hrate : rate<epsilon) :
    ∀ᶠ q : ℕ in atTop, ∀ L : ℝ, 0<L →
      Real.log L ≤ rate*q+C+J*Real.log (q+1:ℕ) → L ≤ Real.exp (epsilon*q) := by
  filter_upwards [eventually_log_succ_loss_absorbed C J (sub_pos.mpr hrate)] with q hq
  intro L hL hbound
  apply (Real.log_le_iff_le_exp hL).mp
  nlinarith

/-- Explicitly separate macroscopic normalization progress from partition
accuracy. The two genuine scale slopes together use at most one quarter of
an assigned logarithmic budget across n dimension stages. -/
theorem exists_explicit_epsilon_calendar (n M m : ℕ) (hm : 1 ≤ m)
    {epsilon : ℝ} (he : 0<epsilon) :
    ∃ t : ℕ, 2 ≤ t ∧
      let tau := epsilon/(8*(n+1)*Real.log 2)
      0<tau ∧
      (n:ℝ)*((M:ℝ)*(Real.log (2*(n:ℝ)^2+1)+Real.log 2+Real.log (2*(m:ℝ)))/((t:ℝ)-1)+
        tau*Real.log 2) ≤ epsilon/4 := by
  let V := Real.log (2*(n:ℝ)^2+1)+Real.log 2+Real.log (2*(m:ℝ))
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hV : 0 ≤ V := by
    have h1 : 0 ≤ Real.log (2*(n:ℝ)^2+1) := Real.log_nonneg (by nlinarith [sq_nonneg (n:ℝ)])
    have h2 : 0 ≤ Real.log (2*(m:ℝ)) := Real.log_nonneg (by linarith)
    dsimp [V]
    linarith
  obtain ⟨t,ht⟩ := exists_nat_gt (2+8*(n+1)*(M:ℝ)*V/epsilon)
  have ht2 : 2 ≤ t := by
    have h0 : 0 ≤ 8*(n+1)*(M:ℝ)*V/epsilon := by positivity
    have : (2:ℝ)<t := by linarith
    exact_mod_cast this.le
  refine ⟨t,ht2,by positivity,?_⟩
  have htpos : (0:ℝ)<(t:ℝ)-1 := by
    have : (2:ℝ) ≤ t := by exact_mod_cast ht2
    linarith
  have hn : (0:ℝ)<n+1 := by positivity
  have hrate : (M:ℝ)*V/((t:ℝ)-1) ≤ epsilon/(8*(n+1)) := by
    apply (div_le_div_iff₀ htpos (by positivity)).mpr
    have hh := (div_lt_iff₀ he).mp (show 8*(n+1)*(M:ℝ)*V/epsilon<(t:ℝ)-1 by linarith)
    nlinarith
  have hreset : epsilon/(8*(n+1)*Real.log 2)*Real.log 2=epsilon/(8*(n+1)) := by
    field_simp
  rw [hreset]
  change (n:ℝ)*((M:ℝ)*V/((t:ℝ)-1)+epsilon/(8*(n+1))) ≤ epsilon/4
  have hmul := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg (α:=ℝ) n)
  have hsmall : (n:ℝ)*(epsilon/(8*(n+1))) ≤ epsilon/8 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<8)).mpr
    have hratio : (n:ℝ)/(n+1) ≤ 1 := (div_le_one hn).mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hratio he.le
    convert hh using 1 <;> field_simp
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_log_succ_loss_absorbed
#print axioms KakeyaTwoScale.eventually_uniform_log_envelope
#print axioms KakeyaTwoScale.exists_explicit_epsilon_calendar
