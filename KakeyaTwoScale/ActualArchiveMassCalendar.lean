module
public import KakeyaTwoScale.ActualArchiveMassEpsilon

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def archiveOrientationCount (n : ℕ) : ℕ :=
  1+∑ b ∈ Finset.range (n+1), (bufferedStageOrientations b (n-b)).card

theorem orientation_count_le (b c n : ℕ) (hn : b+c=n) :
    (bufferedStageOrientations b c).card ≤ archiveOrientationCount n := by
  have hc : c=n-b := by omega
  rw [hc]
  have hmem : b ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (n+1)) =>
    Nat.zero_le (bufferedStageOrientations i (n-i)).card) hmem
  unfold archiveOrientationCount
  omega

/-- One calendar works for every possible dimension drop. Canonical
orientation counts are bounded before scale or polynomial data are chosen. -/
theorem exists_archive_mass_precision (n M : ℕ) {epsilon : ℝ} (he : 0<epsilon) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ b c : ℕ, 0<b → b+c=n →
      (M:ℝ)*Real.log (2*((bufferedStageOrientations b c).card:ℝ))/((b*t:ℕ)-1:ℝ)<epsilon := by
  let m := archiveOrientationCount n
  have hm : 1 ≤ m := by dsimp [m,archiveOrientationCount]; omega
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (2*(m:ℝ)) := Real.log_nonneg (by linarith)
  obtain ⟨t,ht⟩ := exists_nat_gt (2+(M:ℝ)*Real.log (2*(m:ℝ))/epsilon)
  have ht2 : 2 ≤ t := by
    have h0 : 0 ≤ (M:ℝ)*Real.log (2*(m:ℝ))/epsilon := by positivity
    have : (2:ℝ)<t := by linarith
    exact_mod_cast this.le
  refine ⟨t,ht2,?_⟩
  intro b c hb hn
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have htR : (2:ℝ) ≤ t := by exact_mod_cast ht2
  have hden : (0:ℝ)<(b*t:ℕ)-1 := by push_cast; nlinarith
  have hcard := orientation_count_le b c n hn
  have hlogcard : Real.log (2*((bufferedStageOrientations b c).card:ℝ)) ≤ Real.log (2*(m:ℝ)) := by
    by_cases hzero : (bufferedStageOrientations b c).card=0
    · simp only [hzero,Nat.cast_zero,mul_zero,Real.log_zero]
      exact hlog
    · apply Real.log_le_log (by positivity)
      have hh : ((bufferedStageOrientations b c).card:ℝ) ≤ m := by exact_mod_cast hcard
      linarith
  apply (div_lt_iff₀ hden).mpr
  have hmterm := mul_le_mul_of_nonneg_left hlogcard (Nat.cast_nonneg (α:=ℝ) M)
  have hsmall := (div_lt_iff₀ he).mp (show (M:ℝ)*Real.log (2*(m:ℝ))/epsilon<(t:ℝ)-1 by linarith)
  have hbt : (t:ℝ) ≤ (b:ℝ)*t := by nlinarith
  have heprod := mul_le_mul_of_nonneg_left (sub_le_sub_right hbt 1) he.le
  push_cast
  nlinarith

/-- The retained-mass portion of the full archive envelope is now proved
with an arbitrarily small dyadic epsilon loss. Original cardinality and height
calendars remain explicit and must be instantiated by the Kakeya root. -/
theorem exists_uniform_archive_mass_calendar (n k A M : ℕ) {epsilon tau : ℝ}
    (he : 0<epsilon) (htau : 0<tau) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (B Lh b c J s fuel : ℕ) (T C O : Type) [DecidableEq T] [DecidableEq C]
        (N : Fin k → ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O) (P U : ℝ)
        (H : ActualBufferedArchive k A B Lh ⌊tau*(q:ℝ)⌋₊ t T C O N I P U fuel),
        b+c=n → s=b*t → B ≤ M*q → Lh ≤ q → fuel ≤ n →
        H.loss ≤ (2:ℝ)^(epsilon*(q:ℝ)) := by
  let e := epsilon*Real.log 2/(n+1)
  have he' : 0<e := by dsimp [e]; exact div_pos (mul_pos he (Real.log_pos (by norm_num))) (by positivity)
  obtain ⟨t,ht,hprecision⟩ := exists_archive_mass_precision n M he'
  obtain ⟨R,hR⟩ := exists_nat_gt (2*(k:ℝ)/tau+k)
  refine ⟨t,ht,?_⟩
  filter_upwards [eventually_actual_archive_mass_loss n k A M t R ht htau hR.le hprecision] with q hq
  intro B Lh b c J s fuel T C O _ _ N I P U H hn hs hB hLh hfuel
  have h := hq B Lh b c J s fuel T C O N I P U H hn hs hB hLh
  apply h.trans
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  apply Real.exp_le_exp.mpr
  have hd : (H.drops:ℝ) ≤ n := by exact_mod_cast H.drops_le.trans hfuel
  have hratio : (H.drops:ℝ)/(n+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ epsilon*Real.log 2*(q:ℝ) by positivity)
  dsimp [e]
  convert hh using 1 <;> ring

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {N : Fin k → ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Apply the uniform archive loss directly to the original nonlinear mass. -/
theorem terminal_mass_of_dyadic_loss (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (epsilon : ℝ) (q : ℕ) (h : H.loss ≤ (2:ℝ)^(epsilon*(q:ℝ))) :
    tupleCubeMass I.W.tuples I.cube I.cubes I.alpha / (2:ℝ)^(epsilon*(q:ℝ)) ≤
      tupleCubeMass H.terminal.state.tuples I.cube I.cubes I.alpha := by
  have hm : 0 ≤ tupleCubeMass I.W.tuples I.cube I.cubes I.alpha := by
    unfold tupleCubeMass
    positivity
  exact (div_le_div_of_nonneg_left hm H.loss_pos h).trans H.terminal_mass

end ActualBufferedArchive

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orientation_count_le
#print axioms KakeyaTwoScale.exists_archive_mass_precision
#print axioms KakeyaTwoScale.exists_uniform_archive_mass_calendar

#print axioms KakeyaTwoScale.ActualBufferedArchive.terminal_mass_of_dyadic_loss
