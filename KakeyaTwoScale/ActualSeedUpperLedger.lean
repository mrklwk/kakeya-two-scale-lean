module
public import KakeyaTwoScale.ActualSeedUniformBound

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def calendarRemainder (b : ℕ) : ℝ := Real.log (2*(b:ℝ)^2+1)+Real.log 2/(b:ℝ)

namespace ActualSynchronizedBufferedSeed
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {I : BufferedStageInput b c k A B Lh J s depth T C O}

/-- Cancellation uses the same depth as the actual count and cap certificates.
The full polynomial complexity remains a displayed once-per-stage constant. -/
theorem log_normalizationUpper_le (S : ActualSynchronizedBufferedSeed I)
    (M q t : ℕ) (ht : 2 ≤ t) (hs : s=b*t)
    (hcalendar : ∀ j ∈ Finset.range s, I.D j=partitionBoxDegree b j)
    (hdepth : depth ≤ B/(s-1)+1) (hB : B ≤ M*q) (hLh : Lh ≤ q)
    {U : ℝ} (hU : 0<U) :
    Real.log (S.normalizationUpper U) ≤ Real.log U +
      ((M:ℝ)*(calendarRemainder b+Real.log (2*(S.orientations.card:ℝ))/(b:ℝ))/((s:ℝ)-1))*(q:ℝ) +
      (Real.log (2*algebraicAxisCoverBudget (b+c)
        (max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i))))) +
        calendarRemainder b+(Real.log 2+seedLogConstant S.orientations.card s (b+c) k A M)/(b:ℝ)) +
      ((4*k+4:ℝ)/(b:ℝ))*Real.log (q+1:ℕ) := by
  have hb := I.dimension_pos
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hs2 : 2 ≤ s := by rw [hs]; nlinarith
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs2
  have hden : (0:ℝ)<(s:ℝ)-1 := by linarith
  have hsum : (∑ i ∈ Finset.range s, I.D i)=∑ i ∈ Finset.range (b*t), partitionBoxDegree b i := by
    rw [←hs]
    exact Finset.sum_congr rfl hcalendar
  have hcancel := partition_calendar_log_cancellation b t hb
  rw [←hsum,←hs] at hcancel
  have hrem : 0 ≤ calendarRemainder b := by
    unfold calendarRemainder
    have h1 : 0 ≤ Real.log (2*(b:ℝ)^2+1) := Real.log_nonneg (by nlinarith [sq_nonneg (b:ℝ)])
    have h2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
    positivity
  have hd := sharp_depth_real_bound B s S.cellular_depth hs2 (S.cellular_depth_le.trans hdepth)
  have hBR : (B:ℝ) ≤ (M:ℝ)*q := by exact_mod_cast hB
  have hd' : (S.cellular_depth:ℝ) ≤ (M:ℝ)*q/((s:ℝ)-1)+1 := by
    have := div_le_div_of_nonneg_right hBR hden.le
    linarith
  have hterm := (mul_le_mul_of_nonneg_left hcancel (Nat.cast_nonneg S.cellular_depth)).trans
    (mul_le_mul_of_nonneg_right hd' hrem)
  have hmass := div_le_div_of_nonneg_right (S.log_loss_le M q hs2 hdepth hB hLh) hbR.le
  rw [S.log_normalizationUpper hU]
  change _ ≤ _ at hterm
  dsimp only [calendarRemainder] at hterm ⊢
  simp only [div_eq_mul_inv] at hterm hmass ⊢
  nlinarith

end ActualSynchronizedBufferedSeed
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualSynchronizedBufferedSeed.log_normalizationUpper_le
