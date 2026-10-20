module
public import KakeyaTwoScale.ActualNormalizedStageAccounting
public import KakeyaTwoScale.PartitionDegreeBudget
public import KakeyaTwoScale.FullRunLossAbsorption

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The polynomial degree calendar cancels the leading cellular contraction
in the normalized count. The remaining base is independent of t and scale. -/
theorem partition_calendar_crossing_bound (b t : ℕ) (hb : 0<b) :
    ((b*(∑ j ∈ Finset.range (b*t), partitionBoxDegree b j)+1:ℕ):ℝ)  ≤
      (2*(b:ℝ)^2+1)*2^t := by
  have hs := partitionBoxDegree_sum b hb t
  have hsR : ((∑ j ∈ Finset.range (b*t), partitionBoxDegree b j):ℝ)+2*b = 2*b*2^t := by
    exact_mod_cast hs
  push_cast
  have hp : (1:ℝ) ≤ 2^t := one_le_pow₀ (by norm_num)
  nlinarith [sq_nonneg (b:ℝ)]

/-- After cancellation, increasing the calendar t reduces the scale rate;
no t-dependent polynomial complexity occurs inside the cellular exponent. -/
theorem partition_calendar_log_cancellation (b t : ℕ) (hb : 0<b) :
    Real.log (b*(∑ j ∈ Finset.range (b*t), partitionBoxDegree b j)+1:ℕ) -
      ((b*t:ℕ)-1:ℝ)*Real.log 2/(b:ℝ)  ≤
      Real.log (2*(b:ℝ)^2+1)+Real.log 2/(b:ℝ) := by
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have h := Real.log_le_log (by positivity)
    (partition_calendar_crossing_bound b t hb)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at h
  push_cast at h ⊢
  have he : ((b:ℝ)*t-1)*Real.log 2/b = (t:ℝ)*Real.log 2-Real.log 2/b := by
    field_simp
  rw [he]
  linarith

/-- Real-valued depth bound, uniform in the actual selected depth. -/
theorem sharp_depth_real_bound (B s d : ℕ) (hs : 2  ≤  s)
    (hd : d  ≤  B/(s-1)+1) :
    (d:ℝ) ≤ (B:ℝ)/((s:ℝ)-1)+1 := by
  have hp : (0:ℝ)<(s:ℝ)-1 := by
    have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hdiv : ((B/(s-1):ℕ):ℝ)*((s:ℝ)-1) ≤ B := by
    have h := Nat.div_mul_le_self B (s-1)
    have h' : ((B/(s-1):ℕ):ℝ)*(s-1:ℕ) ≤ B := by exact_mod_cast h
    simpa only [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one] using h'
  have hq := (le_div_iff₀ hp).mpr hdiv
  have hdR : (d:ℝ) ≤ ((B/(s-1):ℕ):ℝ)+1 := by exact_mod_cast hd
  linarith

namespace ActualSynchronizedBufferedSeed
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {I : BufferedStageInput b c k A B Lh J s depth T C O}

/-- Exact retained-mass ledger: only the orientation term is exponential in
the cellular depth. All other scale-dependent terms are logarithmic. -/
theorem log_loss (S : ActualSynchronizedBufferedSeed I) :
    Real.log S.loss =
      (depth+1:ℝ)*Real.log (2*(S.orientations.card:ℝ)) + Real.log (s+1:ℕ) +
      2*Real.log (depth+1:ℕ) + 2*k*Real.log (Lh+1:ℕ) +
      k*Real.log 3 + (b+c)*Real.log (2*(A+(b+c)+5)+1:ℕ) +
      2*(k+1)*Real.log (B+1:ℕ) := by
  have hm : (0:ℝ)<S.orientations.card := by
    exact_mod_cast Finset.card_pos.mpr S.orientations_nonempty
  simp only [loss,bufferedForestLoss,bufferedSeedLoss,Nat.cast_mul,Nat.cast_pow]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

/-- The exact cap/count logarithm keeps the common actual cellular depth.
Its negative contraction must not be discarded before cancellation. -/
theorem log_normalizationUpper (S : ActualSynchronizedBufferedSeed I) {U : ℝ}
    (hU : 0<U) :
    Real.log (S.normalizationUpper U) = Real.log U +
      Real.log (2*algebraicAxisCoverBudget (b+c)
        (max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i))))) +
      (S.cellular_depth:ℝ)*(Real.log (b*(∑ i ∈ Finset.range s, I.D i)+1:ℕ) -
        ((s:ℝ)-1)*Real.log 2/(b:ℝ)) +
      (Real.log 2+Real.log S.loss)/(b:ℝ) := by
  have hc : 0<(2:ℝ)*algebraicAxisCoverBudget (b+c)
      (max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i)))) := by
    unfold algebraicAxisCoverBudget
    positivity
  have hx : 0<S.crossing := by
    dsimp [crossing]
    exact mul_pos hc (by positivity)
  have hcap := S.capFactor_pos
  have hloss := S.loss_pos
  rw [normalizationUpper,Real.log_mul (by positivity) (by positivity),
    Real.log_mul hx.ne' hU.ne',Real.log_rpow (div_pos S.capFactor_pos (div_pos zero_lt_one S.loss_pos)),
    Real.log_div S.capFactor_pos.ne' (by positivity),Real.log_div one_ne_zero S.loss_pos.ne',Real.log_one]
  have hcross : Real.log S.crossing =
      Real.log (2*algebraicAxisCoverBudget (b+c)
        (max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i))))) +
      (S.cellular_depth:ℝ)*Real.log (b*(∑ i ∈ Finset.range s, I.D i)+1:ℕ) := by
    rw [crossing,Real.log_mul hc.ne' (by positivity),Real.log_pow]
  have hcaplog : Real.log S.capFactor = Real.log 2 +
      (S.cellular_depth:ℝ)*(Real.log 2-(s:ℝ)*Real.log 2) := by
    rw [capFactor,Real.log_mul (by norm_num) (by positivity),Real.log_pow,
      Real.log_div (by norm_num) (by positivity),Real.log_pow]
  rw [hcross,hcaplog]
  ring

end ActualSynchronizedBufferedSeed
end KakeyaTwoScale
#print axioms KakeyaTwoScale.partition_calendar_crossing_bound
#print axioms KakeyaTwoScale.ActualSynchronizedBufferedSeed.log_loss
#print axioms KakeyaTwoScale.ActualSynchronizedBufferedSeed.log_normalizationUpper

#print axioms KakeyaTwoScale.partition_calendar_log_cancellation
#print axioms KakeyaTwoScale.sharp_depth_real_bound
