module
public import KakeyaTwoScale.ActualSeedUniformBound

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualNormalizedBufferedStage
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {I : BufferedStageInput b c k A B Lh J s depth T C O} {N : Fin k → ℝ} {P U : ℝ} {a : ℕ}

/-- This bound concerns the rounds actually executed by normalization. -/
theorem actual_rounds_bound (Z : ActualNormalizedBufferedStage I N P U a)
    {q : ℕ} {tau : ℝ} (htau : 0<tau) (hq : 0<q) (hLh : Lh ≤ q)
    (ha : 0<a) (hdrop : tau*(q:ℝ)/2 ≤ a) :
    (Z.rounds:ℝ) ≤ 2*k/tau+k := by
  have hh : ∀ j, Z.seed.state.height j ≤ q := fun j => (Z.seed.heights j).trans hLh
  have hbudget := Z.rounds_bound.trans (frozen_potential_bound _ hh)
  apply macroscopic_round_bound htau hq hdrop _ ha
  nlinarith [hbudget]

/-- Exact log retention for the actually constructed stage. -/
theorem log_retentionLoss (Z : ActualNormalizedBufferedStage I N P U a) :
    Real.log Z.retentionLoss = Real.log Z.seed.loss + (Z.rounds:ℝ)*
      ((k:ℝ)*Real.log 3+(b+c:ℝ)*Real.log (2*(A+(b+c)+5)+1:ℕ)+
        (k+1:ℝ)*Real.log (B+1:ℕ)) := by
  rw [retentionLoss,Real.log_mul Z.seed.loss_pos.ne' (by positivity),Real.log_pow]
  push_cast
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring

/-- Explicit uniform mass loss with a scale-independent bound on the actual
round count. The only genuine scale slope comes from orientation selection. -/
theorem log_retentionLoss_le (Z : ActualNormalizedBufferedStage I N P U a)
    (M q R : ℕ) (hs : 2 ≤ s) (hdepth : depth ≤ B/(s-1)+1)
    (hB : B ≤ M*q) (hLh : Lh ≤ q) (hR : Z.rounds ≤ R) :
    Real.log Z.retentionLoss ≤
      ((M:ℝ)*Real.log (2*(Z.seed.orientations.card:ℝ))/((s:ℝ)-1))*(q:ℝ) +
      (seedLogConstant Z.seed.orientations.card s (b+c) k A M +
        (R:ℝ)*(k*Real.log 3+(b+c)*Real.log (2*(A+(b+c)+5)+1:ℕ)+
          (k+1)*Real.log (M+1:ℕ))) +
      (4*k+4+R*(k+1):ℝ)*Real.log (q+1:ℕ) := by
  have hsLoss := Z.seed.log_loss_le M q hs hdepth hB hLh
  have hBlog : Real.log (B+1:ℕ) ≤ Real.log (M+1:ℕ)+Real.log (q+1:ℕ) := by
    have hn : B+1 ≤ (M+1)*(q+1) := by nlinarith
    have h := Real.log_le_log (by positivity : (0:ℝ)<(B+1:ℕ))
      (by exact_mod_cast hn : ((B+1:ℕ):ℝ) ≤ ((M+1:ℕ):ℝ)*(q+1:ℕ))
    rwa [Real.log_mul (by positivity) (by positivity)] at h
  have hbase : 0 ≤ (k:ℝ)*Real.log 3+(b+c:ℝ)*Real.log (2*(A+(b+c)+5)+1:ℕ)+
      (k+1:ℝ)*Real.log (B+1:ℕ) := by
    have h1 : 0 ≤ Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
    have h2 : 0 ≤ Real.log (2*(A+(b+c)+5)+1:ℕ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*(A+(b+c)+5)+1))
    have h3 : 0 ≤ Real.log (B+1:ℕ) := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 B)
    positivity
  have hRR : (Z.rounds:ℝ) ≤ R := by exact_mod_cast hR
  have hprod := mul_le_mul_of_nonneg_right hRR hbase
  rw [Z.log_retentionLoss]
  have hpoly := mul_le_mul_of_nonneg_left hBlog (show (0:ℝ) ≤ (R:ℝ)*(k+1) by positivity)
  push_cast at hsLoss hprod hpoly ⊢
  nlinarith

end ActualNormalizedBufferedStage
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.actual_rounds_bound
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.log_retentionLoss
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.log_retentionLoss_le
