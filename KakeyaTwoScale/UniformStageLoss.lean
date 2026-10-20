module
public import KakeyaTwoScale.FullRunLossAbsorption

@[expose] public section

open Filter
open scoped BigOperators
namespace KakeyaTwoScale

/-- Uniform over every stopping prefix (indeed every subset of stages), once
ALL scale-independent constants and the genuine scale-error coefficients have
been established. This numerical adapter does not construct those estimates
for a geometric run. In particular its constants cannot depend on N. -/
theorem eventually_uniform_stage_loss {I : Type*} [DecidableEq I]
    (stages : Finset I) (loss : I → ℕ → ℝ) (alpha C J : I → ℝ)
    {epsilon : ℝ} (hbudget : ∑ i ∈ stages, alpha i < epsilon)
    (hnonneg : ∀ N i, i ∈ stages → 0 ≤ loss i N)
    (hbound : ∀ N i, i ∈ stages →
      loss i N ≤ alpha i * N + C i + J i * Real.log N) :
    ∀ᶠ N : ℕ in atTop, ∀ chosen : Finset I, chosen ⊆ stages →
      ∑ i ∈ chosen, loss i N ≤ epsilon * N := by
  have hg : 0 < epsilon - ∑ i ∈ stages, alpha i := sub_pos.mpr hbudget
  filter_upwards [eventually_log_loss_absorbed (∑ i ∈ stages, C i)
    (∑ i ∈ stages, J i) hg] with N hN
  intro chosen hchosen
  have hsub : ∑ i ∈ chosen, loss i N ≤ ∑ i ∈ stages, loss i N := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hchosen (fun i hi _ => hnonneg N i hi)
  have hsum := Finset.sum_le_sum (fun i hi => hbound N i hi)
  simp only [Finset.sum_add_distrib,← Finset.sum_mul] at hsum
  calc
    ∑ i ∈ chosen, loss i N ≤ ∑ i ∈ stages, loss i N := hsub
    _ ≤ epsilon * N := by nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_uniform_stage_loss
