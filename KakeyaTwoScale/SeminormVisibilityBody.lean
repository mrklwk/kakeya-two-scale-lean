module
public import KakeyaTwoScale.MollifiedAreaJointContinuity

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The norm cutoff keeps visibility bodies bounded even for degenerate seminorms. -/
def seminormVisibilityBody {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℝ E) : Set E := {v | ‖v‖ ≤ 1 ∧ p v ≤ 1}

theorem seminormVisibilityBody_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℝ E) : Convex ℝ (seminormVisibilityBody p) := by
  have he : seminormVisibilityBody p = closedBall 0 1 ∩ p.closedBall 0 1 := by
    ext v
    simp only [seminormVisibilityBody,mem_ofPred_eq,mem_inter_iff,mem_closedBall_zero_iff,Seminorm.mem_closedBall_zero]
  rw [he]
  exact (convex_closedBall (0 : E) 1).inter (p.convex_closedBall 0 1)

theorem seminormVisibilityBody_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℝ E) (v : E) : -v ∈ seminormVisibilityBody p ↔ v ∈ seminormVisibilityBody p := by
  simp only [seminormVisibilityBody,mem_ofPred_eq,norm_neg,map_neg_eq_map]

theorem seminormVisibilityBody_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (p : Seminorm ℝ E) (hp : Continuous p) : IsCompact (seminormVisibilityBody p) := by
  have he : seminormVisibilityBody p = closedBall 0 1 ∩ {v | p v ≤ 1} := by
    ext v
    simp only [seminormVisibilityBody,mem_ofPred_eq,mem_inter_iff,mem_closedBall_zero_iff]
  rw [he]
  exact (isCompact_closedBall (0 : E) 1).inter_right (isClosed_le hp continuous_const)

/-- A fixed positive inner ball survives zero and degenerate seminorms. -/
theorem closedBall_subset_seminormVisibilityBody {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Seminorm ℝ E) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ v, p v ≤ C * ‖v‖) :
    closedBall 0 (1/(1+C)) ⊆ seminormVisibilityBody p := by
  intro v hv
  rw [mem_closedBall_zero_iff] at hv
  have hpos : 0 < 1+C := by positivity
  have ht : ‖v‖ * (1+C) ≤ 1 := (le_div_iff₀ hpos).mp hv
  have hn := norm_nonneg v
  constructor
  · nlinarith
  · exact (hb v).trans (by nlinarith)

/-- Positive finite volume comes from explicit inner and outer Euclidean balls. -/
theorem seminormVisibilityBody_volume_bounds {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ v, p v ≤ C * ‖v‖) :
    volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1/(1+C))) ≤ volume (seminormVisibilityBody p) ∧
    0 < volume (seminormVisibilityBody p) ∧ volume (seminormVisibilityBody p) < ∞ := by
  have hinner := ball_subset_closedBall.trans (closedBall_subset_seminormVisibilityBody p C hC hb)
  have houter : seminormVisibilityBody p ⊆ closedBall 0 1 := fun v hv => mem_closedBall_zero_iff.mpr hv.1
  have hpos : 0 < 1/(1+C) := by positivity
  have hz : volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1/(1+C))) ≠ 0 :=
    isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr hpos)
  exact ⟨measure_mono hinner,(pos_iff_ne_zero.mpr hz).trans_le (measure_mono hinner),
    (measure_mono houter).trans_lt measure_closedBall_lt_top⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.seminormVisibilityBody_convex
#print axioms KakeyaTwoScale.seminormVisibilityBody_neg
#print axioms KakeyaTwoScale.seminormVisibilityBody_compact
#print axioms KakeyaTwoScale.closedBall_subset_seminormVisibilityBody
#print axioms KakeyaTwoScale.seminormVisibilityBody_volume_bounds
