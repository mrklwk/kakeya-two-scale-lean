module
public import KakeyaTwoScale.ActualNormalizedStageGeometry

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualNormalizedBufferedStage
attribute [local instance] Classical.propDecidable
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {I : BufferedStageInput b c k A B Lh J s depth T C O} {N : Fin k → ℝ} {P U : ℝ} {a : ℕ}

/-- Lower budgets are summed only for an actually active family. -/
theorem active_total_lower (Z : ActualNormalizedBufferedStage I N P U a)
    (j : Fin k) (hj : 0 < Z.state.height j) :
    N j*(P*Z.degree) ≤ (Z.state.count j:ℝ) := by
  classical
  have hh : (0:ℝ) < (Z.state.grains I.cube).card := by
    exact_mod_cast Finset.card_pos.mpr (Z.nonempty.image _)
  have hc := total_record_count_eq_grain_sum Z.state.tuples I.cube Z.state.grain
    (fun y => Z.state.parent y j) (Z.state.origin j) (fun y hy => Z.valid.2.2.2.1 y hy j)
  have hcR : (Z.state.count j:ℝ) = ∑ g ∈ Z.state.grains I.cube,
      (grainRecordCount Z.state.tuples I.cube Z.state.grain (fun y => Z.state.parent y j) g:ℝ) := by
    exact_mod_cast hc
  rw [hcR]
  have hs := Finset.sum_le_sum (fun g hg => Z.lower g hg j hj)
  apply le_trans _ hs
  simp only [Finset.sum_const,nsmul_eq_mul]
  change N j*(P*Z.degree) ≤ ((Z.state.grains I.cube).card:ℝ)*
    (N j*(P*Z.degree)/((Z.state.grains I.cube).card:ℝ))
  exact le_of_eq (by field_simp)

/-- The ancestor length comparison follows from actual conservation and full
archived counts, without lower-count survival in any selected marginal. -/
theorem active_length_step (Z : ActualNormalizedBufferedStage I N P U a)
    (j : Fin k) (hj : 0 < Z.state.height j) (hN : 0 < N j) (hP : 0 < P)
    (hupper : (I.W.count j:ℝ) ≤ U*(N j*P)) :
    Z.degree*Z.state.length I.δ j ≤ U*I.W.length I.δ j := by
  have hδ := I.width_pos
  have hnew : 0 ≤ Z.state.length I.δ j := by unfold FrozenGeometryState.length; positivity
  have hold : 0 ≤ I.W.length I.δ j := by unfold FrozenGeometryState.length; positivity
  have hh := (mul_le_mul_of_nonneg_left (Z.active_total_lower j hj) hnew).trans
    ((Z.axial j).trans (mul_le_mul_of_nonneg_left hupper hold))
  apply (mul_le_mul_iff_right₀ (mul_pos hN hP)).mp
  convert hh using 1 <;> ring

theorem permanently_frozen (Z : ActualNormalizedBufferedStage I N P U a)
    (j : Fin k) (hj : I.W.height j=0) : Z.state.height j=0 := by
  have h := Z.heights j
  omega

/-- Every actual parent record receives its own deduplicated axial budget. -/
theorem parent_budgets (Z : ActualNormalizedBufferedStage I N P U a) :
    ∃ parent : Fin k → Z.state.Piece → I.W.Piece,
      (∀ y ∈ Z.state.tuples, ∀ j, parent j (Z.state.parent y j)=I.W.parent y j) ∧
      (∀ j, ∀ t ∈ Z.state.records j, parent j t ∈ I.W.records j) ∧
      (∀ j, ∀ t ∈ I.W.records j,
        (∑ _u ∈ (Z.state.records j).filter (fun u => parent j u=t), Z.state.length I.δ j) ≤
          I.W.length I.δ j) :=
  FrozenGeometryState.physical_transition_parent_budgets I.W Z.state I.Y₀ I.cube I.tube
    (fun q => physicalCoordinateCube (I.Q q)) I.δ I.width_pos I.valid Z.valid Z.nonempty
    Z.tuples_subset (fun y hy j => (Z.geometry y hy j).trans Set.inter_subset_left) Z.axes

/-- A positive exact degree may be below one; its logarithmic floor comes
from retained mass and grain balance, not a family lower count. -/
theorem degree_log_floor (Z : ActualNormalizedBufferedStage I N P U a) :
    Real.log (1/Z.retentionLoss)-Real.log 2 ≤ (b:ℝ)*Real.log Z.degree := by
  have hh : (0:ℝ) < (I.W.grains I.cube).card := by
    exact_mod_cast Finset.card_pos.mpr (I.nonempty.image _)
  exact selected_degree_log_floor hh Z.degree_pos (by norm_num)
    (div_pos zero_lt_one Z.retentionLoss_pos) Z.degree_identity Z.grain_survival

end ActualNormalizedBufferedStage
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.active_total_lower
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.active_length_step
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.permanently_frozen
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.parent_budgets
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.degree_log_floor
