module
public import KakeyaTwoScale.ActualIndexedDegreeObjective

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualNormalizedBufferedStage
variable {b c k A B Lh J s depth : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {I : BufferedStageInput b c k A B Lh J s depth T Q O} {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}

/-- Retention loss is at least one by actual positive mass and subset
monotonicity, independently of its implementation formula. -/
theorem retentionLoss_one_le (Z : ActualNormalizedBufferedStage I N P U a) :
    1≤Z.retentionLoss := by
  obtain ⟨y,hy⟩ := I.nonempty
  have hpos : 0<tupleCubeMass I.W.tuples I.cube I.cubes I.alpha :=
    lt_of_lt_of_le (by norm_num) (tuple_mass_one_le _ _ _ I.exponent_pos.le hy (I.support y (I.valid.1 hy)))
  have hm : tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/Z.retentionLoss ≤
      tupleCubeMass Z.state.tuples I.cube I.cubes I.alpha := Z.mass
  have hh := hm.trans (tuple_mass_mono _ _ I.cube I.cubes Z.tuples_subset I.exponent_pos.le)
  have hh' := (div_le_iff₀ Z.retentionLoss_pos).mp hh
  nlinarith

/-- A stage has an unweighted log-degree floor. Its positive dimension is
used, but no degree-at-least-one claim is made. -/
theorem log_degree_floor (Z : ActualNormalizedBufferedStage I N P U a) :
    -Real.log (2*Z.retentionLoss)≤Real.log Z.degree := by
  have hb : (1:ℝ)≤b := by exact_mod_cast I.dimension_pos
  have hl : 0≤Real.log (2*Z.retentionLoss) := Real.log_nonneg (by linarith [Z.retentionLoss_one_le])
  have hh := Z.degree_log_floor
  rw [Real.log_div (by norm_num) Z.retentionLoss_pos.ne',Real.log_one,zero_sub] at hh
  rw [Real.log_mul (by norm_num) Z.retentionLoss_pos.ne'] at hl ⊢
  by_cases hd : 0≤Real.log Z.degree
  · linarith
  · have hx := mul_le_mul_of_nonpos_right hb (le_of_not_ge hd)
    simp only [one_mul] at hx
    linarith

end ActualNormalizedBufferedStage
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

theorem loss_one_le (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) : 1≤H.loss := by
  induction H with
  | zero => exact le_rfl
  | short => exact le_rfl
  | last _ _ _ Z => exact Z.retentionLoss_one_le
  | next _ _ _ Z _ _ tail ih =>
    change 1≤Z.retentionLoss*tail.loss
    nlinarith [Z.retentionLoss_one_le]

/-- One actual archive loss controls every executed last-degree floor. -/
theorem stageDegrees_log_floor (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    ∀D∈H.stageDegrees, -Real.log (2*H.loss)≤Real.log D := by
  induction H with
  | zero => simp [stageDegrees]
  | short => simp [stageDegrees]
  | last I P U Z =>
    intro D hD
    rcases List.mem_singleton.mp hD with rfl
    exact Z.log_degree_floor
  | next I P U Z hb ht tail ih =>
    intro D hD
    have hs : Z.retentionLoss≤Z.retentionLoss*tail.loss := le_mul_of_one_le_right Z.retentionLoss_pos.le tail.loss_one_le
    have ht : tail.loss≤Z.retentionLoss*tail.loss := le_mul_of_one_le_left tail.loss_pos.le Z.retentionLoss_one_le
    change -Real.log (2*(Z.retentionLoss*tail.loss))≤Real.log D
    rcases List.mem_cons.mp hD with rfl | hD
    · exact (neg_le_neg (Real.log_le_log (mul_pos (by norm_num) Z.retentionLoss_pos) (mul_le_mul_of_nonneg_left hs (by norm_num)))).trans Z.log_degree_floor
    · exact (neg_le_neg (Real.log_le_log (mul_pos (by norm_num) tail.loss_pos) (mul_le_mul_of_nonneg_left ht (by norm_num)))).trans (ih D hD)

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.retentionLoss_one_le
#print axioms KakeyaTwoScale.ActualBufferedArchive.stageDegrees_log_floor
