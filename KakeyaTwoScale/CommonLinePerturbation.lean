module
public import KakeyaTwoScale.PolynomialChartCounting
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- One common recentering changes the direction of a whole line while fixing
its point at reference time c. The same intercept serves all ancestor intervals. -/
def recenteredLineIntercept {m : ℕ} (b v : Fin m → ℝ) (c : ℝ) (w : Fin m → ℝ) :=
  b-c • (w-v)

theorem recenteredLine_dist {m : ℕ} (b v w : Fin m → ℝ) (c t : ℝ) :
    dist (recenteredLineIntercept b v c w+t • w) (b+t • v) =
      |t-c| * dist w v := by
  rw [dist_eq_norm,dist_eq_norm]
  have he : recenteredLineIntercept b v c w+t • w-(b+t • v)=(t-c) • (w-v) := by
    dsimp [recenteredLineIntercept]
    module
  rw [he,norm_smul,Real.norm_eq_abs]

/-- Whole balls of directions are eligible for ALL interval constraints
simultaneously. Each tolerance records its distance to ONE shared reference
time. No independent choice of intercept for each constraint is used. -/
theorem common_line_direction_ball {m : ℕ} {I : Type*}
    (b v : Fin m → ℝ) (c : ℝ) (J : I → Set ℝ)
    (A : I → Set ((Fin m → ℝ) × ℝ)) (M : I → ℝ)
    (hM : ∀ i, 0 < M i) {r : ℝ} (_hr : 0 < r)
    (htime : ∀ i, ∀ t ∈ J i, |t-c| ≤ M i)
    (hline : ∀ i, ∀ t ∈ J i, (b+t • v,t) ∈ A i) :
    ball v r ⊆ {w : Fin m → ℝ | ∃ b' : Fin m → ℝ,
      ∀ i, ∀ t ∈ J i, (b'+t • w,t) ∈ thickening (M i*r) (A i)} := by
  intro w hw
  refine ⟨recenteredLineIntercept b v c w,?_⟩
  intro i t ht
  apply mem_thickening_iff.mpr
  refine ⟨(b+t • v,t),hline i t ht,?_⟩
  have hd : dist w v < r := hw
  have hdist : dist (recenteredLineIntercept b v c w+t • w) (b+t • v) < M i*r := by
    rw [recenteredLine_dist]
    exact (mul_le_mul_of_nonneg_right (htime i t ht) dist_nonneg).trans_lt
      (mul_lt_mul_of_pos_left hd (hM i))
  simpa [Prod.dist_eq] using hdist

end KakeyaTwoScale
#print axioms KakeyaTwoScale.recenteredLine_dist
#print axioms KakeyaTwoScale.common_line_direction_ball
