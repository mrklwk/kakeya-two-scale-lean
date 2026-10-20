module
public import KakeyaTwoScale.MeasurablePathCounts

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- A coordinate cube has the exact dimensional squared-norm budget. -/
theorem cube_norm_sq_le {N : ℕ} (z : EuclideanSpace ℝ (Fin N)) (b : ℝ)
    (_hb : 0 ≤ b) (hz : ∀ i, |z i| ≤ b) : ‖z‖^2 ≤ N*b^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i : Fin N, (z i)^2 ≤ ∑ _i : Fin N, b^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := abs_le.mp (hz i)
      nlinarith
    _ = _ := by simp [nsmul_eq_mul]

/-- All points in the shrunken ball and hub cube share one strict norm budget. -/
theorem central_hub_budget {N : ℕ} (α b : ℝ) (hα : 0 ≤ α) (hb : 0 ≤ b)
    (hsmall : α^2+N*b^2 < 1) (x z : EuclideanSpace ℝ (Fin N))
    (hx : ‖x‖ ≤ α) (hz : ∀ i, |z i| ≤ b) : ‖x‖^2+‖z‖^2 < 1 := by
  have hh := cube_norm_sq_le z b hb hz
  nlinarith [norm_nonneg x]

/-- Actual crossing lower bound with constants fixed before endpoints and hub. -/
theorem central_hub_count_lower {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : Continuous f)
    (α b : ℝ) (hα : 0 ≤ α) (hb : 0 ≤ b) (hsmall : α^2+N*b^2 < 1)
    (x y z : EuclideanSpace ℝ (Fin N)) (hx : ‖x‖ ≤ α) (hy : ‖y‖ ≤ α)
    (hz : ∀ i, |z i| ≤ b) (hxsign : 0 < f x) (hysign : f y < 0) :
    1 ≤ (∑ j : Fin N, ballCoordinateCount f j (coordinateHybrid x z j.val)) +
      ∑ j : Fin N, ballCoordinateCount f j (coordinateHybrid y z j.val) :=
  two_paths_count_lower f hf x y z
    (central_hub_budget α b hα hb hsmall x z hx hz)
    (central_hub_budget α b hα hb hsmall y z hy hz) hxsign hysign

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cube_norm_sq_le
#print axioms KakeyaTwoScale.central_hub_budget
#print axioms KakeyaTwoScale.central_hub_count_lower
