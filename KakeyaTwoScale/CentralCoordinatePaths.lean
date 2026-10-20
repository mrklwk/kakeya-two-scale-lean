module
public import KakeyaTwoScale.AveragedVisibilityCheckpoint
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Coordinate path vertex: the first k coordinates come from the hub. -/
def coordinateHybrid {N : ℕ} (x z : EuclideanSpace ℝ (Fin N)) (k : ℕ) :
    EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => if i.val < k then z i else x i)

@[simp] theorem coordinateHybrid_zero {N : ℕ} (x z : EuclideanSpace ℝ (Fin N)) :
    coordinateHybrid x z 0 = x := by ext i; simp [coordinateHybrid]

@[simp] theorem coordinateHybrid_end {N : ℕ} (x z : EuclideanSpace ℝ (Fin N)) :
    coordinateHybrid x z N = z := by ext i; simp [coordinateHybrid]

/-- The norm budget is uniform over all path vertices, including repeated ones. -/
theorem coordinateHybrid_norm_sq_le {N : ℕ} (x z : EuclideanSpace ℝ (Fin N)) (k : ℕ) :
    ‖coordinateHybrid x z k‖^2 ≤ ‖x‖^2 + ‖z‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change (if i.val < k then z i else x i)^2 ≤ (x i)^2+(z i)^2
  split_ifs <;> nlinarith [sq_nonneg (x i),sq_nonneg (z i)]

/-- A strict shared squared-norm budget keeps every vertex in the open ball. -/
theorem coordinateHybrid_mem_ball {N : ℕ} (x z : EuclideanSpace ℝ (Fin N))
    (h : ‖x‖^2+‖z‖^2 < 1) (k : ℕ) : coordinateHybrid x z k ∈ ball 0 1 := by
  rw [mem_ball_zero_iff]
  have hh := coordinateHybrid_norm_sq_le x z k
  nlinarith [norm_nonneg (coordinateHybrid x z k)]

/-- At step j only coordinate j changes. -/
theorem coordinateHybrid_succ_apply {N : ℕ} (x z : EuclideanSpace ℝ (Fin N))
    (j i : Fin N) (hij : i ≠ j) : coordinateHybrid x z (j.val+1) i = coordinateHybrid x z j.val i := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  change (if i.val < j.val+1 then z i else x i) = (if i.val < j.val then z i else x i)
  have he : i.val < j.val+1 ↔ i.val < j.val := by omega
  simp only [he]

/-- Every straight axis segment remains in the same open ball. -/
theorem coordinateHybrid_segment_mem_ball {N : ℕ} (x z : EuclideanSpace ℝ (Fin N))
    (h : ‖x‖^2+‖z‖^2 < 1) (j : Fin N) (t : ℝ) (ht : t ∈ Icc 0 1) :
    (1-t) • coordinateHybrid x z j.val + t • coordinateHybrid x z (j.val+1) ∈ ball 0 1 := by
  exact (convex_ball (0 : EuclideanSpace ℝ (Fin N)) 1)
    (coordinateHybrid_mem_ball x z h _) (coordinateHybrid_mem_ball x z h _)
    (by linarith [ht.2]) ht.1 (by ring)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateHybrid_norm_sq_le
#print axioms KakeyaTwoScale.coordinateHybrid_mem_ball
#print axioms KakeyaTwoScale.coordinateHybrid_succ_apply
#print axioms KakeyaTwoScale.coordinateHybrid_segment_mem_ball
