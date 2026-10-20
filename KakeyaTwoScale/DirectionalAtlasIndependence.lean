module
public import KakeyaTwoScale.FramedHypersurfaceArea
public import Mathlib.Analysis.Normed.Module.RCLike.Basic

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Normalize using Euclidean length, not the coordinate Pi sup norm. -/
theorem coordinate_euclidean_normalization {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) :
    ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ • WithLp.ofLp u = v := by
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hw : w ≠ 0 := by
    intro hz
    exact hv (congrArg WithLp.ofLp hz)
  refine ⟨‖w‖⁻¹ • w,norm_smul_inv_norm hw,?_⟩
  change ‖w‖ • (‖w‖⁻¹ • v) = v
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw),one_smul]

/-- Every direction has the same area for any two atlases of the same set.
Infinite area is allowed; no cancellation by it occurs. -/
theorem DisjointChartAtlas.directionalArea_independent {n : ℕ}
    {Z : Set (Fin (n+1) → ℝ)} (A B : DisjointChartAtlas n Z) (v : Fin (n+1) → ℝ) :
    A.directionalArea v = B.directionalArea v := by
  have hu (u : EuclideanSpace ℝ (Fin (n+1))) (hunit : ‖u‖ = 1) :
      A.directionalArea (WithLp.ofLp u) = B.directionalArea (WithLp.ofLp u) := by
    obtain ⟨R,hR⟩ := exists_axis_isometry (0 : Fin (n+1)) u hunit
    have hA := A.frame_identity R
    have hB := B.frame_identity R
    rw [orthogonalCoordinates_first_axis,hR] at hA hB
    exact hA.trans hB.symm
  by_cases hv : v = 0
  · subst v
    rw [A.directionalArea_zero,B.directionalArea_zero]
  · obtain ⟨u,hunit,he⟩ := coordinate_euclidean_normalization v hv
    rw [← he,A.directionalArea_smul,B.directionalArea_smul,hu u hunit]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinate_euclidean_normalization
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_independent
