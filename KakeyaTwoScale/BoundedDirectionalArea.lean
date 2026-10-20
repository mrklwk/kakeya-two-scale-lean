module
public import KakeyaTwoScale.FramedPolynomialAreaBudget
public import KakeyaTwoScale.DirectionalAtlasIndependence

@[expose] public section

open MvPolynomial MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- One transverse coordinate cube contains every orthogonal projection of a
fixed Euclidean ball. The cube is selected before the direction/frame. -/
theorem bounded_orthogonal_projection {n : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x : Fin (n+1) → ℝ) (hx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r) :
    transverseProjection n ((orthogonalCoordinates R).symm x) ∈ closedBall 0 r := by
  rw [mem_closedBall_zero_iff]
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro j
  have hcoord := PiLp.norm_apply_le (R.symm (WithLp.toLp 2 x)) j.succ
  have hn : ‖R.symm (WithLp.toLp 2 x)‖ ≤ r := by simpa using hx
  exact hcoord.trans hn

/-- Uniform finite first-order bound on the SAME localized set, for every
Euclidean unit direction. Neither K nor the transverse cube depends on that direction. -/
theorem polynomial_bounded_unit_area {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ K, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖ = 1) :
    (A.restrict K hK).directionalArea (WithLp.ofLp u) ≤
      (P.totalDegree : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r) := by
  obtain ⟨R,hR⟩ := exists_axis_isometry (0 : Fin (n+1)) u hu
  have hh := polynomial_framed_region_budget P hP A R K hK
    (closedBall (0 : Fin n → ℝ) r) measurableSet_closedBall
    (fun x hx => bounded_orthogonal_projection r hr R x (hbound x hx.2))
  rwa [orthogonalCoordinates_first_axis,hR] at hh

/-- Linear Euclidean-norm control in all directions, including zero. -/
theorem polynomial_bounded_area_norm_le {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ K, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (v : Fin (n+1) → ℝ) :
    (A.restrict K hK).directionalArea v ≤
      ENNReal.ofReal ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (n+1)))‖ *
        ((P.totalDegree : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)) := by
  by_cases hv : v = 0
  · subst v
    rw [DisjointChartAtlas.directionalArea_zero]
    exact zero_le
  · obtain ⟨u,hunit,he⟩ := coordinate_euclidean_normalization v hv
    have hscale := (A.restrict K hK).directionalArea_smul
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (n+1)))‖ (WithLp.ofLp u)
    rw [he,abs_of_nonneg (norm_nonneg _)] at hscale
    rw [hscale]
    exact mul_le_mul le_rfl (polynomial_bounded_unit_area P hP A K hK r hr hbound u hunit) zero_le zero_le

/-- The whole localized directional functional is finite for every direction.
No finite-area hypothesis is supplied. -/
theorem polynomial_bounded_area_lt_top {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ K, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (v : Fin (n+1) → ℝ) : (A.restrict K hK).directionalArea v < ∞ := by
  apply lt_of_le_of_lt (polynomial_bounded_area_norm_le P hP A K hK r hr hbound v)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (by simp) measure_closedBall_lt_top)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.bounded_orthogonal_projection
#print axioms KakeyaTwoScale.polynomial_bounded_unit_area
#print axioms KakeyaTwoScale.polynomial_bounded_area_norm_le
#print axioms KakeyaTwoScale.polynomial_bounded_area_lt_top
