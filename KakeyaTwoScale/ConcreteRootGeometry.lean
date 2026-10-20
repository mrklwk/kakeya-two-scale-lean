module
public import KakeyaTwoScale.SpatialTupleLocalization
public import KakeyaTwoScale.ShortCylinderGridCount
public import KakeyaTwoScale.SharpBallPacking
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Actual half-open Euclidean grid cube. -/
def rootGridCube {n : ℕ} (δ : ℝ) (z : Fin n → ℤ) :
    Set (EuclideanSpace ℝ (Fin n)) := WithLp.ofLp ⁻¹' gridCell δ z

/-- Coarse owner of the lower corner; defined at every positive fine scale. -/
def rootCoarseOwner {n : ℕ} (δ : ℝ) (z : Fin n → ℤ) : Fin n → ℤ :=
  gridIndex 1 (latticePoint δ z)

theorem rootGridCube_radius {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ rootGridCube δ z) :
    dist x (latticeCenter δ z) ≤ (n+1:ℝ)*δ := by
  have hz := (mem_gridCell_iff hδ (WithLp.ofLp x) z).mp hx
  simpa only [hz] using rounded_center_dist hδ x

theorem rootGridCube_measurable {n : ℕ} (δ : ℝ) (z : Fin n → ℤ) :
    MeasurableSet (rootGridCube δ z) :=
  (measurableSet_gridCell δ z).preimage (PiLp.volume_preserving_ofLp (Fin n)).measurable

theorem rootGridCube_volume {n : ℕ} (δ : ℝ) (z : Fin n → ℤ) :
    volume (rootGridCube δ z) = ENNReal.ofReal δ ^ n := by
  rw [rootGridCube, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (measurableSet_gridCell δ z).nullMeasurableSet, volume_gridCell]

theorem rootGridCube_preconnected {n : ℕ} (δ : ℝ) (z : Fin n → ℤ) :
    IsPreconnected (rootGridCube δ z) := by
  have hc : Convex ℝ (gridCell δ z) := by
    have he : gridCell δ z = Set.univ.pi (fun i =>
        Set.Ico (δ*(z i:ℝ)) (δ*((z i:ℝ)+1))) := by
      ext x
      simp [gridCell, Set.mem_pi]
    rw [he]
    exact convex_pi (fun i _ => convex_Ico (𝕜 := ℝ) _ _)
  exact (hc.linear_preimage (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap).isPreconnected

/-- The entire incident unit cylinder fits in the same dimension-only ball
as its fine cube. No localization/capture certificate is supplied. -/
theorem rootGridCube_common_ball {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (z : Fin n → ℤ) :
    rootGridCube δ z ⊆ ball (latticeCenter 1 (rootCoarseOwner δ z)) (2*n+6:ℝ) ∧
    ∀ b u : EuclideanSpace ℝ (Fin n), ‖u‖=1 →
      (rootGridCube δ z ∩ flatCylinder b u 1 δ).Nonempty →
      flatCylinder b u 1 δ ⊆ ball (latticeCenter 1 (rootCoarseOwner δ z)) (2*n+6:ℝ) := by
  have hh := cube_and_cylinders_in_grid_ball (n := n) (A := n+1)
    (by norm_num : (0:ℝ)<1) hδ1 (rootGridCube δ z) (latticeCenter δ z)
    (fun x hx => (rootGridCube_radius hδ z x hx).trans
      (by simpa using mul_le_mul_of_nonneg_left hδ1 (show (0:ℝ) ≤ n+1 by positivity)))
  have he : ((n+1:ℕ)+n+5:ℝ)*1 = 2*n+6 := by push_cast; ring
  rw [he] at hh
  exact ⟨hh.1, fun b u hu hi => hh.2 b u 1 hu (by norm_num) hi⟩

/-- One original unit cylinder visits at most 13^n coarse owners, uniformly
in its translation and the fine scale. -/
theorem rootCoarseOwner_visit_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (b u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1)
    (cubes : Finset (Fin n → ℤ))
    (hmeet : ∀ z ∈ cubes, (rootGridCube δ z ∩ flatCylinder b u 1 δ).Nonempty) :
    (cubes.image (rootCoarseOwner δ)).card ≤ 13^n := by
  classical
  have hb : ∀ a ∈ cubes.image (rootCoarseOwner δ),
      dist (latticePoint 1 a) (WithLp.ofLp b) ≤ 4 := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    have hc := shortCylinder_grid_corner_bound (1/δ) hδ
      (by rw [div_mul_cancel₀ _ hδ.ne']) b u hu z (hmeet z hz)
    have hr := dist_gridRound_le (by norm_num : (0:ℝ)<1) (latticePoint δ z)
    have he : (1/δ+2)*δ = 1+2*δ := by field_simp
    rw [he] at hc
    have ht := dist_triangle (latticePoint 1 (rootCoarseOwner δ z))
      (latticePoint δ z) (WithLp.ofLp b)
    change dist (latticePoint δ z) (latticePoint 1 (rootCoarseOwner δ z)) ≤ 1 at hr
    rw [dist_comm] at hr
    linarith
  have hp := sharp_ball_packing (cubes.image (rootCoarseOwner δ)) (latticePoint 1)
    (WithLp.ofLp b) 1 4 (by norm_num) (by norm_num) hb
    (fun a _ a' _ hne => latticePoint_separated (by norm_num) hne)
  have hd : Module.finrank ℝ (Fin n → ℝ)=n := by simp
  rw [hd] at hp
  norm_num at hp
  exact_mod_cast hp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.rootGridCube_radius
#print axioms KakeyaTwoScale.rootGridCube_measurable
#print axioms KakeyaTwoScale.rootGridCube_volume
#print axioms KakeyaTwoScale.rootGridCube_preconnected
#print axioms KakeyaTwoScale.rootGridCube_common_ball
#print axioms KakeyaTwoScale.rootCoarseOwner_visit_bound
