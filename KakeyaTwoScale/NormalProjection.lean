module
public import KakeyaTwoScale.TubeShortening
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

open Metric
noncomputable section
namespace KakeyaTwoScale
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Canonical ambient-valued projection normal to H. -/
def normalProjection (H : Submodule ℝ X) [H.HasOrthogonalProjection] : X →L[ℝ] X :=
  Hᗮ.starProjection

def affinePlane (H : Submodule ℝ X) (p : X) : Set X := {x | x-p ∈ H}

variable (H : Submodule ℝ X) [H.HasOrthogonalProjection]

theorem normalProjection_norm_le : ‖normalProjection H‖ ≤ 1 := Hᗮ.starProjection_norm_le

theorem normalProjection_zero {h : X} (hh : h ∈ H) : normalProjection H h = 0 := by
  rw [normalProjection, Submodule.starProjection_orthogonal_val,
    (Submodule.starProjection_eq_self_iff (K:=H)).mpr hh, sub_self]

theorem normalProjection_self {a : X} (ha : a ∈ Hᗮ) : normalProjection H a = a :=
  (Submodule.starProjection_eq_self_iff (K:=Hᗮ)).mpr ha

theorem normalProjection_mem (x : X) : normalProjection H x ∈ Hᗮ :=
  Hᗮ.starProjection_apply_mem x

theorem nearest_plane_point (p x : X) :
    p+H.starProjection (x-p) ∈ affinePlane H p ∧
      dist x (p+H.starProjection (x-p)) = ‖normalProjection H (x-p)‖ := by
  constructor
  · change p+H.starProjection (x-p)-p ∈ H
    simpa using H.starProjection_apply_mem (x-p)
  · rw [normalProjection, Submodule.starProjection_orthogonal_val, dist_eq_norm]
    congr 1
    abel

/-- Normal component is exactly distance to the affine subspace, expressed
without an unproved projection/distance interface. -/
theorem mem_plane_thickening_iff (p x : X) (r : ℝ) :
    x ∈ thickening r (affinePlane H p) ↔ ‖normalProjection H (x-p)‖ < r := by
  constructor
  · intro hx
    obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
    have hzero := normalProjection_zero H hy
    have he : normalProjection H (x-p) = normalProjection H (x-y) := by
      have hh : x-p = (x-y)+(y-p) := by abel
      rw [hh,map_add,hzero,add_zero]
    rw [he]
    have hn := Hᗮ.norm_starProjection_apply_le (x-y)
    exact hn.trans_lt (by simpa [dist_eq_norm] using hxy)
  · intro hx
    have hh := nearest_plane_point H p x
    exact mem_thickening_iff.mpr ⟨_,hh.1,by rwa [hh.2]⟩

def normalDirection (v : X) : X := ‖normalProjection H v‖⁻¹ • normalProjection H v

theorem normalDirection_unit {v : X} (hv : 0 < ‖normalProjection H v‖) :
    ‖normalDirection H v‖ = 1 := by
  rw [normalDirection, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hv,
    inv_mul_cancel₀ hv.ne']

theorem normalDirection_mem (v : X) : normalDirection H v ∈ Hᗮ :=
  Hᗮ.smul_mem _ (normalProjection_mem H v)

theorem normalDirection_projection (v : X) :
    normalProjection H (normalDirection H v) = normalDirection H v :=
  normalProjection_self H (normalDirection_mem H v)

theorem normalDirection_decomposition {v : X} (hv : 0 < ‖normalProjection H v‖) :
    normalProjection H v = ‖normalProjection H v‖ • normalDirection H v := by
  rw [normalDirection, smul_smul, mul_inv_cancel₀ hv.ne', one_smul]

/-- The preceding shortening theorem now uses the canonical projection and
produces an actual complement of an affine-plane neighborhood. -/
theorem shortened_tube_outside_plane (b v p : X) (s r : ℝ)
    (hs : 0 < s) (hv : s ≤ ‖normalProjection H v‖) (hr : r ≤ s/16) :
    ∃ I : Set ℝ, (I = Set.Icc (0:ℝ) (1/4) ∨ I = Set.Icc (3/4:ℝ) 1) ∧
      ∀ t ∈ I, ∀ x, dist x (segmentPoint b v t) ≤ r →
        x ∉ thickening (s/16) (affinePlane H p) := by
  obtain ⟨I,hI,hx⟩ := transverse_tube_shortening (normalProjection H) (normalProjection_norm_le H)
    b v p s r hs hv hr
  refine ⟨I,hI,?_⟩
  intro t ht x hxt
  rw [mem_plane_thickening_iff H]
  exact not_lt.mpr (hx t ht x hxt).le
/-- An affine extension of H by a normal direction, with explicit witnesses. -/
def extendedPlane (p a : X) : Set X :=
  {y | ∃ h ∈ H, ∃ t : ℝ, y = p + h + t • a}

/-- Distance to the extended plane is precisely approximation of the normal
component by its normal line. No angle or neighborhood certificate is assumed. -/
theorem mem_extendedPlane_thickening_iff (p a x : X) (r : ℝ)
    (ha : a ∈ Hᗮ) :
    x ∈ thickening r (extendedPlane H p a) ↔
      ∃ t : ℝ, dist (normalProjection H (x-p)) (t • a) < r := by
  constructor
  · intro hx
    obtain ⟨y, ⟨h, hh, t, rfl⟩, hxy⟩ := mem_thickening_iff.mp hx
    refine ⟨t, ?_⟩
    have he : normalProjection H (x-p) - t • a =
        normalProjection H (x-(p+h+t • a)) := by
      simp only [map_sub, map_add, map_smul, normalProjection_zero H hh,
        normalProjection_self H ha, add_zero]
      abel
    rw [dist_eq_norm, he]
    exact (Hᗮ.norm_starProjection_apply_le _).trans_lt
      (by simpa [dist_eq_norm] using hxy)
  · rintro ⟨t, ht⟩
    apply mem_thickening_iff.mpr
    refine ⟨p+H.starProjection (x-p)+t • a,
      ⟨H.starProjection (x-p), H.starProjection_apply_mem _, t, rfl⟩, ?_⟩
    have he : x-(p+H.starProjection (x-p)+t • a) =
        normalProjection H (x-p)-t • a := by
      rw [normalProjection, Submodule.starProjection_orthogonal_val]
      abel
    simpa only [dist_eq_norm, he] using ht

/-- A tube whose normal velocity approximates a normal line lies in the
corresponding enlarged-plane neighborhood. Constants are explicit and uniform. -/
theorem tube_near_extendedPlane (p a b v x : X) (t t₀ c r e R radius : ℝ)
    (ha : a ∈ Hᗮ) (ht : t ∈ Set.Icc (0:ℝ) 1) (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1)
    (hbase : ‖normalProjection H (segmentPoint b v t₀-p)‖ ≤ R)
    (hvelocity : ‖normalProjection H v-c • a‖ ≤ e)
    (hx : dist x (segmentPoint b v t) ≤ r) (hradius : r+R+e < radius) :
    x ∈ thickening radius (extendedPlane H p a) := by
  apply (mem_extendedPlane_thickening_iff H p a x _ ha).mpr
  refine ⟨(t-t₀)*c, ?_⟩
  have hdt : |t-t₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1,ht₀.2], by linarith [ht.2,ht₀.1]⟩
  have hepos : 0 ≤ e := (norm_nonneg _).trans hvelocity
  have hsmul : ‖(t-t₀) • (normalProjection H v-c • a)‖ ≤ e := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hdt hvelocity (norm_nonneg _) (by norm_num)).trans (by simp)
  have herror : ‖normalProjection H (x-segmentPoint b v t)‖ ≤ r :=
    (Hᗮ.norm_starProjection_apply_le _).trans (by simpa [dist_eq_norm] using hx)
  have hid : normalProjection H (x-p)-((t-t₀)*c) • a =
      normalProjection H (x-segmentPoint b v t) +
      normalProjection H (segmentPoint b v t₀-p) +
      (t-t₀) • (normalProjection H v-c • a) := by
    simp only [segmentPoint, map_sub, map_add, map_smul, smul_sub, sub_smul, mul_smul]
    module
  rw [dist_eq_norm, hid]
  have hn := norm_add_le (normalProjection H (x-segmentPoint b v t) +
    normalProjection H (segmentPoint b v t₀-p)) ((t-t₀) • (normalProjection H v-c • a))
  have hn' := norm_add_le (normalProjection H (x-segmentPoint b v t))
    (normalProjection H (segmentPoint b v t₀-p))
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mem_plane_thickening_iff
#print axioms KakeyaTwoScale.normalDirection_unit
#print axioms KakeyaTwoScale.normalDirection_projection
#print axioms KakeyaTwoScale.shortened_tube_outside_plane

#print axioms KakeyaTwoScale.mem_extendedPlane_thickening_iff

#print axioms KakeyaTwoScale.tube_near_extendedPlane
