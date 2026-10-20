module
public import KakeyaTwoScale.NormalPlaneNet
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open InnerProductGeometry
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Angle to the canonical tangential projection. Mathlib assigns pi/2 when
that projection is zero, exactly the normal-direction boundary case. -/
def planeAngle (H : Submodule ℝ X) [H.HasOrthogonalProjection] (v : X) : ℝ :=
  angle v (H.starProjection v)

variable (H : Submodule ℝ X) [H.HasOrthogonalProjection]

theorem inner_tangent (v : X) : inner ℝ v (H.starProjection v) = ‖H.starProjection v‖^2 := by
  have hh := H.starProjection_inner_eq_zero v _ (H.starProjection_apply_mem v)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hh
  linarith

theorem planeAngle_range (v : X) : 0 ≤ planeAngle H v ∧ planeAngle H v ≤ Real.pi/2 := by
  refine ⟨angle_nonneg _ _, ?_⟩
  unfold planeAngle angle
  apply Real.arccos_le_pi_div_two.mpr
  rw [inner_tangent H]
  positivity

theorem sin_planeAngle_unit (v : X) (hv : ‖v‖ = 1) :
    Real.sin (planeAngle H v) = ‖normalProjection H v‖ := by
  by_cases ht : H.starProjection v = 0
  · simp [planeAngle, ht, angle, normalProjection, Submodule.starProjection_orthogonal_val, hv]
  have htp : 0 < ‖H.starProjection v‖ := norm_pos_iff.mpr ht
  have hc := cos_angle_mul_norm_mul_norm v (H.starProjection v)
  rw [hv, one_mul, inner_tangent H] at hc
  have hcos : Real.cos (planeAngle H v) = ‖H.starProjection v‖ := by
    unfold planeAngle
    nlinarith
  have hn := H.norm_sq_eq_add_norm_sq_starProjection v
  change ‖v‖^2 = ‖H.starProjection v‖^2 + ‖normalProjection H v‖^2 at hn
  rw [hv] at hn
  have htrig := Real.sin_sq_add_cos_sq (planeAngle H v)
  rw [hcos] at htrig
  have hs := sin_angle_nonneg v (H.starProjection v)
  change 0 ≤ Real.sin (planeAngle H v) at hs
  nlinarith [norm_nonneg (normalProjection H v)]

/-- Uniform angle-speed comparison, including purely normal unit directions. -/
theorem planeAngle_speed_bounds (v : X) (hv : ‖v‖ = 1) :
    (2/Real.pi)*planeAngle H v ≤ ‖normalProjection H v‖ ∧
      ‖normalProjection H v‖ ≤ planeAngle H v := by
  obtain ⟨h0, hpi⟩ := planeAngle_range H v
  rw [← sin_planeAngle_unit H v hv]
  exact ⟨Real.mul_le_sin h0 hpi, Real.sin_le h0⟩
/-- The projection angle is no larger than the angle with any nonzero
vector of H; hence it is the usual least angle when H is nontrivial. -/
theorem planeAngle_le_angle (v u : X) (hv : ‖v‖ = 1)
    (hu : u ∈ H) (hu0 : u ≠ 0) : planeAngle H v ≤ angle v u := by
  have hinner : inner ℝ v u = inner ℝ (H.starProjection v) u := by
    have hh := H.starProjection_inner_eq_zero v u hu
    rw [inner_sub_left] at hh
    linarith
  have hbound := real_inner_le_norm (H.starProjection v) u
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  by_cases ht : H.starProjection v = 0
  · have hi : inner ℝ v u = 0 := by simpa [ht] using hinner
    simp [planeAngle, ht, angle, hi]
  have htp : 0 < ‖H.starProjection v‖ := norm_pos_iff.mpr ht
  unfold planeAngle angle
  apply Real.arccos_le_arccos
  rw [hv, one_mul, one_mul, inner_tangent H, hinner]
  rw [sq, mul_div_cancel_right₀ _ htp.ne']
  exact (div_le_iff₀ hup).mpr hbound

/-- A genuine tube/plane-neighborhood encounter supplies the axis encounter
used by the brush construction, with the explicit one-radius loss. -/
theorem tube_plane_encounter (p b v : X) (r R : ℝ)
    (hmeet : (Metric.thickening r (segmentPoint b v '' Set.Icc (0:ℝ) 1) ∩
      Metric.thickening R (affinePlane H p)).Nonempty) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, ‖normalProjection H (segmentPoint b v t-p)‖ < R+r := by
  obtain ⟨x, hx, hp⟩ := hmeet
  obtain ⟨y, ⟨t, ht, rfl⟩, hxt⟩ := Metric.mem_thickening_iff.mp hx
  refine ⟨t, ht, ?_⟩
  have hn := (mem_plane_thickening_iff H p x R).mp hp
  have hd : ‖normalProjection H (segmentPoint b v t-x)‖ < r :=
    (Hᗮ.norm_starProjection_apply_le _).trans_lt
      (by simpa [dist_eq_norm, norm_sub_rev] using hxt)
  have he : segmentPoint b v t-p = (segmentPoint b v t-x)+(x-p) := by abel
  rw [he, map_add]
  have htri := norm_add_le (normalProjection H (segmentPoint b v t-x)) (normalProjection H (x-p))
  linarith

/-- Low-angle tubes stay near the base plane itself; no normal-direction
net or shortening is needed. The constant is explicit and scale uniform. -/
theorem low_angle_tube_near_plane (p b v x : X) (t t₀ C r R radius : ℝ)
    (hv : ‖v‖ = 1) (hangle : planeAngle H v ≤ C*r)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1)
    (hbase : ‖normalProjection H (segmentPoint b v t₀-p)‖ ≤ R)
    (hx : dist x (segmentPoint b v t) ≤ r) (hrad : R+(C+1)*r < radius) :
    x ∈ Metric.thickening radius (affinePlane H p) := by
  have hspeed := (planeAngle_speed_bounds H v hv).2.trans hangle
  have hnear := tube_near_extendedPlane H p 0 b v x t t₀ 0 r (C*r) R radius
    Hᗮ.zero_mem ht ht₀ hbase (by simpa using hspeed) hx (by nlinarith)
  obtain ⟨u, hu⟩ := (mem_extendedPlane_thickening_iff H p 0 x radius Hᗮ.zero_mem).mp hnear
  apply (mem_plane_thickening_iff H p x radius).mpr
  simpa using hu

end KakeyaTwoScale
#print axioms KakeyaTwoScale.planeAngle_range
#print axioms KakeyaTwoScale.sin_planeAngle_unit
#print axioms KakeyaTwoScale.planeAngle_speed_bounds

#print axioms KakeyaTwoScale.planeAngle_le_angle

#print axioms KakeyaTwoScale.tube_plane_encounter

#print axioms KakeyaTwoScale.low_angle_tube_near_plane
