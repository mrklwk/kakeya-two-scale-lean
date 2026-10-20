module
public import KakeyaTwoScale.ProjectiveNet
public import KakeyaTwoScale.NormalProjection

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
variable {X J : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Construct the projective net from actual tube velocities. Every selected
normal is unit and fixed by the canonical projection, and every original
index is assigned to a selected index. Epsilon may be r/s at any scale. -/
theorem normal_plane_net (H : Submodule ℝ X) [H.HasOrthogonalProjection]
    (family : Finset J) (hne : family.Nonempty) (v : J → X)
    (hv : ∀ j ∈ family, 0 < ‖normalProjection H (v j)‖)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ (net : Finset J) (assign : J → J), net ⊆ family ∧
      (∀ j ∈ net, ‖normalDirection H (v j)‖ = 1 ∧
        normalDirection H (v j) ∈ Hᗮ) ∧
      (∀ j ∈ net, ∀ k ∈ net, j ≠ k →
        epsilon ≤ dist (normalDirection H (v j)) (normalDirection H (v k)) ∧
        epsilon ≤ dist (normalDirection H (v j)) (-normalDirection H (v k))) ∧
      (∀ j ∈ family, assign j ∈ net ∧
        (dist (normalDirection H (v j)) (normalDirection H (v (assign j))) < epsilon ∨
        dist (normalDirection H (v j)) (-normalDirection H (v (assign j))) < epsilon)) := by
  obtain ⟨net, assign, hsub, hsep, hcover⟩ :=
    finite_projective_net_assignment family hne (fun j => normalDirection H (v j)) epsilon he
  refine ⟨net, assign, hsub, ?_, hsep, hcover⟩
  intro j hj
  exact ⟨normalDirection_unit H (hv j (hsub hj)), normalDirection_mem H (v j)⟩

/-- Projective proximity gives a signed velocity approximation, with the
normal speed as the exact factor. Both antipodal cases are included. -/
theorem normal_velocity_approximation (H : Submodule ℝ X) [H.HasOrthogonalProjection]
    (v a : X) (epsilon : ℝ) (hv : 0 < ‖normalProjection H v‖)
    (hclose : dist (normalDirection H v) a ≤ epsilon ∨
      dist (normalDirection H v) (-a) ≤ epsilon) :
    ∃ c : ℝ, |c| = ‖normalProjection H v‖ ∧
      ‖normalProjection H v-c • a‖ ≤ ‖normalProjection H v‖*epsilon := by
  have step (u : X) (hu : dist (normalDirection H v) u ≤ epsilon) :
      ‖normalProjection H v-‖normalProjection H v‖ • u‖ ≤
        ‖normalProjection H v‖*epsilon := by
    calc
      _ = ‖‖normalProjection H v‖ • (normalDirection H v-u)‖ := by
        congr 1
        rw [smul_sub, ← normalDirection_decomposition H hv]
      _ = ‖normalProjection H v‖*dist (normalDirection H v) u := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hv, dist_eq_norm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hu hv.le
  rcases hclose with h | h
  · exact ⟨_, abs_of_pos hv, step a h⟩
  · refine ⟨-‖normalProjection H v‖, by simp [abs_of_pos hv], ?_⟩
    simpa using step (-a) h

/-- The source high-band r/s net costs at most 2r in normal velocity. -/
theorem normal_velocity_band_approximation (H : Submodule ℝ X) [H.HasOrthogonalProjection]
    (v a : X) (r s : ℝ) (hs : 0 < s) (hr : 0 ≤ r)
    (hv : 0 < ‖normalProjection H v‖) (hupper : ‖normalProjection H v‖ ≤ 2*s)
    (hclose : dist (normalDirection H v) a ≤ r/s ∨
      dist (normalDirection H v) (-a) ≤ r/s) :
    ∃ c : ℝ, ‖normalProjection H v-c • a‖ ≤ 2*r := by
  obtain ⟨c, _, hc⟩ := normal_velocity_approximation H v a (r/s) hv hclose
  refine ⟨c, hc.trans ?_⟩
  calc
    _ ≤ (2*s)*(r/s) := mul_le_mul_of_nonneg_right hupper (div_nonneg hr hs.le)
    _ = 2*r := by field_simp

/-- Concrete high-band containment: an axis meeting the R-neighborhood of H
and assigned by the r/s projective net has its r-tube in the radius enlarged
plane whenever R+3r<radius. This is uniform in H, the family and the scale. -/
theorem high_band_tube_containment (H : Submodule ℝ X) [H.HasOrthogonalProjection]
    (p a b v x : X) (t t₀ r s R radius : ℝ)
    (ha : a ∈ Hᗮ) (ht : t ∈ Set.Icc (0:ℝ) 1) (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1)
    (hs : 0 < s) (hr : 0 ≤ r) (hv : 0 < ‖normalProjection H v‖)
    (hupper : ‖normalProjection H v‖ ≤ 2*s)
    (hbase : ‖normalProjection H (segmentPoint b v t₀-p)‖ ≤ R)
    (hclose : dist (normalDirection H v) a ≤ r/s ∨
      dist (normalDirection H v) (-a) ≤ r/s)
    (hx : dist x (segmentPoint b v t) ≤ r) (hradius : R+3*r < radius) :
    x ∈ Metric.thickening radius (extendedPlane H p a) := by
  obtain ⟨c, hc⟩ := normal_velocity_band_approximation H v a r s hs hr hv hupper hclose
  exact tube_near_extendedPlane H p a b v x t t₀ c r (2*r) R radius
    ha ht ht₀ hbase hc hx (by linarith)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normal_plane_net

#print axioms KakeyaTwoScale.normal_velocity_approximation
#print axioms KakeyaTwoScale.normal_velocity_band_approximation

#print axioms KakeyaTwoScale.high_band_tube_containment
