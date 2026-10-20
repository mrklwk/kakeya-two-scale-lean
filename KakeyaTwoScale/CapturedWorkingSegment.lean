module
public import KakeyaTwoScale.CenteredCylinderContainment
public import KakeyaTwoScale.GraphParentCapsule

@[expose] public section

open Set Metric NormedSpace
noncomputable section
namespace KakeyaTwoScale

/-- A graph-speed lower bound permits a centered physical segment of the same
numerical length, wholly inside the captured parameter interval. -/
theorem centered_working_segment_parameter {d : ℕ}
    (b v : EuclideanSpace ℝ (Fin d)) (s L : ℝ) (hL : 0≤L) (hv : 1≤‖v‖) :
    ∀ q∈Icc (-(L/2)) (L/2), ∃ t∈Icc s (s+L),
      b+(s+L/2) • v+q • normalize v=b+t • v := by
  intro q hq
  have hvpos : 0<‖v‖ := lt_of_lt_of_le zero_lt_one hv
  have hlow : -(L/2)≤q/‖v‖ := by
    apply (le_div_iff₀ hvpos).mpr
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hv),hq.1]
  have hhigh : q/‖v‖≤L/2 := by
    apply (div_le_iff₀ hvpos).mpr
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hv),hq.2]
  refine ⟨s+L/2+q/‖v‖,⟨by linarith,by linarith⟩,?_⟩
  simp only [NormedSpace.normalize,div_eq_mul_inv,smul_smul]
  module

/-- Truncated capture bounds every captured point's distance to the common
center with the necessary radius enlargement. -/
theorem captured_point_dist_lt {d : ℕ} (Z : Set (EuclideanSpace ℝ (Fin d)))
    (center x : EuclideanSpace ℝ (Fin d)) (rho R : ℝ)
    (hx : x∈thickening rho (Z∩closedBall center R)) : dist x center<R+rho := by
  obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
  have hh := dist_triangle x y center
  have hyR : dist y center≤R := hy.2
  linarith

/-- The actual physical working axis inherits the original truncated capture. -/
theorem captured_working_axis {d : ℕ} (b v : EuclideanSpace ℝ (Fin d))
    (s L rho : ℝ) (Z : Set (EuclideanSpace ℝ (Fin d)))
    (hL : 0≤L) (hv : 1≤‖v‖)
    (hcapture : ∀ t∈Icc s (s+L), b+t • v∈thickening rho Z) :
    ∀ q∈Icc (-(L/2)) (L/2), b+(s+L/2) • v+q • normalize v∈thickening rho Z := by
  intro q hq
  obtain ⟨t,ht,he⟩ := centered_working_segment_parameter b v s L hL hv q hq
  rw [he]
  exact hcapture t ht

/-- Points on one affine line use one exact oriented unit axis at all levels. -/
theorem affine_line_normalized_difference {d : ℕ}
    (b v : EuclideanSpace ℝ (Fin d)) (s t : ℝ) :
    b+t • v=b+s • v+((t-s)*‖v‖) • normalize v := by
  have he : ((t-s)*‖v‖) • normalize v=(t-s) • v := by
    rw [mul_smul,norm_smul_normalize]
  rw [he]
  module

end KakeyaTwoScale
#print axioms KakeyaTwoScale.centered_working_segment_parameter
#print axioms KakeyaTwoScale.captured_point_dist_lt
#print axioms KakeyaTwoScale.captured_working_axis
#print axioms KakeyaTwoScale.affine_line_normalized_difference
