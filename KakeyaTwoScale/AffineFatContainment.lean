module
public import KakeyaTwoScale.RecursionScaleConstants

@[expose] public section

open Set Metric NormedSpace
noncomputable section
namespace KakeyaTwoScale

theorem affine_axis_parameter_bound {d : ℕ}
    (b v center : EuclideanSpace ℝ (Fin d)) (s t B L l : ℝ)
    (hv : v≠0) (hB : 0≤B) (hlL : l≤L)
    (hs : dist (b+s • v) center<(B+1)*L)
    (ht : dist (b+t • v) center<(B+1)*l) :
    |(s-t)*‖v‖|<2*(B+1)*L := by
  have he := affine_line_normalized_difference b v t s
  have hd : dist (b+s • v) (b+t • v)=|(s-t)*‖v‖| := by
    rw [he,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,norm_normalize hv,mul_one]
  have hh := dist_triangle (b+s • v) center (b+t • v)
  rw [dist_comm center _,hd] at hh
  have hscale := mul_le_mul_of_nonneg_left hlL (by linarith : 0≤B+1)
  nlinarith

/-- A fixed dimension/localization dilation absorbs the actual shift between
same-line working tubes, without assuming their axial intervals nested. -/
theorem affine_workingTube_Fat_containment {n : ℕ}
    (b v center : EuclideanSpace ℝ (Fin (n+1))) (s t B L l w : ℝ)
    (hv : v≠0) (hB : 0≤B) (hl : 0<l) (hlL : l≤L) (hw : 0≤w)
    (hs : dist (b+s • v) center<(B+1)*L)
    (ht : dist (b+t • v) center<(B+1)*l) :
    centeredCylinder (b+s • v) (normalize v) (recursionKappa n*L) w⊆
      centeredCylinder (b+t • v) (normalize v)
        ((recursionDilation n B*L/l)*(recursionKappa n*l))
        ((recursionDilation n B*L/l)*w) := by
  have hL := hl.trans_le hlL
  have hshift := affine_axis_parameter_bound b v center s t B L l hv hB hlL hs ht
  have hmargin := recursion_axial_margin n B L l hB hL hl
  have hD := recursionDilation_ge_one n B hB
  have ha : 1≤recursionDilation n B*L/l := by
    apply (le_div_iff₀ hl).mpr
    have hm := mul_le_mul_of_nonneg_right hD hL.le
    nlinarith
  apply coaxial_centeredCylinder_subset _ _ _ _ _ _ _ ((s-t)*‖v‖)
    (affine_line_normalized_difference b v t s)
  · linarith
  · exact le_mul_of_one_le_left hw ha

/-- Full outer captured points, not only the shortened physical segment, fit
inside the child dilation. This is the fixed-slab sweep containment ingredient. -/
theorem affine_point_Fat_containment {n : ℕ}
    (b v center : EuclideanSpace ℝ (Fin (n+1))) (s t B L l w : ℝ)
    (hv : v≠0) (hB : 0≤B) (hl : 0<l) (hlL : l≤L) (hw : 0<w)
    (hs : dist (b+s • v) center<(B+1)*L)
    (ht : dist (b+t • v) center<(B+1)*l) :
    b+s • v∈centeredCylinder (b+t • v) (normalize v)
      ((recursionDilation n B*L/l)*(recursionKappa n*l))
      ((recursionDilation n B*L/l)*w) := by
  have hL := hl.trans_le hlL
  have hshift := affine_axis_parameter_bound b v center s t B L l hv hB hlL hs ht
  have hmargin := recursion_axial_margin n B L l hB hL hl
  have hD : 0<recursionDilation n B := lt_of_lt_of_le zero_lt_one (recursionDilation_ge_one n B hB)
  rw [affine_line_normalized_difference b v t s]
  apply line_point_mem_centeredCylinder
  · have hk := mul_pos (recursionKappa_pos n) hL
    linarith
  · positivity

end KakeyaTwoScale
#print axioms KakeyaTwoScale.affine_axis_parameter_bound
#print axioms KakeyaTwoScale.affine_workingTube_Fat_containment
#print axioms KakeyaTwoScale.affine_point_Fat_containment
