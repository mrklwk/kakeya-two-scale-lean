module
public import KakeyaTwoScale.EuclideanCapturedDirectionBall
public import KakeyaTwoScale.LocalizedAxisTruncation
public import KakeyaTwoScale.EqualWidthCylinderAncestry
public import KakeyaTwoScale.ChartTubeContainment

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- A common translated intercept reconstructs every point of the same axis. -/
theorem translated_chart_axis {n : ℕ} (h : Fin (n+1))
    (c u center : EuclideanSpace ℝ (Fin (n+1))) (hu : u h ≠ 0) (s : ℝ) :
    center + euclideanUnsplit h ((c+s • u-center) h,
      chartIntercept h (c-center) u 0 + (c+s • u-center) h • chartSlope h u) = c+s • u := by
  apply WithLp.ofLp_injective 2
  apply funext
  apply (Fin.forall_iff_succAbove h (P := fun j =>
    (center + euclideanUnsplit h ((c+s • u-center) h,
      chartIntercept h (c-center) u 0 + (c+s • u-center) h • chartSlope h u)) j =
        (c+s • u) j)).mpr
  constructor
  · simp [unsplit_height]
  · intro j
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
      unsplit_horizontal,Pi.add_apply,Pi.smul_apply,chartIntercept,chartSlope]
    field_simp
    ring

/-- Projected middle-half heights, retained unchanged under slope perturbation. -/
def middleHalfHeights {n : ℕ} (h : Fin (n+1))
    (b u center : EuclideanSpace ℝ (Fin (n+1))) (L : ℝ) : Set ℝ :=
  {t | ∃ s ∈ Icc (L/4) (3*L/4), t=(b+s • u-center) h}

/-- Actual nested equal-width cylinders supply all chart capture and time-bound
hypotheses of the direction-ball theorem. A single localized descendant point
and its base give one common intercept for every ancestor. There is no assumed
eligible-direction ball or chart capture in this theorem. -/
theorem localized_cylinder_direction_ball {n : ℕ} {I : Type*}
    (h : Fin (n+1)) (b : I → EuclideanSpace ℝ (Fin (n+1)))
    (c u center w : EuclideanSpace ℝ (Fin (n+1)))
    (V : I → Set (EuclideanSpace ℝ (Fin (n+1)))) (L : I → ℝ)
    (ell delta rho C : ℝ) (hu : ‖u‖=1) (huh : u h ≠ 0)
    (hell : 0 < ell) (hdelta : 0 < delta) (hC : 0 ≤ C)
    (hL : ∀ i, 0 < L i) (hLone : ∀ i, L i ≤ 1)
    (hdeltaL : ∀ i, delta ≤ L i) (hellL : ∀ i, ell ≤ L i)
    (hlong : ∀ i, 8*rho ≤ L i)
    (hcontain : ∀ i, flatCylinder c u ell delta ⊆ flatCylinder (b i) u (L i) delta)
    (hw : w ∈ flatCylinder c u ell delta) (hwball : dist w center < C*ell)
    (hcapture : ∀ i, flatCylinder (b i) u (L i) delta ⊆ thickening rho (V i)) :
    ball (chartSlope h u) (delta/(16*(n+2:ℝ)*(C+3))) ⊆
      interior {v | ∃ a, chartLineCaptured h center
        (fun i => V i ∩ closedBall center ((C+4)*L i))
        (fun i => middleHalfHeights h (b i) u center (L i)) (rho+delta) v a} := by
  have hbase (i) := equal_width_cylinder_base (b i) c u (L i) ell delta
    hu hell hdelta (hcontain i)
  have hpoint (i) (s : ℝ) (hs : s ∈ Icc (L i/4) (3*L i/4)) :
      b i+s • u ∈ flatCylinder (b i) u (L i) delta := by
    refine ⟨s,by linarith [hs.1,hL i],by linarith [hs.2,hL i],?_,?_⟩
    · simp
    · simpa using hdelta
  have htime (i) (t : ℝ) (ht : t ∈ middleHalfHeights h (b i) u center (L i)) :
      |t| ≤ C+3 := by
    obtain ⟨s,hs,rfl⟩ := ht
    have hd := flatCylinder_pair_dist_lt (b i) u (b i+s • u) w (L i) delta hu
      (hpoint i s hs) (hcontain i hw)
    have ht := dist_triangle (b i+s • u) w center
    have hcoord : |(b i+s • u-center) h| ≤ dist (b i+s • u) center := by
      simpa only [Real.norm_eq_abs,dist_eq_norm] using PiLp.norm_apply_le (b i+s • u-center) h
    have hscale := mul_le_mul_of_nonneg_left (hellL i) hC
    have hscale' := mul_le_mul_of_nonneg_left (hLone i) (show 0 ≤ C+3 by linarith)
    nlinarith [hdeltaL i]
  apply euclidean_direction_ball_interior h center _ _ (chartIntercept h (c-center) u 0)
    (chartSlope h u) rho delta (C+3) hdelta (by linarith) htime
  intro i t ht
  obtain ⟨s,hs,rfl⟩ := ht
  have he : b i+s • u=c+(s-inner ℝ u (c-b i)) • u := by
    nth_rw 1 [hbase i]
    module
  have hchart := translated_chart_axis h c u center huh (s-inner ℝ u (c-b i))
  rw [← he] at hchart
  rw [hchart]
  exact (localized_axis_truncation (b i) u center w (V i) (L i) ell delta rho C
    hu (hL i) hdelta (hdeltaL i) (hellL i) hC (hlong i)
    (hcontain i hw) hwball (hcapture i)).1 s hs

end KakeyaTwoScale
#print axioms KakeyaTwoScale.translated_chart_axis
#print axioms KakeyaTwoScale.localized_cylinder_direction_ball
