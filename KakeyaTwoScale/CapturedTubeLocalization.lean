module
public import KakeyaTwoScale.CapturedWorkingSegment

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Capture of the closed working axis places its whole open tube in the
actual enlarged neighborhood and in the correctly enlarged localization ball. -/
theorem captured_centeredTube_localization {d : ℕ}
    (m u center : EuclideanSpace ℝ (Fin d)) (lambda w rho B L : ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin d))) (hrho : 0<rho) (hw : w≤rho) (hscale : rho≤L/4)
    (haxis : ∀ t∈Icc (-(lambda/2)) (lambda/2),
      m+t • u∈thickening rho (Z∩closedBall center (B*L))) :
    centeredCylinder m u lambda w⊆thickening (2*rho) Z∩ball center ((B+2)*L) := by
  rintro x ⟨q,hq0,hqL,_hi,hr⟩
  have ht : q-lambda/2∈Icc (-(lambda/2)) (lambda/2) := ⟨by linarith,by linarith⟩
  obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp (haxis (q-lambda/2) ht)
  have he : m+(q-lambda/2) • u=m-(lambda/2) • u+q • u := by module
  have hx : dist x (m+(q-lambda/2) • u)<w := by rw [he,dist_eq_norm]; exact hr
  have hxz := dist_triangle x (m+(q-lambda/2) • u) z
  have hzcenter : dist z center≤B*L := hz.2
  have hxcenter := dist_triangle x z center
  refine ⟨mem_thickening_iff.mpr ⟨z,hz.1,by linarith⟩,?_⟩
  change dist x center<(B+2)*L
  nlinarith

/-- Every captured line point itself lies in the deepest base region. -/
theorem captured_point_base_localization {d : ℕ}
    (x center : EuclideanSpace ℝ (Fin d)) (rho B L : ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin d))) (hrho : 0<rho) (hscale : rho≤L/4)
    (hx : x∈thickening rho (Z∩closedBall center (B*L))) :
    x∈thickening (2*rho) Z∩ball center ((B+2)*L) := by
  obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
  have hzc : dist z center≤B*L := hz.2
  have hh := dist_triangle x z center
  refine ⟨mem_thickening_iff.mpr ⟨z,hz.1,by linarith⟩,?_⟩
  change dist x center<(B+2)*L
  nlinarith

/-- Captured affine midpoints have the uniform common-center bound used by
nonnested-interval retention. -/
theorem captured_affine_midpoint_bound {d : ℕ}
    (b v center : EuclideanSpace ℝ (Fin d)) (s lambda rho B L : ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin d))) (hlambda : 0≤lambda) (hscale : rho≤L)
    (hcapture : ∀ t∈Icc s (s+lambda), b+t • v∈thickening rho (Z∩closedBall center (B*L))) :
    dist (b+(s+lambda/2) • v) center<(B+1)*L := by
  have hh := captured_point_dist_lt Z center (b+(s+lambda/2) • v) rho (B*L)
    (hcapture (s+lambda/2) ⟨by linarith,by linarith⟩)
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.captured_centeredTube_localization
#print axioms KakeyaTwoScale.captured_point_base_localization
#print axioms KakeyaTwoScale.captured_affine_midpoint_bound
