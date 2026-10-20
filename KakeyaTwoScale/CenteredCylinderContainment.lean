module
public import KakeyaTwoScale.PrescribedCylinderFat

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

def centeredCylinder {d : ℕ} (m u : EuclideanSpace ℝ (Fin d)) (L w : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) := flatCylinder (m-(L/2) • u) u L w

/-- Exact common-line containment permits nonnested axial intervals. -/
theorem coaxial_centeredCylinder_subset {d : ℕ}
    (m m' u : EuclideanSpace ℝ (Fin d)) (L L' w w' t : ℝ)
    (hm : m=m'+t • u) (haxial : |t|+L/2≤L'/2) (hwidth : w≤w') :
    centeredCylinder m u L w⊆centeredCylinder m' u L' w' := by
  rintro x ⟨q,hq0,hqL,hi,hr⟩
  have ht := abs_le.mp (show |t|≤L'/2-L/2 by linarith)
  have he : x-(m'-(L'/2) • u+(q-L/2+t+L'/2) • u)=
      x-(m-(L/2) • u+q • u) := by rw [hm]; module
  refine ⟨q-L/2+t+L'/2,by linarith [ht.1],by linarith [ht.2],?_,?_⟩
  · rwa [he]
  · exact he ▸ hr.trans_le hwidth

/-- The prescribed Fat union contains the central enlargement of every
eligible centered cylinder, with the exact same base and axis witnesses. -/
theorem centeredCylinder_dilate_subset_prescribedFat {d : ℕ}
    (m u : EuclideanSpace ℝ (Fin d)) (a L w : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin d))) (hu : ‖u‖=1)
    (hsub : centeredCylinder m u L w⊆E) :
    centeredCylinder m u (a*L) (a*w)⊆prescribedCylinderFat a L w E := by
  intro x hx
  refine ⟨m-(L/2) • u,u,hu,hsub,?_⟩
  have he : m-(L/2) • u+((1-a)*L/2) • u=m-((a*L)/2) • u := by module
  rw [he]
  exact hx

/-- Whole-line points can be retained separately from shortened working tubes;
this is the version needed for the common outer sweep slab. -/
theorem line_point_mem_centeredCylinder {d : ℕ}
    (m u : EuclideanSpace ℝ (Fin d)) (t L w : ℝ) (ht : |t|<L/2) (hw : 0<w) :
    m+t • u∈centeredCylinder m u L w := by
  have he : m+t • u-(m-(L/2) • u+(t+L/2) • u)=0 := by module
  refine ⟨t+L/2,by linarith [(abs_lt.mp ht).1],by linarith [(abs_lt.mp ht).2],?_,?_⟩
  · rw [he]; simp
  · rw [he,norm_zero]; exact hw

/-- The original cylinder width enlarges the captured-axis neighborhood by
exactly w. This uses actual nearby witnesses and the triangle inequality. -/
theorem centeredCylinder_subset_thickening {d : ℕ}
    (m u : EuclideanSpace ℝ (Fin d)) (L w rho : ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin d)))
    (haxis : ∀ t∈Icc (-(L/2)) (L/2), m+t • u∈thickening rho Z) :
    centeredCylinder m u L w⊆thickening (rho+w) Z := by
  rintro x ⟨t,ht0,htL,_hi,hr⟩
  have ht : t-L/2∈Icc (-(L/2)) (L/2) := ⟨by linarith,by linarith⟩
  obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp (haxis (t-L/2) ht)
  refine mem_thickening_iff.mpr ⟨z,hz,?_⟩
  have he : m+(t-L/2) • u=m-(L/2) • u+t • u := by module
  have hx : dist x (m+(t-L/2) • u)<w := by rw [he,dist_eq_norm]; exact hr
  have hh := dist_triangle x (m+(t-L/2) • u) z
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coaxial_centeredCylinder_subset
#print axioms KakeyaTwoScale.centeredCylinder_dilate_subset_prescribedFat
#print axioms KakeyaTwoScale.line_point_mem_centeredCylinder
#print axioms KakeyaTwoScale.centeredCylinder_subset_thickening
