module
public import KakeyaTwoScale.ThicknessFiniteCover
public import KakeyaTwoScale.EuclideanCylinderExtensionVolume

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The actual central dilates of unit-axis cylinders with prescribed original
length and width, contained in E. There is no finite population parameter. -/
def prescribedCylinderFat {d : ℕ} (a L w : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ b u, ‖u‖=1 ∧ flatCylinder b u L w⊆E ∧
    x∈flatCylinder (b+((1-a)*L/2) • u) u (a*L) (a*w)}

theorem prescribedCylinderFat_subset {d : ℕ} (a L w : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin d))) (hL : 0<L) (hw : 0<w) :
    prescribedCylinderFat a L w E ⊆ flatCylinderFatUnion a E := by
  rintro x ⟨b,u,_hu,hsub,hx⟩
  exact ⟨b,u,L,w,hL,hw,hsub,hx⟩

/-- Local thickness is discharged from the actual defining cylinders. -/
theorem prescribedCylinderFat_inner_ball {d : ℕ} (a L w : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin d))) (ha : 0<a) (hw : 0<w) (hwL : w≤L) :
    ∀ x∈prescribedCylinderFat a L w E,
      ∃ y, ball y (a*w/8)⊆prescribedCylinderFat a L w E∩ball x (a*w) := by
  rintro x ⟨b,u,hu,hsub,hx⟩
  obtain ⟨y,_hy,hball⟩ := flatCylinder_local_thickness
    (b+((1-a)*L/2) • u) u (a*L) (a*w) hu (mul_pos ha hw)
    (mul_le_mul_of_nonneg_left hwL ha.le) x hx
  refine ⟨y,fun z hz => ?_⟩
  exact ⟨⟨b,u,hu,hsub,(hball hz).1⟩,(hball hz).2⟩

/-- Actual finite covering of a finite-volume prescribed Fat union, with its
cardinality paid for by disjoint inner-ball volumes. -/
theorem prescribedCylinderFat_cover {d : ℕ} (a L w : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin d))) (ha : 0<a) (hw : 0<w) (hwL : w≤L)
    (hfinite : volume (prescribedCylinderFat a L w E)≠⊤) :
    ∃ F : Finset (EuclideanSpace ℝ (Fin d)),
      (↑F : Set _)⊆prescribedCylinderFat a L w E ∧
      prescribedCylinderFat a L w E⊆⋃ x∈F,ball x (2*(a*w)) ∧
      (F.card : ℝ≥0∞)*volume (ball (0 : EuclideanSpace ℝ (Fin d)) (a*w/8))≤
        volume (prescribedCylinderFat a L w E) :=
  thickness_finite_cover _ (a*w) (mul_pos ha hw) hfinite
    (prescribedCylinderFat_inner_ball a L w E ha hw hwL)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.prescribedCylinderFat_subset
#print axioms KakeyaTwoScale.prescribedCylinderFat_inner_ball
#print axioms KakeyaTwoScale.prescribedCylinderFat_cover
