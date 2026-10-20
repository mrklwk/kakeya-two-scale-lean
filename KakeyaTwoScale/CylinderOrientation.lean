module
public import KakeyaTwoScale.LocalizedChartBoxes

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

theorem flatCylinder_reverse {n : ℕ} (b u : EuclideanSpace ℝ (Fin n)) (L delta : ℝ) :
    flatCylinder (b+L • u) (-u) L delta=flatCylinder b u L delta := by
  ext x
  constructor
  · rintro ⟨t,ht,htL,hperp,hnorm⟩
    have he : b+L • u+t • (-u)=b+(L-t) • u := by module
    refine ⟨L-t,by linarith,by linarith,?_,?_⟩
    · rw [he,inner_neg_left] at hperp
      linarith
    · rwa [he] at hnorm
  · rintro ⟨t,ht,htL,hperp,hnorm⟩
    have he : b+L • u+(L-t) • (-u)=b+t • u := by module
    refine ⟨L-t,by linarith,by linarith,?_,?_⟩
    · rw [he,inner_neg_left,hperp,neg_zero]
    · rwa [he]

def orientedCylinderBase {n : ℕ} (reverse : Bool) (b u : EuclideanSpace ℝ (Fin n)) (L : ℝ) :
    EuclideanSpace ℝ (Fin n) := if reverse then b+L • u else b

theorem oriented_flatCylinder {n : ℕ} (reverse : Bool)
    (b u : EuclideanSpace ℝ (Fin n)) (L delta : ℝ) :
    flatCylinder (orientedCylinderBase reverse b u L) (orientedDirection reverse u) L delta=
      flatCylinder b u L delta := by
  cases reverse
  · rfl
  · exact flatCylinder_reverse b u L delta

end KakeyaTwoScale
#print axioms KakeyaTwoScale.flatCylinder_reverse
#print axioms KakeyaTwoScale.oriented_flatCylinder
