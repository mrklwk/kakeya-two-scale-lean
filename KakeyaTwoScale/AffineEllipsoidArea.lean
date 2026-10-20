module
public import KakeyaTwoScale.AffineEllipsoidSignMass

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Atlas independence also applies when the covered sets are propositionally
rather than definitionally equal. No equality of chart choices is asserted. -/
theorem DisjointChartAtlas.directionalArea_eq_of_set_eq {n : ℕ}
    {Z W : Set (Fin (n+1) → ℝ)} (A : DisjointChartAtlas n Z)
    (C : DisjointChartAtlas n W) (h : Z = W) (v : Fin (n+1) → ℝ) :
    A.directionalArea v = C.directionalArea v := by
  subst W
  exact A.directionalArea_independent C v

/-- The transported restricted pullback covers exactly the original zero set
localized to the specified ellipsoid, including all singular/repeated-factor zeros. -/
theorem affineEllipsoid_zero_localization {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
    (Q : MvPolynomial (Fin N) ℝ) :
    (fun x => b+x) '' (B '' ({x | MvPolynomial.eval x (polynomialAffinePullback B b Q)=0} ∩
      coordinateEuclideanBall N 1)) = {y | MvPolynomial.eval y Q=0} ∩ affineEllipsoid B b := by
  rw [← image_comp,inter_comm {x | _},inter_comm {y | _},affineEllipsoid_polynomial_set B b Q (fun r => r=0)]
  rfl

/-- Direction-by-direction identification with the actual original polynomial
atlas on E. This is the localization bridge needed by the ellipsoid theorem. -/
theorem DisjointChartAtlas.affineEllipsoid_area {n : ℕ}
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ)
    (Q : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {y | MvPolynomial.eval y Q=0})
    (C : DisjointChartAtlas n {x | MvPolynomial.eval x (polynomialAffinePullback B b Q)=0})
    (v : Fin (n+1) → ℝ) :
    (((C.restrict (coordinateEuclideanBall (n+1) 1)
      (coordinateEuclideanBall_open _ _).measurableSet).ambientMap B).translate b).directionalArea v =
      (A.restrict (affineEllipsoid B b) (affineEllipsoid_open B b).measurableSet).directionalArea v := by
  exact DisjointChartAtlas.directionalArea_eq_of_set_eq _ _
    (affineEllipsoid_zero_localization B b Q) v

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_eq_of_set_eq
#print axioms KakeyaTwoScale.affineEllipsoid_zero_localization
#print axioms KakeyaTwoScale.DisjointChartAtlas.affineEllipsoid_area
