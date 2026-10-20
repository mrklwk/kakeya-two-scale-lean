module
public import KakeyaTwoScale.AffineAtlasArea

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The complete unit-ball bisection bound transported to every invertible affine
image, with the same dimensional constant and actual transported localization.
Directions are the images of the original coordinate vectors. -/
theorem polynomial_affine_bisection_transport (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : MvPolynomial (Fin (n+1)) ℝ)
      (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0})
      (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ),
      (2/5:ℝ)*volume.real (coordinateEuclideanBall (n+1) 1) ≤
        volume.real (coordinateEuclideanBall (n+1) 1 ∩ {x | 0 < MvPolynomial.eval x P}) →
      (2/5:ℝ)*volume.real (coordinateEuclideanBall (n+1) 1) ≤
        volume.real (coordinateEuclideanBall (n+1) 1 ∩ {x | MvPolynomial.eval x P < 0}) →
      ENNReal.ofReal c * volume ((fun x => b+B x) '' coordinateEuclideanBall (n+1) 1) ≤
        ∑ j : Fin (n+1),
          (((A.restrict (coordinateEuclideanBall (n+1) 1) (coordinateEuclideanBall_open _ _).measurableSet).ambientMap B).translate b).directionalArea (B (Pi.single j 1)) := by
  obtain ⟨c,hc,h⟩ := polynomial_ball_bisection n
  refine ⟨c,hc,?_⟩
  intro P A B b hp hn
  exact (A.restrict (coordinateEuclideanBall (n+1) 1) (coordinateEuclideanBall_open _ _).measurableSet).affine_area_lower_bound
    B b _ (ENNReal.ofReal c) (h P A hp hn)

/-- Principal-axis weights are exactly the positive axis scales under
homogeneity; no inverse-axis factor is silently introduced. -/
theorem DisjointChartAtlas.affine_axis_weights {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z)
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ)
    (l : Fin (n+1) → ℝ) (u : Fin (n+1) → (Fin (n+1) → ℝ))
    (hl : ∀ j, 0 ≤ l j) (haxis : ∀ j, B (Pi.single j 1)=l j • u j) :
    (∑ j : Fin (n+1), ((A.ambientMap B).translate b).directionalArea (B (Pi.single j 1))) =
      ∑ j : Fin (n+1), ENNReal.ofReal (l j)*((A.ambientMap B).translate b).directionalArea (u j) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [haxis j,DisjointChartAtlas.directionalArea_smul,abs_of_nonneg (hl j)]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_affine_bisection_transport
#print axioms KakeyaTwoScale.DisjointChartAtlas.affine_axis_weights
