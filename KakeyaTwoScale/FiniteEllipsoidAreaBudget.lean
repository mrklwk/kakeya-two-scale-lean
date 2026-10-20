module
public import KakeyaTwoScale.FiniteAtlasLocalization
public import KakeyaTwoScale.FiniteEllipsoidSmoothing

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Function
noncomputable section
namespace KakeyaTwoScale

/-- Robust bisection of finitely many disjoint translates charges each common
direction once to the containing region. The constant precedes the index type,
family size, polynomial, affine map and containing region. -/
theorem finite_translated_ellipsoid_bisection (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ι : Type) [Fintype ι]
      (Q : MvPolynomial (Fin (n+1)) ℝ) (_hQ : Q ≠ 0)
      (A : DisjointChartAtlas n {x | MvPolynomial.eval x Q=0})
      (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : ι → Fin (n+1) → ℝ)
      (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U),
      Pairwise (Disjoint on fun i => affineEllipsoid B (b i)) →
      (∀ i, affineEllipsoid B (b i) ⊆ U) →
      (∀ i, (2/5:ℝ)*volume.real (affineEllipsoid B (b i)) ≤
        volume.real (affineEllipsoid B (b i) ∩ {x | 0 < MvPolynomial.eval x Q})) →
      (∀ i, (2/5:ℝ)*volume.real (affineEllipsoid B (b i)) ≤
        volume.real (affineEllipsoid B (b i) ∩ {x | MvPolynomial.eval x Q < 0})) →
      ENNReal.ofReal c * (∑ i, volume (affineEllipsoid B (b i))) ≤
        ∑ j : Fin (n+1), (A.restrict U hU).directionalArea (B (Pi.single j 1)) := by
  classical
  obtain ⟨c,hc,h⟩ := polynomial_ellipsoid_bisection n
  refine ⟨c,hc,?_⟩
  intro ι _ Q hQ A B b U hU hd hEU hp hn
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ellipsoidCoordinateAreaSum Q A B (b i) :=
      Finset.sum_le_sum (fun i _ => h Q hQ A B (b i) (hp i) (hn i))
    _ = ∑ j : Fin (n+1), ∑ i,
        (A.restrict (affineEllipsoid B (b i)) (affineEllipsoid_open B (b i)).measurableSet).directionalArea (B (Pi.single j 1)) :=
      Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun j _ => A.sum_restrict_area_le
      (fun i => affineEllipsoid B (b i)) (fun i => (affineEllipsoid_open B (b i)).measurableSet)
      hd U hU hEU (B (Pi.single j 1)))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_translated_ellipsoid_bisection
