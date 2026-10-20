module
public import KakeyaTwoScale.AffineEllipsoidArea

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual directional area sum of Q on the specified ellipsoid. -/
def ellipsoidCoordinateAreaSum {n : ℕ} (Q : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {y | MvPolynomial.eval y Q=0})
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin (n+1), (A.restrict (affineEllipsoid B b)
    (affineEllipsoid_open B b).measurableSet).directionalArea (B (Pi.single j 1))

/-- Complete original-polynomial ellipsoid bisection: the same positive
constant is fixed by dimension before Q, the atlas, the translation and all axes.
The hypotheses are the two actual strict-sign volumes on the ellipsoid. -/
theorem polynomial_ellipsoid_bisection (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : MvPolynomial (Fin (n+1)) ℝ) (_hQ : Q ≠ 0)
      (A : DisjointChartAtlas n {y | MvPolynomial.eval y Q=0})
      (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ),
      (2/5:ℝ)*volume.real (affineEllipsoid B b) ≤
        volume.real (affineEllipsoid B b ∩ {y | 0 < MvPolynomial.eval y Q}) →
      (2/5:ℝ)*volume.real (affineEllipsoid B b) ≤
        volume.real (affineEllipsoid B b ∩ {y | MvPolynomial.eval y Q < 0}) →
      ENNReal.ofReal c * volume (affineEllipsoid B b) ≤ ellipsoidCoordinateAreaSum Q A B b := by
  obtain ⟨c,hc,h⟩ := polynomial_affine_bisection_transport n
  refine ⟨c,hc,?_⟩
  intro Q hQ A B b hp hn
  let P := polynomialAffinePullback B b Q
  have hP : P ≠ 0 := polynomialAffinePullback_ne_zero B b Q hQ
  let C := (polynomial_disjoint_chart_atlas P hP).some
  have hp' := affineEllipsoid_mass_pullback B b Q (fun r => 0 < r) (2/5) hp
  have hn' := affineEllipsoid_mass_pullback B b Q (fun r => r < 0) (2/5) hn
  have hb := h P C B b hp' hn'
  change ENNReal.ofReal c * volume (affineEllipsoid B b) ≤ _ at hb
  calc
    _ ≤ _ := hb
    _ = ellipsoidCoordinateAreaSum Q A B b := by
      apply Finset.sum_congr rfl
      intro j _
      exact A.affineEllipsoid_area B b Q C (B (Pi.single j 1))

/-- The original Q atlas is constructed rather than supplied by the caller. -/
def polynomialEllipsoidCoordinateArea {n : ℕ}
    (Q : MvPolynomial (Fin (n+1)) ℝ) (hQ : Q ≠ 0)
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ) : ℝ≥0∞ :=
  ellipsoidCoordinateAreaSum Q (polynomial_disjoint_chart_atlas Q hQ).some B b

theorem actual_polynomial_ellipsoid_bisection (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : MvPolynomial (Fin (n+1)) ℝ) (hQ : Q ≠ 0)
      (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ),
      (2/5:ℝ)*volume.real (affineEllipsoid B b) ≤
        volume.real (affineEllipsoid B b ∩ {y | 0 < MvPolynomial.eval y Q}) →
      (2/5:ℝ)*volume.real (affineEllipsoid B b) ≤
        volume.real (affineEllipsoid B b ∩ {y | MvPolynomial.eval y Q < 0}) →
      ENNReal.ofReal c * volume (affineEllipsoid B b) ≤ polynomialEllipsoidCoordinateArea Q hQ B b := by
  obtain ⟨c,hc,h⟩ := polynomial_ellipsoid_bisection n
  exact ⟨c,hc,fun Q hQ => h Q hQ (polynomial_disjoint_chart_atlas Q hQ).some⟩

/-- Principal-axis formulation with actual area on E. The direction/scaling
identity is an explicit hypothesis, so no unproved spectral choice is hidden. -/
theorem polynomial_ellipsoid_bisection_axis_weights (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : MvPolynomial (Fin (n+1)) ℝ) (_hQ : Q ≠ 0)
      (A : DisjointChartAtlas n {y | MvPolynomial.eval y Q=0})
      (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ)
      (l : Fin (n+1) → ℝ) (u : Fin (n+1) → (Fin (n+1) → ℝ)),
      (∀ j, 0 ≤ l j) → (∀ j, B (Pi.single j 1)=l j • u j) →
      (2/5:ℝ)*volume.real (affineEllipsoid B b) ≤
        volume.real (affineEllipsoid B b ∩ {y | 0 < MvPolynomial.eval y Q}) →
      (2/5:ℝ)*volume.real (affineEllipsoid B b) ≤
        volume.real (affineEllipsoid B b ∩ {y | MvPolynomial.eval y Q < 0}) →
      ENNReal.ofReal c * volume (affineEllipsoid B b) ≤
        ∑ j : Fin (n+1), ENNReal.ofReal (l j) *
          (A.restrict (affineEllipsoid B b) (affineEllipsoid_open B b).measurableSet).directionalArea (u j) := by
  obtain ⟨c,hc,h⟩ := polynomial_ellipsoid_bisection n
  refine ⟨c,hc,?_⟩
  intro Q hQ A B b l u hl haxis hp hn
  have hb := h Q hQ A B b hp hn
  unfold ellipsoidCoordinateAreaSum at hb
  simpa only [haxis,DisjointChartAtlas.directionalArea_smul,abs_of_nonneg (hl _)] using hb

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_ellipsoid_bisection
#print axioms KakeyaTwoScale.actual_polynomial_ellipsoid_bisection
#print axioms KakeyaTwoScale.polynomial_ellipsoid_bisection_axis_weights
