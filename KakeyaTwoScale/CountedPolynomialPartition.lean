module
public import KakeyaTwoScale.GeneralComponentCount
public import KakeyaTwoScale.UnconditionalPolynomialPartition

@[expose] public section

open Set MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Unconditional ambient polynomial partition with actual finite cells,
explicit degree, global cell count and individual component-mass bounds. -/
theorem exists_counted_degree_budget_polynomial_partition
    (n : ℕ) (hn : 0 < n) (D : ℕ) (hD : 0 < D)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) (hwn : ∀ x, 0 ≤ w x) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      volume (ambientPolynomialZeroSet P) = 0 ∧
      (polynomialComplementComponents P).Finite ∧
      (polynomialComplementComponents P).ncard ≤ 3^n * D^n ∧
      ∀ S ∈ polynomialComplementComponents P,
        (∫ y in S, w y) ≤ ((4*(n:ℝ)^2)/(D:ℝ))^n * (∫ y, w y) := by
  obtain ⟨P,hne,hdeg,hnull,hmass⟩ :=
    exists_degree_budget_component_partition n hn D hD w hw hwn
  refine ⟨P,hne,hdeg,hnull,(polynomialComplementComponents_finite_ncard_le P).1,
    polynomialComplementComponents_ncard_le_degree_budget P hdeg hD,?_⟩
  rintro S ⟨x,hx,rfl⟩
  exact hmass x hx

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_counted_degree_budget_polynomial_partition
