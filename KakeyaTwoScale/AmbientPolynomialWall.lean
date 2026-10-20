module
public import KakeyaTwoScale.PolynomialWall
public import KakeyaTwoScale.AffineRestriction

@[expose] public section

open Metric Set
noncomputable section
namespace KakeyaTwoScale

/-- Actual zero set of the ambient multivariate polynomial. -/
def ambientPolynomialZeroSet {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | MvPolynomial.eval (fun i => x i) P=0}

/-- A capsule meets at most degree(P)+1 complementary cells outside the closed
radius-delta polynomial wall. All finite cell representatives, affine
restriction, sorting, and the identically-zero restriction case are proved.
There is no assumed crossing, partitioning, or algebraic estimate. -/
theorem finite_polynomial_capsule_cells_le_totalDegree {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (b u : EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (cells : Finset (Set (EuclideanSpace ℝ (Fin n))))
    (hmeet : ∀ S ∈ cells, ∃ x ∈ euclideanTube b u δ,
      x ∉ cthickening δ (ambientPolynomialZeroSet P) ∧
      connectedComponentIn (ambientPolynomialZeroSet P)ᶜ x=S) :
    cells.card ≤ P.totalDegree+1 := by
  classical
  let Z := ambientPolynomialZeroSet P
  let R := affineLineRestriction P b u
  have hR : ∀ t, R.eval t=0 ↔ b+t • u ∈ Z := by
    intro t
    rw [show R.eval t = MvPolynomial.eval (fun i => (b+t • u) i) P from
      affineLineRestriction_eval P b u t]
    rfl
  by_cases hzero : R=0
  · have haxis : ∀ t ∈ Icc (0:ℝ) 1, b+t • u ∈ Z := by
      intro t _
      apply (hR t).mp
      rw [hzero,Polynomial.eval_zero]
    have hempty := capsule_offwall_empty_of_axis_subset Z b u hδ haxis
    have hcempty : cells=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨x,hx,hw,_⟩ := hmeet S hS
      have : x ∈ euclideanTube b u δ \ cthickening δ Z := ⟨hx,hw⟩
      rw [hempty] at this
      exact this
    simp [hcempty]
  · exact (finite_capsule_cells_le_restriction_degree Z b u R hzero hR hδ cells hmeet).trans
      (Nat.add_le_add_right (affineLineRestriction_natDegree_le P b u) 1)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_polynomial_capsule_cells_le_totalDegree
