module
public import KakeyaTwoScale.DegreeOptimization

@[expose] public section

open scoped BigOperators
namespace KakeyaTwoScale

/-- The actual HRZ ancestor-length denominator contributes s to the
zero-indexed s-th degree, not i-s. -/
theorem hrz_degree_log_identity (n i : ℕ) (D : ℕ → ℝ) :
    (∑ s ∈ Finset.range i, ((n:ℝ)-s)*D s) +
      ((i:ℝ)-1)*degreePrefixLog D i -
      (∑ s ∈ Finset.range i, (s:ℝ)*D s) = degreeConstraintLog n D i := by
  unfold degreePrefixLog degreeConstraintLog
  rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Closure of the HRZ log comparison once actual lower component count,
original-direction count (with multiplicity paid), and selected Holder
length estimate have been proved. The analytic estimates are premises. -/
theorem hrz_log_constraint {i ell lambda product grains weighted family base lowerLoss upperLoss lengthLoss : ℝ}
    (hi : 0 ≤ i)
    (hcount : family+product-grains-lowerLoss ≤ base-i*ell-weighted+upperLoss)
    (hlength : lambda-product-lengthLoss ≤ ell) :
    family-base+i*lambda-(lowerLoss+upperLoss+i*lengthLoss) ≤
      grains+(i-1)*product-weighted := by
  have hh := mul_le_mul_of_nonneg_left hlength hi
  nlinarith

/-- Independent per-stage error bounds may be collected into the uniform
error used by the exact finite optimizer; no assumption about log D signs. -/
theorem degree_optimization_with_stage_errors (n m : ℕ) (D error : ℕ → ℝ)
    (h : m+2 ≤ n) (x w E : ℝ)
    (he : ∀ i < m, error i ≤ E)
    (hc : ∀ i < m, ((i:ℝ)+1)*x+w-error i ≤ degreeConstraintLog n D (i+1)) :
    (m:ℝ)*(m+1)/(2*n)*x +
      (1/2-((n:ℝ)-m)*((n:ℝ)-m-1)/(2*n*((n:ℝ)-1)))*(w-E) ≤
        degreeObjectiveLog m m D := by
  apply degree_log_optimization n m D h x w E
  intro i hi
  have := hc i hi
  have := he i hi
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.hrz_degree_log_identity
#print axioms KakeyaTwoScale.hrz_log_constraint
#print axioms KakeyaTwoScale.degree_optimization_with_stage_errors
