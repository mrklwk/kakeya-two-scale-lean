module
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Polynomials separate any finite family of distinct points over a field.
This is the evaluation-surjectivity input for quantitative root counting. -/
theorem finite_polynomial_interpolation {K σ ι : Type*} [Field K] [Fintype ι]
    (x : ι → σ → K) (hx : Function.Injective x) (v : ι → K) :
    ∃ p : MvPolynomial σ K, ∀ i, MvPolynomial.eval (x i) p = v i := by
  classical
  have hsep : ∀ i j : ι, i ≠ j → ∃ p : MvPolynomial σ K,
      MvPolynomial.eval (x i) p = 1 ∧ MvPolynomial.eval (x j) p = 0 := by
    intro i j hij
    have hne : x i ≠ x j := fun h => hij (hx h)
    obtain ⟨k,hk⟩ := Function.ne_iff.mp hne
    refine ⟨MvPolynomial.C ((x i k - x j k)⁻¹) *
      (MvPolynomial.X k - MvPolynomial.C (x j k)), ?_, ?_⟩
    · simp [sub_ne_zero.mpr hk]
    · simp
  have hb : ∀ i : ι, ∃ p : MvPolynomial σ K,
      ∀ j, MvPolynomial.eval (x j) p = if j = i then 1 else 0 := by
    intro i
    choose p hp using fun j : {j : ι // j ≠ i} => hsep i j.val j.property.symm
    refine ⟨∏ j, p j, ?_⟩
    intro j
    rw [map_prod]
    by_cases hji : j = i
    · subst j
      simp [hp]
    · rw [ite_eq_right (by simpa using hji)]
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨j,hji⟩ : {j : ι // j ≠ i}))
      exact (hp ⟨j,hji⟩).2
  choose p hp using hb
  refine ⟨∑ i, MvPolynomial.C (v i) * p i, ?_⟩
  intro j
  simp [hp]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_polynomial_interpolation
