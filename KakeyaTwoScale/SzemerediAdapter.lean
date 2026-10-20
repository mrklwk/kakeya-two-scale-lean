module
public import DensityHalesJewett.Szemeredi
public import Mathlib.Tactic

@[expose] public section

namespace KakeyaTwoScale
/-- The finite density input used in the common-progression-height argument.
The threshold is positive and depends only on length and density. -/
theorem finite_szemeredi (ell : ℕ) (density : ℝ) (hd : 0 < density) :
    ∃ N : ℕ, 0 < N ∧ ∀ A : Finset ℕ, A ⊆ Finset.range N →
      density * (N : ℝ) ≤ A.card →
      ∃ s d : ℕ, 0 < d ∧ ∀ i : ℕ, i < ell → s+i*d ∈ A := by
  let k := max ell 3
  let bound := Combinatorics.ArithmeticProgression.densityTheoremBound k density
  refine ⟨max bound 1, by omega, ?_⟩
  intro A hA hc
  obtain ⟨P, hP⟩ := Combinatorics.ArithmeticProgression.exists_of_density_nat
    k (by dsimp [k]; omega) density hd (max bound 1) (le_max_left _ _) A hA hc
  refine ⟨P.start, P.diff, Nat.pos_of_ne_zero P.diff_ne_zero, ?_⟩
  intro i hi
  have hik : i < k := lt_of_lt_of_le hi (le_max_left _ _)
  simpa [Combinatorics.ArithmeticProgression.term, nsmul_eq_mul] using hP ⟨i,hik⟩
end KakeyaTwoScale
#print axioms Combinatorics.ArithmeticProgression.exists_of_density_nat
#print axioms KakeyaTwoScale.finite_szemeredi
