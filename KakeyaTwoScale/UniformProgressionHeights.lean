module
public import KakeyaTwoScale.UniformProgressionArea
public import KakeyaTwoScale.ProgressionCutoff

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Uniform simultaneous arithmetic-progression heights, including the positive
step cutoff. The constant depends only on length and density, not on the family.
The finite Szemerédi input is proved in the audited dependency closure. -/
theorem uniform_progression_heights (ell : ℕ) (hell : 2 ≤ ell)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∀ {J : Type*} (family : Finset J), family.Nonempty →
      ∀ sets : J → Set ℝ,
      (∀ j ∈ family, MeasurableSet (sets j)) →
      (∀ j ∈ family, sets j ⊆ Set.Icc 0 1) →
      (∀ j ∈ family, lam ≤ volume.real (sets j)) →
      ∃ p : ℝ × ℝ, c < p.2 ∧ c*family.card ≤
        ((family.filter fun j => p ∈ progressionParameters ell (sets j)).card : ℝ) := by
  obtain ⟨N,hN,harea⟩ := uniform_progression_area ell hell lam hlam
  let c := lam/(4*(N:ℝ)^3)
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro J family hne sets hm hs ha
  apply common_separated_progression family hne sets hell hc hm hs
  intro j hj
  have he : 2*c = lam/(2*(N:ℝ)^3) := by dsimp [c]; ring
  rw [he]
  exact harea (sets j) (hm j hj) (hs j hj) (ha j hj)
end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_progression_heights
