module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped BigOperators
namespace KakeyaTwoScale

/-- Fractions of equal-volume cubes retained by trimmed cells. This finite
selection lemma asserts no geometric partition exists. -/
theorem heavy_fraction_count {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (ha : ∀ q ∈ Q, a q ≤ 1)
    (hmass : θ * Q.card ≤ ∑ q ∈ Q, a q) :
    θ / 2 * Q.card ≤ (Q.filter fun q => θ / 2 ≤ a q).card := by
  classical
  let G := Q.filter fun q => θ / 2 ≤ a q
  have hb : ∀ q ∈ Q, a q ≤ (if q ∈ G then 1 else 0) + θ / 2 := by
    intro q hq
    by_cases hg : q ∈ G
    · simp only [hg, ↓reduceIte]
      linarith [ha q hq]
    · have hl : a q < θ / 2 := by
        simpa only [G, Finset.mem_filter, hq, true_and, not_le] using hg
      simp only [hg, ↓reduceIte, zero_add]
      exact hl.le
  have hs := Finset.sum_le_sum hb
  have hsub : Q.filter (fun q => q ∈ G) = G := by
    ext q
    simp only [G, Finset.mem_filter, and_self_left]
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter, hsub,
    Finset.sum_const, nsmul_eq_mul] at hs
  nlinarith

/-- A trimmed-mass upper bound controls the number of heavy cubes assigned
to one cell, even when the untrimmed cell mass is unavailable. -/
theorem heavy_fiber_count {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℝ) {θ B : ℝ} (hθ : 0 < θ)
    (ha : ∀ q ∈ S, θ / 2 ≤ a q)
    (hmass : ∑ q ∈ S, a q ≤ B) :
    (S.card : ℝ) ≤ 2 * B / θ := by
  have hs := Finset.sum_le_sum ha
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  apply (le_div_iff₀ hθ).2
  nlinarith

/-- Algebraic capture needs only cubes with positive captured fraction.
The geometric enlargement then converts point capture to whole-cube capture. -/
theorem positive_fraction_count {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a : ι → ℝ) {θ : ℝ}
    (ha : ∀ q ∈ Q, a q ≤ 1)
    (hmass : θ * Q.card ≤ ∑ q ∈ Q, a q) :
    θ * Q.card ≤ (Q.filter fun q => 0 < a q).card := by
  classical
  have hb : ∀ q ∈ Q, a q ≤ if 0 < a q then 1 else 0 := by
    intro q hq
    split_ifs with h
    · exact ha q hq
    · exact le_of_not_gt h
  have hs := Finset.sum_le_sum hb
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  exact hmass.trans hs

end KakeyaTwoScale

#print axioms KakeyaTwoScale.heavy_fraction_count
#print axioms KakeyaTwoScale.heavy_fiber_count
#print axioms KakeyaTwoScale.positive_fraction_count
