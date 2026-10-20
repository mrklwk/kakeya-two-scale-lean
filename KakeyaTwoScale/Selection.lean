module
public import Mathlib.Tactic

@[expose] public section

/-! Finite bookkeeping for fixed parent weights. These lemmas do not assert
that geometric tubes provide the hypotheses. -/
namespace KakeyaTwoScale
open scoped BigOperators

/-- Cellwise child mass is bounded by twice the full-cube parent weight.
In the paper d = δ^m and r = ρ^m. The original capacities stay fixed. -/
theorem cell_mass_bound {P : Type*} (parents : Finset P)
    (count capacity : P → ℝ) (d r u : ℝ) (hd : 0 ≤ d)
    (hcount : ∀ p ∈ parents, count p ≤ capacity p)
    (hcapacity : ∀ p ∈ parents, d * capacity p ≤ 2*u*r) :
    d * ∑ p ∈ parents, count p ≤ 2*r*(u*parents.card) := by
  calc
    d * ∑ p ∈ parents, count p = ∑ p ∈ parents, d*count p := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _p ∈ parents, 2*u*r := Finset.sum_le_sum fun p hp =>
      (mul_le_mul_of_nonneg_left (hcount p hp) hd).trans (hcapacity p hp)
    _ = 2*r*(u*parents.card) := by simp; ring

/-- Low-weight cells lose at most twice threshold times occupied volume.
A geometric implementation will integrate this finite-cell inequality. -/
theorem low_cell_loss {C : Type*} (cells : Finset C)
    (mass volume weight : C → ℝ) (M : ℝ)
    (hvol : ∀ c ∈ cells, 0 ≤ volume c)
    (hweight : ∀ c ∈ cells, weight c ≤ M)
    (hmass : ∀ c ∈ cells, mass c ≤ 2*volume c*weight c) :
    ∑ c ∈ cells, mass c ≤ 2*M*∑ c ∈ cells, volume c := by
  calc
    ∑ c ∈ cells, mass c ≤ ∑ c ∈ cells, 2*M*volume c := by
      apply Finset.sum_le_sum
      intro c hc
      have h := mul_le_mul_of_nonneg_left (hweight c hc)
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hvol c hc))
      nlinarith [hmass c hc]
    _ = 2*M*∑ c ∈ cells, volume c := by rw [Finset.mul_sum]

/-- Exact mass budget after narrow selection and the three subsequent losses. -/
theorem retained_mass (U R l₁ l₂ l₃ : ℝ) (hU : 0 ≤ U)
    (h₁ : l₁ ≤ U/100) (h₂ : l₂ ≤ 2*U/100) (h₃ : l₃ ≤ U/100)
    (hR : 3*U/8-l₁-l₂-l₃ ≤ R) : U/4 ≤ R := by
  linarith
end KakeyaTwoScale

#print axioms KakeyaTwoScale.cell_mass_bound
#print axioms KakeyaTwoScale.low_cell_loss
#print axioms KakeyaTwoScale.retained_mass
