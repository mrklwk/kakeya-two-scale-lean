module
public import KakeyaTwoScale.ProgressionEnergy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem progression_energy_budget_algebra (a m p C J R : ℝ)
    (ha : 0 ≤ a) (hm : 0 < m) (hp : 0 < p) (hJ : 0 ≤ J) (hR : 0 ≤ R)
    (haUpper : a ≤ 2*p/m) :
    (C*(m/p))^2*((a/p)^2*J+(a/p)*R) ≤ C^2/p^2*(4*J+2*m*R) := by
  have ham : a*m ≤ 2*p := (le_div_iff₀ hm).mp haUpper
  have hsq := pow_le_pow_left₀ (mul_nonneg ha hm.le) ham 2
  have h1 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ C^2*J/p^4 by positivity)
  have h2 := mul_le_mul_of_nonneg_left ham (show 0 ≤ C^2*m*R/p^3 by positivity)
  convert add_le_add h1 h2 using 1 <;> field_simp
  all_goals ring

/-- Actual energy budget with the prime exceptional bound inserted. -/
theorem progressionEnergy_prime_budget (p m U K L B D : ℕ) [Fact p.Prime]
    (hm0 : 0 < m) (hmp : m < p) (J : Finset ℕ)
    (hprime : ∀ j ∈ J, j.Prime) (hsize : ∀ j ∈ J, L ≤ j ∧ j ≤ m)
    (hL : 1 ≤ L) (hscale : U*m ≤ K*p) (hcut : (K+2)*p < L^(B+1))
    (A : Finset (ZMod p)) (haUpper : (A.card:ℝ) ≤ 2*(p:ℝ)/(m:ℝ))
    (C : ℝ) (hC : 0 ≤ C) (ψ : ZMod p → ℂ)
    (hdec : ∀ k, ‖normalizedFourier p ψ k‖ ≤ C*((m:ℝ)/(p:ℝ))/(1+frequencySize k*(m:ℝ)/(p:ℝ))^D) :
    ∑ j ∈ J, progressionEnergy p A ψ j ≤
      C^2/(p:ℝ)^2 * (4*(J.card:ℝ)+2*(m:ℝ)*((2*K+3)*B:ℕ)+
        2*(m:ℝ)*(J.card:ℝ)/(1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*D)) := by
  have hJ : ∀ j ∈ J, (j:ZMod p) ≠ 0 := fun j hj =>
    natCast_nonzero_of_prime_below p j (hprime j hj) ((hsize j hj).2.trans_lt hmp)
  have h := progressionEnergy_sum_bound p m U D ((2*K+3)*B) J hJ A C hC ψ hdec
    (smallFrequencyIndices_card_le p m U K L B hmp J hprime hsize hL hscale hcut)
  refine h.trans ?_
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hm : 0 < (m:ℝ) := by exact_mod_cast hm0
  have hb := progression_energy_budget_algebra (A.card:ℝ) m p C J.card
    (((2*K+3)*B:ℕ)+(J.card:ℝ)/(1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*D))
    (Nat.cast_nonneg _) hm hp (Nat.cast_nonneg _) (by positivity) haUpper
  convert hb using 1; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.progression_energy_budget_algebra
#print axioms KakeyaTwoScale.progressionEnergy_prime_budget
