module
public import KakeyaTwoScale.DyadicPrimeDensity

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

/-- The actual integer half-interval in PZ's restricted-index argument. -/
def halfIntervalPrimes (m : ℕ) : Finset ℕ :=
  (Finset.Icc ((m+1)/2) m).filter Nat.Prime

theorem dyadicPrimes_subset_halfInterval (m : ℕ) :
    dyadicPrimes (m/2) ⊆ halfIntervalPrimes m := by
  intro p hp
  obtain ⟨hp,hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hprime⟩

/-- Quantitative half-interval prime count, with parity and integer endpoints
included. All sufficiently large integers m, not merely primes or even m. -/
theorem halfIntervalPrimes_log_density : ∀ᶠ m : ℕ in atTop,
    (Real.log 4/18)*(m:ℝ) ≤ ((halfIntervalPrimes m).card:ℝ)*Real.log m := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp dyadic_prime_density_eventually
  refine eventually_atTop.mpr ⟨max (2*N) 4,?_⟩
  intro m hm
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm
  have hnN : N ≤ m/2 := by have := le_trans (le_max_left (2*N) 4) hm; omega
  have h := hN (m/2) hnN
  have hthird : (m:ℝ) ≤ 3*(m/2:ℕ) := by exact_mod_cast (show m ≤ 3*(m/2) by omega)
  have hcard : ((dyadicPrimes (m/2)).card:ℝ) ≤ (halfIntervalPrimes m).card := by
    exact_mod_cast Finset.card_le_card (dyadicPrimes_subset_halfInterval m)
  have hlog : Real.log (2*(m/2:ℕ):ℝ) ≤ Real.log (m:ℝ) :=
    Real.log_le_log (by
      have : (2:ℝ) ≤ (m/2:ℕ) := by exact_mod_cast (show 2 ≤ m/2 by omega)
      positivity) (by exact_mod_cast (show 2*(m/2) ≤ m by omega))
  have hlognonneg : 0 ≤ Real.log (2*(m/2:ℕ):ℝ) := Real.log_nonneg (by
    have : (2:ℝ) ≤ (m/2:ℕ) := by exact_mod_cast (show 2 ≤ m/2 by omega)
    linarith)
  have hc : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  calc
    Real.log 4/18*(m:ℝ) ≤ Real.log 4/6*(m/2:ℕ) := by nlinarith
    _ ≤ ((dyadicPrimes (m/2)).card:ℝ)*Real.log (2*(m/2:ℕ)) := h
    _ ≤ ((halfIntervalPrimes m).card:ℝ)*Real.log m :=
      mul_le_mul hcard hlog hlognonneg (by positivity)

/-- Explicit c*m/log m prime-density input for the restricted-index proof. -/
theorem halfIntervalPrimes_density : ∀ᶠ m : ℕ in atTop,
    ((Real.log 4/18)*(m:ℝ))/Real.log m ≤ (halfIntervalPrimes m).card := by
  filter_upwards [halfIntervalPrimes_log_density,eventually_ge_atTop (2:ℕ)] with m hm hm2
  have hlog : 0 < Real.log (m:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  exact (div_le_iff₀ hlog).mpr hm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadicPrimes_subset_halfInterval
#print axioms KakeyaTwoScale.halfIntervalPrimes_log_density
#print axioms KakeyaTwoScale.halfIntervalPrimes_density
