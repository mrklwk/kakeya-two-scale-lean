module
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Nat
open scoped BigOperators

def dyadicPrimes (n : ℕ) : Finset ℕ := (Finset.Ioc n (2*n)).filter Nat.Prime

/-- The low-prime contribution in Erdős's binomial proof, without assuming
that the upper half-interval contains no primes. -/
theorem low_prime_binomial_bound (n : ℕ) (hn : 2 < n) :
    (∏ p ∈ (Finset.range (2*n/3+1)).filter Nat.Prime,
      p ^ n.centralBinom.factorization p) ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3) := by
  have npos : 0 < n := by omega
  have hbase : 1 ≤ 2*n := by omega
  let S := (Finset.range (2*n/3+1)).filter Nat.Prime
  let f p := p ^ n.centralBinom.factorization p
  change (∏ p ∈ S, f p) ≤ _
  rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2*n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod fun p _ => (?_ : f p ≤ 2*n)).trans ?_
    · exact Nat.pow_factorization_choose_le (by omega)
    rw [Finset.prod_const]
    apply Nat.pow_le_pow_right hbase
    have hc : (Finset.Icc 1 (Nat.sqrt (2*n))).card = Nat.sqrt (2*n) := by simp
    apply (Finset.card_le_card ?_).trans hc.le
    intro p hp
    obtain ⟨hs,hle⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hs).2.one_lt.le,hle⟩
  · refine le_trans ?_ (primorial_le_four_pow (2*n/3))
    refine (Finset.prod_le_prod fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨hs,hle⟩ := Finset.mem_filter.mp hp
      refine (Nat.pow_le_pow_right (Finset.mem_filter.mp hs).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hle))
    exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
      (fun p hp _ => (Finset.mem_filter.mp hp).2.one_lt.le)

/-- Quantitative replacement for the no-Bertrand-prime hypothesis: keep the
entire contribution of primes in (n,2n], bounded by their number. -/
theorem centralBinom_le_dyadic_prime_count (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3)*(2*n)^(dyadicPrimes n).card := by
  let S := (Finset.range (2*n/3+1)).filter Nat.Prime
  let J := dyadicPrimes n
  let f p := p ^ n.centralBinom.factorization p
  have hdis : Disjoint S J := by
    apply Finset.disjoint_left.mpr
    intro p hp hj
    have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hj).1).1
    have : 2*n/3 ≤ n := by omega
    omega
  have hsub : S ∪ J ⊆ Finset.range (2*n+1) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      have : 2*n/3 ≤ 2*n := Nat.div_le_self _ _
      exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2; omega)
  have he : n.centralBinom = (∏ p ∈ S, f p)*(∏ p ∈ J, f p) := by
    rw [← Finset.prod_union hdis]
    rw [← Nat.prod_pow_factorization_centralBinom n]
    symm
    apply Finset.prod_subset hsub
    intro p hp hnot
    dsimp only [f]
    by_cases hprime : p.Prime
    · have hpmax : p ≤ 2*n := by simpa using hp
      have hsmall : ¬ p ≤ 2*n/3 := by
        intro h
        apply hnot
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime⟩)
      have hpn : p ≤ n := by
        by_contra h
        apply hnot
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,hpmax⟩,hprime⟩)
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn (by omega),pow_zero]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hprime,pow_zero]
  rw [he]
  apply mul_le_mul'
  · exact low_prime_binomial_bound n hn
  · calc
      (∏ p ∈ J, f p) ≤ ∏ _p ∈ J, 2*n := Finset.prod_le_prod (fun p _ => Nat.pow_factorization_choose_le (by omega))
      _ = (2*n)^J.card := by rw [Finset.prod_const]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.low_prime_binomial_bound
#print axioms KakeyaTwoScale.centralBinom_le_dyadic_prime_count
