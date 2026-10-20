module
public import KakeyaTwoScale.ModelPrime
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Distinct large prime divisors have a product at most the nonzero integer.
This is the exact arithmetic counting input for exceptional frequencies. -/
theorem large_prime_divisors_power_le (J : Finset ℕ) (L n : ℕ) (hn : n ≠ 0)
    (hp : ∀ j ∈ J, j.Prime) (hL : ∀ j ∈ J, L ≤ j) (hd : ∀ j ∈ J, j ∣ n) :
    L^J.card ≤ n := by
  have hsub : J ⊆ n.primeFactors := fun j hj => (hp j hj).mem_primeFactors (hd j hj) hn
  have hdiv : (∏ j ∈ J, j) ∣ n :=
    (Finset.prod_dvd_prod_of_subset J n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)
  calc
    L^J.card = ∏ _j ∈ J, L := by simp
    _ ≤ ∏ j ∈ J, j := Finset.prod_le_prod hL
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv

/-- A strict power cutoff gives an integer bound on the number of distinct
large prime divisors. No logarithmic estimate or prime-density theorem is assumed. -/
theorem large_prime_divisors_card_le (J : Finset ℕ) (L n B : ℕ) (hL : 1 ≤ L) (hn : n ≠ 0)
    (hp : ∀ j ∈ J, j.Prime) (hsize : ∀ j ∈ J, L ≤ j) (hd : ∀ j ∈ J, j ∣ n)
    (hcut : n < L^(B+1)) : J.card ≤ B := by
  by_contra h
  have hb : B+1 ≤ J.card := by omega
  have hpow : L^(B+1) ≤ L^J.card := Nat.pow_le_pow_right hL hb
  have hbound := large_prime_divisors_power_le J L n hn hp hsize hd
  omega

end KakeyaTwoScale
#print axioms KakeyaTwoScale.large_prime_divisors_power_le
#print axioms KakeyaTwoScale.large_prime_divisors_card_le
