module
public import KakeyaTwoScale.ModularProjectionBound
public import Mathlib.NumberTheory.Bertrand

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The prime for cyclic modeling is comparable to the height count, and
all rational denominators in the fixed finite family remain invertible once
that count dominates them. Zero numerators are allowed. -/
theorem exists_model_prime (R : Finset ℚ) (N : ℕ) (hN : 0 < N)
    (hden : ∀ r ∈ R, r.den ≤ N) :
    ∃ p : ℕ, p.Prime ∧ 20*N < p ∧ p ≤ 40*N ∧
      ∀ r ∈ R, (r.den : ZMod p) ≠ 0 := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (20*N) (by omega)
  refine ⟨p,hp,hlo,by omega,?_⟩
  intro r hr hzero
  have hdvd : p ∣ r.den := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hle : p ≤ r.den := Nat.le_of_dvd r.den_pos hdvd
  have hbound := hden r hr
  omega

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_model_prime
