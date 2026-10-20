module
public import KakeyaTwoScale.DiagonalPolynomialRoots
public import KakeyaTwoScale.PolynomialComponents

@[expose] public section

open MvPolynomial MonomialOrder
open scoped MonomialOrder
noncomputable section
namespace KakeyaTwoScale

/-- A pure-power term dominates every strictly lower-total-degree remainder
in the degree-lexicographic order. -/
theorem diagonal_polynomial_leading_data {K : Type*} [Field K] {n M : ℕ}
    (i : Fin n) (c : K) (hc : c ≠ 0) (r : MvPolynomial (Fin n) K)
    (hr : r.totalDegree < M) :
    degLex.degree (C c * X i ^ M + r) = Finsupp.single i M ∧
      degLex.leadingCoeff (C c * X i ^ M + r) = c := by
  classical
  rw [C_mul_X_pow_eq_monomial]
  have hlt : degLex.degree r ≺[degLex]
      degLex.degree (monomial (Finsupp.single i M) c) := by
    rw [degLex.degree_monomial,ite_eq_right hc]
    rw [degLex_lt_iff,Finsupp.DegLex.lt_iff]
    left
    simpa only [ofDegLex_toDegLex,degree_degLexDegree,Finsupp.degree_single] using hr
  rw [degLex.degree_add_of_lt hlt,degLex.leadingCoeff_add_of_lt hlt]
  simp [degLex.degree_monomial,degLex.leadingCoeff_monomial,hc]

/-- A diagonal system with nonzero pure-power coefficients and arbitrary
strictly lower-total-degree remainders has at most M^n distinct solutions. -/
theorem diagonal_polynomial_system_card_le {K ι : Type*} [Field K] [Fintype ι]
    {n M : ℕ} (c : Fin n → K) (hc : ∀ i, c i ≠ 0)
    (r : Fin n → MvPolynomial (Fin n) K) (hr : ∀ i, (r i).totalDegree < M)
    (x : ι → Fin n → K) (hx : Function.Injective x)
    (hroot : ∀ j i, c i * (x j i)^M + eval (x j) (r i) = 0) :
    Fintype.card ι ≤ M^n := by
  let b := fun i => C (c i) * X i ^ M + r i
  have hd := fun i => diagonal_polynomial_leading_data i (c i) (hc i) (r i) (hr i)
  refine diagonal_leading_system_card_le degLex b ?_ ?_ x hx ?_
  · intro i
    change IsUnit (degLex.leadingCoeff (C (c i) * X i ^ M + r i))
    rw [(hd i).2]
    exact isUnit_iff_ne_zero.mpr (hc i)
  · exact fun i => (hd i).1
  · intro j i
    simpa [b] using hroot j i

/-- Actual finiteness, not just an ncard inequality, for the full common zero
set of the diagonal system. -/
theorem diagonal_polynomial_system_finite_ncard_le {K : Type*} [Field K] {n M : ℕ}
    (c : Fin n → K) (hc : ∀ i, c i ≠ 0)
    (r : Fin n → MvPolynomial (Fin n) K) (hr : ∀ i, (r i).totalDegree < M) :
    let S := {x : Fin n → K | ∀ i, c i * (x i)^M + eval x (r i) = 0}
    S.Finite ∧ S.ncard ≤ M^n := by
  dsimp only
  apply finite_ncard_le_of_finset_bound
  intro A hA
  have h := diagonal_polynomial_system_card_le c hc r hr
    (fun x : A => x.val) Subtype.val_injective (fun x i => hA x.property i)
  simpa using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.diagonal_polynomial_leading_data
#print axioms KakeyaTwoScale.diagonal_polynomial_system_card_le
#print axioms KakeyaTwoScale.diagonal_polynomial_system_finite_ncard_le
