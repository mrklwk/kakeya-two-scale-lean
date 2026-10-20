module
public import KakeyaTwoScale.FinitePolynomialInterpolation
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open scoped BigOperators MonomialOrder
open MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- The monomial box with each exponent strictly below M has M^n elements. -/
def exponentBoxEquiv (n M : ℕ) :
    {s : Fin n →₀ ℕ // ∀ i, s i < M} ≃ (Fin n → Fin M) where
  toFun s i := ⟨s.val i,s.property i⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i).val),fun i => (f i).isLt⟩
  left_inv s := by ext i; rfl
  right_inv f := by ext i; rfl

/-- Division by pure-leading-power equations leaves a polynomial in the finite
exponent box with identical values on their common zero set. -/
theorem polynomial_remainder_on_diagonal_zeros {K : Type*} [Field K] {n M : ℕ}
    (m : MonomialOrder (Fin n)) (b : Fin n → MvPolynomial (Fin n) K)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hdeg : ∀ i, m.degree (b i) = Finsupp.single i M)
    (p : MvPolynomial (Fin n) K) :
    ∃ r : MvPolynomial (Fin n) K,
      (∀ s ∈ r.support, ∀ i, s i < M) ∧
      ∀ x : Fin n → K, (∀ i, eval x (b i) = 0) → eval x r = eval x p := by
  obtain ⟨g,r,heq,_,hr⟩ := m.div hb p
  refine ⟨r,?_,?_⟩
  · intro s hs i
    have h := hr s hs i
    rw [hdeg i,Finsupp.single_le_iff] at h
    exact Nat.lt_of_not_ge h
  · intro x hx
    rw [heq,map_add]
    have hg : eval x (Finsupp.linearCombination (MvPolynomial (Fin n) K) b g) = 0 := by
      simp [Finsupp.linearCombination_apply,Finsupp.sum,hx]
    rw [hg,zero_add]

/-- Quantitative common-root counting from a diagonal leading system.
No radicality, genericity, algebraic closure or finiteness premise is needed. -/
theorem diagonal_leading_system_card_le {K ι : Type*} [Field K] [Fintype ι] {n M : ℕ}
    (m : MonomialOrder (Fin n)) (b : Fin n → MvPolynomial (Fin n) K)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hdeg : ∀ i, m.degree (b i) = Finsupp.single i M)
    (x : ι → Fin n → K) (hx : Function.Injective x)
    (hroot : ∀ j i, eval (x j) (b i) = 0) :
    Fintype.card ι ≤ M^n := by
  classical
  let B : Set (Fin n →₀ ℕ) := {s | ∀ i, s i < M}
  let e : B ≃ (Fin n → Fin M) := exponentBoxEquiv n M
  let : Fintype B := Fintype.ofEquiv (Fin n → Fin M) e.symm
  let V := restrictSupport K B
  let basisV : Module.Basis B K V := basisRestrictSupport K B
  let : Module.Finite K V := Module.Finite.of_basis basisV
  let E : V →ₗ[K] (ι → K) := LinearMap.pi fun j =>
    ((aeval (x j)).toLinearMap).comp V.subtype
  have hsurj : Function.Surjective E := by
    intro v
    obtain ⟨p,hp⟩ := finite_polynomial_interpolation x hx v
    obtain ⟨r,hr,heval⟩ := polynomial_remainder_on_diagonal_zeros m b hb hdeg p
    refine ⟨⟨r,hr⟩,?_⟩
    funext j
    change aeval (x j) r = v j
    simpa [aeval_def] using (heval (x j) (hroot j)).trans (hp j)
  have hdim := LinearMap.finrank_le_finrank_of_surjective hsurj
  have hbcard : Fintype.card B = M^n := by
    rw [Fintype.card_congr e]
    simp
  rw [Module.finrank_eq_card_basis basisV,hbcard] at hdim
  simpa using hdim

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_remainder_on_diagonal_zeros
#print axioms KakeyaTwoScale.diagonal_leading_system_card_le
