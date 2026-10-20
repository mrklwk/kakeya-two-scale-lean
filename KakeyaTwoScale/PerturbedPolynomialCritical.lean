module
public import KakeyaTwoScale.DiagonalPolynomialSystem
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

open MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Formal partial differentiation cannot increase total degree. -/
theorem polynomial_pderiv_totalDegree_le {K σ : Type*} [CommSemiring K]
    (P : MvPolynomial σ K) (i : σ) : (pderiv i P).totalDegree ≤ P.totalDegree := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro s hs
  have hc : P.coeff (s + Finsupp.single i 1) ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp hs
    rw [coeff_pderiv] at h
    exact left_ne_zero_of_mul h
  have h := le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  change Finsupp.degree (s + Finsupp.single i 1) ≤ P.totalDegree at h
  rw [map_add,Finsupp.degree_single] at h
  exact le_trans (Nat.le_add_right _ 1) h

/-- Negative even powers will provide compact positive superlevels. -/
def coercivePolynomialPerturbation {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (D : ℕ) (ε : ℝ) : MvPolynomial (Fin n) ℝ :=
  P^2 - C ε * (1 + ∑ i : Fin n, X i ^ (2*D+2))

theorem coercivePolynomialPerturbation_pderiv {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (D : ℕ) (ε : ℝ) (i : Fin n) :
    pderiv i (coercivePolynomialPerturbation P D ε) =
      pderiv i (P^2) - C (ε * (2*D+2 : ℕ)) * X i ^ (2*D+1) := by
  classical
  have hsum : pderiv i (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ (2*D+2)) =
      ((2*D+2 : ℕ) : MvPolynomial (Fin n) ℝ) * X i ^ (2*D+1) := by
    rw [map_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [pderiv_X_of_ne hji]
    · simp
  simp only [coercivePolynomialPerturbation,map_sub,pderiv_C_mul,map_add,pderiv_one,zero_add,hsum]
  congr 1
  rw [map_mul]
  simp only [map_natCast,mul_assoc]

/-- The complete formal critical-point set of the coercive perturbation is
finite, bounded by (2D+1)^n. This is the algebraic counting step of the general
component argument, without nonsingularity or generic ε assumptions. -/
theorem coercivePolynomialPerturbation_critical_finite_ncard_le {n D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D) (ε : ℝ) (hε : ε ≠ 0) :
    let S := {x : Fin n → ℝ | ∀ i,
      eval x (pderiv i (coercivePolynomialPerturbation P D ε)) = 0}
    S.Finite ∧ S.ncard ≤ (2*D+1)^n := by
  let c : Fin n → ℝ := fun _ => ε * (2*D+2 : ℕ)
  let r := fun i : Fin n => -pderiv i (P^2)
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    apply mul_ne_zero hε
    exact_mod_cast (show 2*D+2 ≠ 0 by omega)
  have hr : ∀ i, (r i).totalDegree < 2*D+1 := by
    intro i
    dsimp only [r]
    rw [totalDegree_neg]
    have h := (polynomial_pderiv_totalDegree_le (P^2) i).trans
      ((totalDegree_pow P 2).trans (Nat.mul_le_mul_left 2 hP))
    omega
  have h := diagonal_polynomial_system_finite_ncard_le c hc r hr
  have heq : {x : Fin n → ℝ | ∀ i,
      eval x (pderiv i (coercivePolynomialPerturbation P D ε)) = 0} =
      {x : Fin n → ℝ | ∀ i, c i * x i ^ (2*D+1) + eval x (r i) = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq,coercivePolynomialPerturbation_pderiv,map_sub,map_mul,
      map_pow,eval_C,eval_X,r,map_neg,c]
    constructor <;> intro hx i <;> have hxi := hx i <;> linarith
  dsimp only
  rw [heq]
  exact h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_pderiv_totalDegree_le
#print axioms KakeyaTwoScale.coercivePolynomialPerturbation_pderiv
#print axioms KakeyaTwoScale.coercivePolynomialPerturbation_critical_finite_ncard_le
