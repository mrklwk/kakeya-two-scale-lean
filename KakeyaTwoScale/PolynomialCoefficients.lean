module
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A literal finite Euclidean coefficient space, with prescribed monomials. -/
def coefficientPolynomial {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (c : EuclideanSpace ℝ ι) : MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.monomial (m i) (c i)

theorem coefficientPolynomial_coeff {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (hm : Function.Injective m)
    (c : EuclideanSpace ℝ ι) (i : ι) :
    (coefficientPolynomial m c).coeff (m i)=c i := by
  simp [coefficientPolynomial,MvPolynomial.coeff_monomial,hm.eq_iff]

theorem coefficientPolynomial_nonzero {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (hm : Function.Injective m)
    (c : EuclideanSpace ℝ ι) (hc : c≠0) : coefficientPolynomial m c≠0 := by
  intro hp
  apply hc
  ext i
  have h := coefficientPolynomial_coeff m hm c i
  rw [hp] at h
  simpa using h.symm

theorem coefficientPolynomial_neg {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (c : EuclideanSpace ℝ ι) :
    coefficientPolynomial m (-c) = -coefficientPolynomial m c := by
  simp [coefficientPolynomial,← Finset.sum_neg_distrib]

theorem coefficientPolynomial_eval_continuous {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (x : Fin n → ℝ) :
    Continuous (fun c : EuclideanSpace ℝ ι => MvPolynomial.eval x (coefficientPolynomial m c)) := by
  simp only [coefficientPolynomial,map_sum,MvPolynomial.eval_monomial]
  fun_prop

theorem coefficientPolynomial_degree {ι : Type*} [Fintype ι] {n D : ℕ}
    (m : ι → (Fin n →₀ ℕ)) (hm : ∀ i, (m i).sum (fun _ e => e)≤D)
    (c : EuclideanSpace ℝ ι) : (coefficientPolynomial m c).totalDegree≤D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_monomial_le (m i) (c i)).trans (hm i)

/-- A monomial box has exactly (D+1)^n coefficients and degree at most n*D.
This supplies quantitative coefficient counts without a binomial dimension formula. -/
def boxMonomial (n D : ℕ) (j : Fin n → Fin (D+1)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (j i).val)

theorem boxMonomial_injective (n D : ℕ) : Function.Injective (boxMonomial n D) := by
  intro j k h
  funext i
  apply Fin.ext
  exact congrArg (fun f : Fin n →₀ ℕ => f i) h

theorem boxMonomial_degree (n D : ℕ) (j : Fin n → Fin (D+1)) :
    (boxMonomial n D j).sum (fun _ e => e) ≤ n*D := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ _i : Fin n, D := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (j i).isLt)
    _ = _ := by simp

theorem boxCoefficient_count (n D : ℕ) :
    Fintype.card (Fin n → Fin (D+1)) = (D+1)^n := by simp

theorem boxCoefficientPolynomial_degree (n D : ℕ)
    (c : EuclideanSpace ℝ (Fin n → Fin (D+1))) :
    (coefficientPolynomial (boxMonomial n D) c).totalDegree≤n*D :=
  coefficientPolynomial_degree _ (boxMonomial_degree n D) c

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coefficientPolynomial_nonzero
#print axioms KakeyaTwoScale.coefficientPolynomial_neg
#print axioms KakeyaTwoScale.coefficientPolynomial_eval_continuous
#print axioms KakeyaTwoScale.coefficientPolynomial_degree

#print axioms KakeyaTwoScale.boxMonomial_injective
#print axioms KakeyaTwoScale.boxCoefficient_count
#print axioms KakeyaTwoScale.boxCoefficientPolynomial_degree
