module
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Actual univariate restriction of an ambient polynomial to b+t*u. -/
def affineLineRestriction {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) : Polynomial ℝ :=
  P.eval₂ Polynomial.C (fun i => Polynomial.C (b i)+Polynomial.C (u i)*Polynomial.X)

 theorem affineLineRestriction_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (affineLineRestriction P b u).eval t = MvPolynomial.eval (fun i => (b+t • u) i) P := by
  change (Polynomial.evalRingHom t) (P.eval₂ Polynomial.C
    (fun i => Polynomial.C (b i)+Polynomial.C (u i)*Polynomial.X)) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by
    ext r
    simp
  rw [hc]
  congr 1
  funext i
  change (Polynomial.C (b i)+Polynomial.C (u i)*Polynomial.X).eval t = (b+t • u) i
  simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
    PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

 theorem affineLineRestriction_natDegree_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) :
    (affineLineRestriction P b u).natDegree ≤ P.totalDegree := by
  classical
  have hlin : ∀ i, (Polynomial.C (b i)+Polynomial.C (u i)*Polynomial.X).natDegree ≤ 1 := by
    intro i
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  unfold affineLineRestriction
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  apply le_trans Polynomial.natDegree_mul_le
  simp only [Polynomial.natDegree_C,zero_add]
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  apply le_trans _ (MvPolynomial.le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i hi
  exact (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (s i) (hlin i))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.affineLineRestriction_eval
#print axioms KakeyaTwoScale.affineLineRestriction_natDegree_le
