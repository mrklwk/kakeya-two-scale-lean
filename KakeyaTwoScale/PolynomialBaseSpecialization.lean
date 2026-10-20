module
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Substitute the base coordinates and retain the vertical variables. -/
def polynomialBaseSpecialization {b c : ℕ}
    (P : MvPolynomial (Fin b ⊕ Fin c) ℝ) (x : Fin b → ℝ) : MvPolynomial (Fin c) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun i => MvPolynomial.C (x i)) MvPolynomial.X) P

/-- Specializing and then evaluating is evaluation at the joint base/fiber point. -/
theorem polynomialBaseSpecialization_eval {b c : ℕ}
    (P : MvPolynomial (Fin b ⊕ Fin c) ℝ) (x : Fin b → ℝ) (z : Fin c → ℝ) :
    MvPolynomial.eval z (polynomialBaseSpecialization P x)=MvPolynomial.eval (Sum.elim x z) P := by
  change (MvPolynomial.eval₂Hom (RingHom.id ℝ) z)
    (P.eval₂ MvPolynomial.C (Sum.elim (fun i => MvPolynomial.C (x i)) MvPolynomial.X)) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (MvPolynomial.eval₂Hom (RingHom.id ℝ) z).comp MvPolynomial.C=RingHom.id ℝ := by
    ext r
    simp
  rw [hc]
  congr 1
  funext i
  cases i <;> simp

/-- The total-degree bound is uniform over every base point, including fibers
where leading coefficients vanish or the entire polynomial becomes zero. -/
theorem polynomialBaseSpecialization_totalDegree_le {b c : ℕ}
    (P : MvPolynomial (Fin b ⊕ Fin c) ℝ) (x : Fin b → ℝ) :
    (polynomialBaseSpecialization P x).totalDegree ≤ P.totalDegree := by
  classical
  let f : Fin b ⊕ Fin c → MvPolynomial (Fin c) ℝ :=
    Sum.elim (fun i => MvPolynomial.C (x i)) MvPolynomial.X
  have hf (i) : (f i).totalDegree ≤ 1 := by cases i <;> simp [f]
  change (P.eval₂ MvPolynomial.C f).totalDegree ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  apply le_trans (MvPolynomial.totalDegree_mul _ _)
  simp only [MvPolynomial.totalDegree_C,zero_add]
  apply le_trans (MvPolynomial.totalDegree_finsetProd _ _)
  apply le_trans _ (MvPolynomial.le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i hi
  exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

/-- Formal vertical differentiation commutes with base specialization. -/
theorem polynomialBaseSpecialization_pderiv {b c : ℕ}
    (P : MvPolynomial (Fin b ⊕ Fin c) ℝ) (x : Fin b → ℝ) (j : Fin c) :
    polynomialBaseSpecialization (MvPolynomial.pderiv (Sum.inr j) P) x =
      MvPolynomial.pderiv j (polynomialBaseSpecialization P x) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [polynomialBaseSpecialization]
  | add P Q hP hQ => simpa [polynomialBaseSpecialization] using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    cases i with
    | inl i => simpa [polynomialBaseSpecialization,MvPolynomial.pderiv_mul] using
        congrArg (fun Q => Q * MvPolynomial.C (x i)) hP
    | inr i =>
      by_cases hi : i=j
      · subst i
        simp_all [polynomialBaseSpecialization]
      · simpa [polynomialBaseSpecialization,MvPolynomial.pderiv_mul,hi] using
          congrArg (fun Q => Q * MvPolynomial.X i) hP

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialBaseSpecialization_eval
#print axioms KakeyaTwoScale.polynomialBaseSpecialization_totalDegree_le
#print axioms KakeyaTwoScale.polynomialBaseSpecialization_pderiv
