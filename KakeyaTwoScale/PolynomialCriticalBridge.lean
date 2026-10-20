module
public import KakeyaTwoScale.PerturbedPolynomialCritical
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

open MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- The analytic derivative along a coordinate equals evaluation of the formal
partial derivative. This supplies actual differentiability before Fermat's rule. -/
theorem polynomial_coordinate_hasDerivAt {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) (i : σ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => eval (Function.update x i u) P)
      (eval (Function.update x i t) (pderiv i P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add P Q hP hQ => simpa [Pi.add_def] using hP.add hQ
  | mul_X P j hP =>
    have hX : HasDerivAt (fun u : ℝ => Function.update x i u j)
        (if j = i then 1 else 0) t := by
      by_cases hji : j = i
      · subst j
        simpa using hasDerivAt_id' t
      · simpa [Function.update_of_ne hji,hji] using hasDerivAt_const t (x j)
    by_cases hji : j = i
    · simpa [hji,pderiv_mul,add_comm,mul_comm,Pi.mul_def] using hP.mul hX
    · simpa [hji,pderiv_mul,Pi.single_apply,mul_comm,Pi.mul_def] using hP.mul hX

/-- Every ambient local maximum of an actual polynomial evaluation is a
zero of every formal partial derivative. -/
theorem polynomial_localMax_formal_critical {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : IsLocalMax (fun y => eval y P) x) :
    ∀ i, eval x (pderiv i P) = 0 := by
  intro i
  have hg : Continuous (fun t : ℝ => Function.update x i t) :=
    continuous_const.update i continuous_id
  have hx' : IsLocalMax (fun y => eval y P) (Function.update x i (x i)) := by
    simpa using hx
  have hm := hx'.comp_continuous hg.continuousAt
  have hd := polynomial_coordinate_hasDerivAt P x i (x i)
  simpa using hd.deriv.symm.trans hm.deriv_eq_zero

/-- The actual local maxima of the selected perturbation are finite, with
explicit general degree/dimension bound. Existence in each original component
is the separate compact-superlevel step, not assumed here. -/
theorem coercivePolynomialPerturbation_localMax_finite_ncard_le {n D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D) (ε : ℝ) (hε : ε ≠ 0) :
    let S := {x : Fin n → ℝ | IsLocalMax
      (fun y => eval y (coercivePolynomialPerturbation P D ε)) x}
    S.Finite ∧ S.ncard ≤ (2*D+1)^n := by
  dsimp only
  have hc := coercivePolynomialPerturbation_critical_finite_ncard_le P hP ε hε
  have hs : {x : Fin n → ℝ | IsLocalMax
      (fun y => eval y (coercivePolynomialPerturbation P D ε)) x} ⊆
      {x : Fin n → ℝ | ∀ i, eval x (pderiv i (coercivePolynomialPerturbation P D ε)) = 0} :=
    fun x hx => polynomial_localMax_formal_critical _ x hx
  exact ⟨hc.1.subset hs, (Set.ncard_le_ncard hs hc.1).trans hc.2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_coordinate_hasDerivAt
#print axioms KakeyaTwoScale.polynomial_localMax_formal_critical
#print axioms KakeyaTwoScale.coercivePolynomialPerturbation_localMax_finite_ncard_le
