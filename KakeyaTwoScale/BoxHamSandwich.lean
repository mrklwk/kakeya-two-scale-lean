module
public import KakeyaTwoScale.ScalarOddSphere

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Higher-dimensional odd-sphere interface, with sphere dimension `(D+1)^n-1`.
`OddSphereZero.lean` proves it whenever the output dimension is smaller than
the coefficient dimension. -/
def BoxOddSphereZero (n D M : ℕ) : Prop :=
  ∀ f : CoefficientSphere (Fin n → Fin (D+1)) → EuclideanSpace ℝ (Fin M),
    Continuous f → (∀ c, f (coefficientAntipode c) = -f c) → ∃ c, f c = 0

/-- The exact topological input suffices for finite simultaneous bisection.
Applications must establish it; this theorem does not prove Borsuk–Ulam. -/
theorem box_bisection_of_oddSphereZero (n D : ℕ) {κ : Type*} [Fintype κ]
    (hzero : BoxOddSphereZero n D (Fintype.card κ))
    (w : κ → EuclideanSpace ℝ (Fin n) → ℝ) (hw : ∀ j, Integrable (w j)) :
    ∃ p : MvPolynomial (Fin n) ℝ, p≠0 ∧ p.totalDegree≤n*D ∧ ∀ j,
      (∫ x in {x : EuclideanSpace ℝ (Fin n) | 0<MvPolynomial.eval (fun i => x i) p}, w j x)=
        (∫ x, w j x)/2 ∧
      (∫ x in {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) p<0}, w j x)=
        (∫ x, w j x)/2 := by
  let e := Fintype.equivFin κ
  let v := fun j => w (e.symm j)
  obtain ⟨c,hc⟩ := hzero (polynomialMassVector (boxMonomial n D) v)
    (continuous_polynomialMassVector _ (boxMonomial_injective n D) v (fun j => hw _))
    (polynomialMassVector_odd _ v)
  obtain ⟨p,hp,hd,hb⟩ := box_massVector_zero_bisects n D (Fintype.card κ) v
    (fun j => hw _) c hc
  refine ⟨p,hp,hd,fun j => ?_⟩
  simpa [v] using hb (e j)

/-- The one-output instance is proved from IVT, when there are at least
two coefficients. General output dimensions are supplied in `OddSphereZero.lean`. -/
theorem boxOddSphereZero_one (n D : ℕ) (hd : 1 < (D+1)^n) :
    BoxOddSphereZero n D 1 := by
  intro f hf ho
  obtain ⟨c,hc⟩ := scalar_odd_sphere_zero (by simpa using hd)
    (fun c => f c 0) (by fun_prop) (fun c => by simpa using congrArg (fun v => v 0) (ho c))
  refine ⟨c,?_⟩
  ext j
  fin_cases j
  exact hc

end KakeyaTwoScale
#print axioms KakeyaTwoScale.box_bisection_of_oddSphereZero
#print axioms KakeyaTwoScale.boxOddSphereZero_one
