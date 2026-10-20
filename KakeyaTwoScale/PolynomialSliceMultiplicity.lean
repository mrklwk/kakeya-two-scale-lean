module
public import KakeyaTwoScale.RegularPolynomialFibers

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale

def polynomialSlice {m : ℕ} (P Q : Fin m → MvPolynomial (Fin m) ℝ) (t : ℝ) :=
  fun j => P j + C t * Q j

theorem polynomialSlice_degree {m D : ℕ} (P Q : Fin m → MvPolynomial (Fin m) ℝ)
    (hP : ∀ j, (P j).totalDegree ≤ D) (hQ : ∀ j, (Q j).totalDegree ≤ D) (t : ℝ) :
    ∀ j, (polynomialSlice P Q t j).totalDegree ≤ D := by
  intro j
  exact (totalDegree_add _ _).trans (max_le (hP j)
    ((totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hQ j)))

theorem polynomialSlice_map {m : ℕ} (P Q : Fin m → MvPolynomial (Fin m) ℝ) (t : ℝ) :
    polynomialMapPi (polynomialSlice P Q t) =
      fun x => polynomialMapPi P x+t • polynomialMapPi Q x := by
  funext x j
  simp [polynomialSlice,polynomialMapPi]

/-- Uniform regular multiplicity of actual polynomial time slices. Singular
fibers may be infinite; no time-slice injectivity is assumed. -/
theorem polynomialSlice_regular_encard_le {m D : ℕ}
    (P Q : Fin m → MvPolynomial (Fin m) ℝ)
    (hP : ∀ j, (P j).totalDegree ≤ D) (hQ : ∀ j, (Q j).totalDegree ≤ D)
    (DF DG : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)))
    (hDF : ∀ x, HasFDerivAt (polynomialMapPi P) (DF x) x)
    (hDG : ∀ x, HasFDerivAt (polynomialMapPi Q) (DG x) x)
    (S : Set (Fin m → ℝ)) (t : ℝ) (y : Fin m → ℝ) :
    Set.encard {x | x ∈ S ∧ (DF x+t • DG x).det ≠ 0 ∧
      polynomialMapPi P x+t • polynomialMapPi Q x=y} ≤ ((4*D+1)^m : ℕ) := by
  have hd (x : Fin m → ℝ) :
      HasFDerivAt (polynomialMapPi (polynomialSlice P Q t)) (DF x+t • DG x) x := by
    rw [polynomialSlice_map]
    exact (hDF x).add ((hDG x).const_smul t)
  apply (Set.encard_mono (show {x | x ∈ S ∧ (DF x+t • DG x).det ≠ 0 ∧
      polynomialMapPi P x+t • polynomialMapPi Q x=y} ⊆
      {x | polynomialMapPi (polynomialSlice P Q t) x=y ∧
        LinearMap.det (fderiv ℝ (polynomialMapPi (polynomialSlice P Q t)) x).toLinearMap ≠ 0}
      from ?_)).trans (regular_polynomial_fiber_encard_le (polynomialSlice P Q t)
        (polynomialSlice_degree P Q hP hQ t) y)
  intro x hx
  refine ⟨?_,?_⟩
  · simpa only [polynomialSlice_map] using hx.2.2
  · rw [(hd x).fderiv]
    exact hx.2.1

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialSlice_degree
#print axioms KakeyaTwoScale.polynomialSlice_map
#print axioms KakeyaTwoScale.polynomialSlice_regular_encard_le
