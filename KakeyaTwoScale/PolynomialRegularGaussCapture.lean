module
public import KakeyaTwoScale.PolynomialGaussRegularLevel

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- One actual regular Gauss threshold works for every tagged whole-set
capture. The captured Gauss wall is transverse to the original constraints,
with a uniform polynomial degree bound and the original capture radius. -/
theorem exists_regular_polynomialGaussBarrier_whole_set_capture {b c D : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hP : ∀ i, (P i).totalDegree ≤ D)
    (hreg : ∀ x : EuclideanSpace ℝ (Fin b ⊕ Fin c),
      rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) :
    ∃ τ ∈ Ioo ((3:ℝ)/4) ((7:ℝ)/8),
      (polynomialGaussBarrier P τ).totalDegree ≤ 2*c*(D-1) ∧
      (∀ x : EuclideanSpace ℝ (Fin b ⊕ Fin c),
        rectangularPolynomialMap P x=0 → eval x (polynomialGaussBarrier P τ)=0 →
        (fderiv ℝ (fun y => (rectangularPolynomialMap P y,
          eval y (polynomialGaussBarrier P τ))) x).range=⊤) ∧
      (∀ (Q : Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
        (T : Set (EuclideanSpace ℝ (Fin b)))
        (z : EuclideanSpace ℝ (Fin b ⊕ Fin c)) (η r : ℝ),
        rectangularPolynomialMap P z=0 →
        (7:ℝ)/8 < (polynomialNormalJacobianAt P z).det^2 /
          eval z (polynomialNormalGram P) →
        (∀ x ∈ Q, dist x z < η) →
        (∃ x ∈ Q, coordinateBaseProjection x ∈ Metric.thickening r T) →
        Q ⊆ Metric.thickening (η+2*(η+r))
          ({y | rectangularPolynomialMap P y=0} ∩ coordinateBaseProjection ⁻¹' T) ∨
        Q ⊆ Metric.thickening (η+2*(η+r))
          ({y | rectangularPolynomialMap P y=0} ∩
            {y | eval y (polynomialGaussBarrier P τ)=0})) := by
  obtain ⟨τ,hτ,hdegree,htrans,htag⟩ := exists_regular_polynomialGaussBarrier P hP hreg
  refine ⟨τ,hτ,hdegree,htrans,?_⟩
  intro Q T z η r hz hratio hnear hbad
  exact whole_set_capture_of_polynomial_gauss P τ hτ.1.le Q T z hz
    (htag z hz hratio).le η r hnear hbad

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_regular_polynomialGaussBarrier_whole_set_capture
