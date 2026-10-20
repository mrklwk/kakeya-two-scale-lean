module
public import KakeyaTwoScale.PolynomialRegularGaussCapture
public import KakeyaTwoScale.PreconnectedPolynomialCells

@[expose] public section

open Set MvPolynomial Metric
noncomputable section
namespace KakeyaTwoScale

def sumCylindricalPolynomial {b c : ℕ} (q : MvPolynomial (Fin b) ℝ) :
    MvPolynomial (Fin b ⊕ Fin c) ℝ := rename Sum.inl q

@[simp] theorem sumCylindricalPolynomial_eval {b c : ℕ}
    (q : MvPolynomial (Fin b) ℝ) (x : EuclideanSpace ℝ (Fin b ⊕ Fin c)) :
    eval x (sumCylindricalPolynomial q) = eval (coordinateBaseProjection x) q := by
  rw [sumCylindricalPolynomial,eval_rename]
  have he : x.ofLp ∘ Sum.inl = (coordinateBaseProjection x).ofLp := by
    funext i
    simp
  rw [he]

def bufferedSuccessorPolynomial {b c s : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (q : Fin s → MvPolynomial (Fin b) ℝ) (τ : ℝ) :
    Option (Fin s) → MvPolynomial (Fin b ⊕ Fin c) ℝ
  | none => polynomialGaussBarrier P τ
  | some i => sumCylindricalPolynomial (q i)

/-- Every projected wall contact is captured wholly by one actual polynomial
successor: one selected cylindrical factor or the selected Gauss barrier. -/
theorem buffered_polynomial_wall_capture {b c s : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (q : Fin s → MvPolynomial (Fin b) ℝ) (τ : ℝ) (hτ : (3:ℝ)/4 ≤ τ)
    (Q : Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (z : EuclideanSpace ℝ (Fin b ⊕ Fin c)) (η r : ℝ)
    (hz : rectangularPolynomialMap P z=0)
    (hgz : 0 ≤ eval z (polynomialGaussBarrier P τ))
    (hnear : ∀ x ∈ Q, dist x z < η)
    (hbad : ∃ x ∈ Q, coordinateBaseProjection x ∈ thickening r (polynomialFactorZeros q)) :
    ∃ i : Option (Fin s), Q ⊆ thickening (η+2*(η+r))
      ({y | rectangularPolynomialMap P y=0} ∩
        {y | eval y (bufferedSuccessorPolynomial P q τ i)=0}) := by
  obtain ⟨x,hx,hcontact⟩ := hbad
  obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hcontact
  obtain ⟨i,hi⟩ := hy
  have hc : ∃ x ∈ Q, coordinateBaseProjection x ∈ thickening r
      {y : EuclideanSpace ℝ (Fin b) | eval y (q i)=0} :=
    ⟨x,hx,mem_thickening_iff.mpr ⟨y,hi,hxy⟩⟩
  rcases whole_set_capture_of_polynomial_gauss P τ hτ Q _ z hz hgz η r hnear hc with h | h
  · refine ⟨some i,?_⟩
    simpa only [bufferedSuccessorPolynomial,sumCylindricalPolynomial_eval,preimage_ofPred_eq] using h
  · exact ⟨none,h⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sumCylindricalPolynomial_eval
#print axioms KakeyaTwoScale.buffered_polynomial_wall_capture
