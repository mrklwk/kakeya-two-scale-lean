module
public import KakeyaTwoScale.PolynomialEuclideanJacobian
public import KakeyaTwoScale.CoordinateNormalProjection
public import KakeyaTwoScale.PolynomialDerivativeDescent

@[expose] public section

open MvPolynomial Matrix
noncomputable section
namespace KakeyaTwoScale

def polynomialBaseJacobian {b c : ℕ} (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) :
    Matrix (Fin c) (Fin b) (MvPolynomial (Fin b ⊕ Fin c) ℝ) :=
  fun i j => pderiv (Sum.inl j) (P i)

def polynomialNormalJacobian {b c : ℕ} (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) :
    Matrix (Fin c) (Fin c) (MvPolynomial (Fin b ⊕ Fin c) ℝ) :=
  fun i j => pderiv (Sum.inr j) (P i)

def polynomialBaseJacobianAt {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (x : Fin b ⊕ Fin c → ℝ) :
    Matrix (Fin c) (Fin b) ℝ := fun i j => eval x (polynomialBaseJacobian P i j)

def polynomialNormalJacobianAt {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (x : Fin b ⊕ Fin c → ℝ) :
    Matrix (Fin c) (Fin c) ℝ := fun i j => eval x (polynomialNormalJacobian P i j)

def polynomialNormalGram {b c : ℕ} (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) :
    MvPolynomial (Fin b ⊕ Fin c) ℝ :=
  let K := polynomialBaseJacobian P
  let H := polynomialNormalJacobian P
  (K*K.transpose+H*H.transpose).det

/-- Polynomial defining the actual squared-minor Gauss barrier. -/
def polynomialGaussBarrier {b c : ℕ} (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (τ : ℝ) : MvPolynomial (Fin b ⊕ Fin c) ℝ :=
  (polynomialNormalJacobian P).det^2 - C τ * polynomialNormalGram P

theorem polynomialNormalGram_eval {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (x : Fin b ⊕ Fin c → ℝ) :
    eval x (polynomialNormalGram P) =
      ((polynomialBaseJacobianAt P x) *
          (polynomialBaseJacobianAt P x).transpose +
       (polynomialNormalJacobianAt P x) *
          (polynomialNormalJacobianAt P x).transpose).det := by
  rw [polynomialNormalGram, (eval x).map_det]
  congr 1
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, polynomialBaseJacobianAt, polynomialNormalJacobianAt]

theorem polynomialGaussBarrier_eval {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (τ : ℝ) (x : Fin b ⊕ Fin c → ℝ) :
    eval x (polynomialGaussBarrier P τ) =
      (polynomialNormalJacobianAt P x).det^2 -
        τ * eval x (polynomialNormalGram P) := by
  simp only [polynomialGaussBarrier,map_sub,map_pow,map_mul,eval_C,(eval x).map_det]
  have he : (eval x).mapMatrix (polynomialNormalJacobian P) = polynomialNormalJacobianAt P x := by
    ext i j
    rfl
  rw [he]

theorem rectangularPolynomialMap_fderiv_blocks {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (x : EuclideanSpace ℝ (Fin b ⊕ Fin c)) :
    fderiv ℝ (rectangularPolynomialMap P) x = coordinateNormalLinear
      (polynomialBaseJacobianAt P x)
      (polynomialNormalJacobianAt P x) := by
  rw [rectangularPolynomialMap_fderiv]
  congr 2
  ext i j
  cases j <;> rfl

/-- Positivity of the polynomial barrier forces the actual normal minor to
be invertible and the actual tangent projection determinant above 3/4. -/
theorem positive_polynomialGaussBarrier_estimates {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (τ : ℝ) (hτ : (3:ℝ)/4 ≤ τ)
    (x : EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (hx : 0 < eval x (polynomialGaussBarrier P τ)) :
    (fderiv ℝ (rectangularPolynomialMap P) x).range = ⊤ ∧
      (3:ℝ)/4 < (tangentProjection (fderiv ℝ (rectangularPolynomialMap P) x)
        coordinateBaseProjection).toLinearMap.normDet^2 := by
  let K := polynomialBaseJacobianAt P x
  let H := polynomialNormalJacobianAt P x
  have hpos : 0 < H.det^2 - τ * (K*K.transpose+H*H.transpose).det := by
    simpa only [polynomialGaussBarrier_eval,polynomialNormalGram_eval] using hx
  have hnonneg := normalGram_det_nonneg K H
  have hH : H.det ≠ 0 := by
    intro he
    rw [he,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_sub] at hpos
    have hτ0 : 0 ≤ τ := by linarith
    nlinarith [mul_nonneg hτ0 hnonneg]
  have hgram := normalGram_det_pos K H hH
  rw [rectangularPolynomialMap_fderiv_blocks]
  refine ⟨coordinateNormalLinear_range K H hH,?_⟩
  rw [coordinate_tangent_projection_normDet_sq K H hH]
  apply (lt_div_iff₀ hgram).mpr
  have hm := mul_le_mul_of_nonneg_right hτ hgram.le
  linarith

/-- Differentiating a polynomial lowers its total-degree bound by one,
including constant and zero polynomials. -/
theorem pderiv_totalDegree_le_pred {σ : Type*} (P : MvPolynomial σ ℝ) (j : σ) :
    (pderiv j P).totalDegree ≤ P.totalDegree-1 := by
  by_cases h : P.totalDegree=0
  · rw [totalDegree_eq_zero_iff_eq_C.mp h,pderiv_C]
    simp
  · have hh := pderiv_totalDegree_lt P j h
    omega

theorem polynomialGaussBarrier_degree {b c D : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hP : ∀ i, (P i).totalDegree ≤ D) (τ : ℝ) :
    (polynomialGaussBarrier P τ).totalDegree ≤ 2*c*(D-1) := by
  have hp (i : Fin c) (j : Fin b ⊕ Fin c) :
      (pderiv j (P i)).totalDegree ≤ D-1 :=
    (pderiv_totalDegree_le_pred (P i) j).trans (Nat.sub_le_sub_right (hP i) 1)
  have hH : (polynomialNormalJacobian P).det.totalDegree ≤ c*(D-1) :=
    polynomial_matrix_det_degree _ (fun i j => hp i (Sum.inr j))
  have hG : (polynomialNormalGram P).totalDegree ≤ c*(2*(D-1)) := by
    apply polynomial_matrix_det_degree
    intro i j
    apply (totalDegree_add _ _).trans
    apply max_le
    · rw [Matrix.mul_apply]
      apply totalDegree_finsetSum_le
      intro k _
      exact (totalDegree_mul _ _).trans (by
        change (pderiv (Sum.inl k) (P i)).totalDegree +
          (pderiv (Sum.inl k) (P j)).totalDegree ≤ 2*(D-1)
        have h1 := hp i (Sum.inl k)
        have h2 := hp j (Sum.inl k)
        omega)
    · rw [Matrix.mul_apply]
      apply totalDegree_finsetSum_le
      intro k _
      exact (totalDegree_mul _ _).trans (by
        change (pderiv (Sum.inr k) (P i)).totalDegree +
          (pderiv (Sum.inr k) (P j)).totalDegree ≤ 2*(D-1)
        have h1 := hp i (Sum.inr k)
        have h2 := hp j (Sum.inr k)
        omega)
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_pow _ 2).trans
    nlinarith
  · apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C,zero_add]
    nlinarith

/-- Actual polynomial Gauss capture: all tangent inverse and differential
hypotheses are discharged by the positive squared-minor barrier. Regularity
of the selected barrier level itself is a separate relative-Sard obligation. -/
theorem whole_set_capture_of_polynomial_gauss {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (τ : ℝ) (hτ : (3:ℝ)/4 ≤ τ)
    (Q : Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (T : Set (EuclideanSpace ℝ (Fin b))) (z : EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (hz : rectangularPolynomialMap P z=0)
    (hgz : 0 ≤ eval z (polynomialGaussBarrier P τ))
    (η r : ℝ) (hnear : ∀ x ∈ Q, dist x z < η)
    (hbad : ∃ x ∈ Q, coordinateBaseProjection x ∈ Metric.thickening r T) :
    Q ⊆ Metric.thickening (η+2*(η+r))
      ({y | rectangularPolynomialMap P y=0} ∩ coordinateBaseProjection ⁻¹' T) ∨
    Q ⊆ Metric.thickening (η+2*(η+r))
      ({y | rectangularPolynomialMap P y=0} ∩ {y | eval y (polynomialGaussBarrier P τ)=0}) := by
  apply whole_set_capture_of_tangent_projection_det
    (rectangularPolynomialMap P) (rectangularPolynomialMap_contDiff P 1) 0
    coordinateBaseProjection (by exact_mod_cast coordinateBaseProjection_norm_le (b := Fin b) (c := Fin c))
    (fun y => eval y (polynomialGaussBarrier P τ))
    (finite_polynomial_eval_contDiff _ 1).continuous _ _ _ Q T z hz hgz η r hnear hbad
  · simp only [finrank_euclideanSpace, Fintype.card_fin, Fintype.card_sum]
    omega
  · intro y _ hy
    exact (positive_polynomialGaussBarrier_estimates P τ hτ y hy).1
  · intro y _ hy
    exact (positive_polynomialGaussBarrier_estimates P τ hτ y hy).2

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialNormalGram_eval
#print axioms KakeyaTwoScale.polynomialGaussBarrier_eval
#print axioms KakeyaTwoScale.rectangularPolynomialMap_fderiv_blocks
#print axioms KakeyaTwoScale.positive_polynomialGaussBarrier_estimates

#print axioms KakeyaTwoScale.pderiv_totalDegree_le_pred
#print axioms KakeyaTwoScale.polynomialGaussBarrier_degree
#print axioms KakeyaTwoScale.whole_set_capture_of_polynomial_gauss
