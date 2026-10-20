module
public import KakeyaTwoScale.OrthogonalTangentTransport
public import KakeyaTwoScale.OrthogonalPolynomialTransport
public import KakeyaTwoScale.PositiveTangentNormalRatio

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- A dimension-only finite family of actual orthogonal coordinate changes
covers every regular point of every polynomial constraint system. Tags are
the exact transformed polynomial normal-minor ratios used by capture. -/
theorem exists_finite_polynomial_orientation_assignment (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      ∀ (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ),
        (∀ x : EuclideanSpace ℝ (Fin b ⊕ Fin c), rectangularPolynomialMap P x=0 →
          (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) →
        ∃ assign : {x : EuclideanSpace ℝ (Fin b ⊕ Fin c) | rectangularPolynomialMap P x=0} →
          (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)),
          ∀ z, assign z ∈ S ∧
            let Pe := fun i => polynomialLinearPullback
              (assign z).symm.toContinuousLinearEquiv.toContinuousLinearMap (P i)
            (7:ℝ)/8 < (polynomialNormalJacobianAt Pe (assign z z)).det^2 /
              MvPolynomial.eval (assign z z) (polynomialNormalGram Pe) := by
  obtain ⟨S,hS⟩ := exists_finite_kernel_orientation_assignment b c
  refine ⟨S,fun P hreg => ?_⟩
  let Z := {x : EuclideanSpace ℝ (Fin b ⊕ Fin c) | rectangularPolynomialMap P x=0}
  let A := fun z : Z => fderiv ℝ (rectangularPolynomialMap P) (z:EuclideanSpace ℝ (Fin b ⊕ Fin c))
  have hdim : ∀ z, Module.finrank ℝ (A z).ker=b := by
    intro z
    have hr := (A z).toLinearMap.finrank_range_add_finrank_ker
    change Module.finrank ℝ (A z).range + Module.finrank ℝ (A z).ker=_ at hr
    have ha : (A z).range=⊤ := hreg z z.property
    rw [ha,finrank_top] at hr
    simp only [finrank_euclideanSpace,Fintype.card_fin,Fintype.card_sum] at hr
    omega
  obtain ⟨e,he⟩ := hS A hdim
  refine ⟨e,fun z => ⟨(he z).1,?_⟩⟩
  dsimp only
  apply polynomial_tangent_tag_normal_ratio _ _ _ (by norm_num)
  rw [rectangularPolynomialMap_pullback_fderiv]
  have hez : (e z).symm ((e z) (z:EuclideanSpace ℝ (Fin b ⊕ Fin c))) = z :=
    (e z).symm_apply_apply z
  change (7:ℝ)/8 < (tangentProjection
    ((fderiv ℝ (rectangularPolynomialMap P) ((e z).symm ((e z) (z:EuclideanSpace ℝ (Fin b ⊕ Fin c))))).comp
      (e z).symm.toContinuousLinearEquiv.toContinuousLinearMap) coordinateBaseProjection).toLinearMap.normDet^2
  rw [hez]
  exact (he z).2

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_finite_polynomial_orientation_assignment
