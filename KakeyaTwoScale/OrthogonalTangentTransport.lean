module
public import KakeyaTwoScale.FiniteTangentOrientations

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- Orthogonal transport identifies the actual two derivative kernels. -/
def orthogonalKernelEquiv {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (e : E ≃ₗᵢ[ℝ] E) :
    A.ker ≃ₗᵢ[ℝ] (A.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap).ker where
  toFun x := ⟨e x,by
    change A (e.symm (e (x:E)))=0
    simp⟩
  invFun x := ⟨e.symm x,x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add (x:E) (y:E)
  map_smul' r x := by
    apply Subtype.ext
    exact e.map_smul r (x:E)
  norm_map' x := e.norm_map x

/-- Exact invariance of the tangent projection determinant under the actual
orthogonal kernel identification. -/
theorem orthogonal_tangent_projection_normDet {E F V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A : E →L[ℝ] F) (e : E ≃ₗᵢ[ℝ] E) (π : E →L[ℝ] V) :
    (tangentProjection (A.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap) π).toLinearMap.normDet =
      ((π.comp e.toContinuousLinearEquiv.toContinuousLinearMap).comp A.ker.subtypeL).toLinearMap.normDet := by
  let k := orthogonalKernelEquiv A e
  let T := tangentProjection (A.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap) π
  have hh := LinearMap.normDet_comp_of_finrank_eq k.toLinearIsometry.toLinearMap T.toLinearMap
    k.toLinearEquiv.finrank_eq
  rw [k.toLinearIsometry.normDet_eq_one,mul_one] at hh
  exact hh.symm

/-- Finite orientations cover actual kernels in the transformed coordinates
used by polynomial pullback, so the determinant tag needs no metric premise. -/
theorem exists_finite_kernel_orientation_assignment (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      ∀ {ι : Type} (A : ι → EuclideanSpace ℝ (Fin b ⊕ Fin c) →L[ℝ] EuclideanSpace ℝ (Fin c)),
        (∀ i, Module.finrank ℝ (A i).ker=b) →
        ∃ assign : ι → (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
            EuclideanSpace ℝ (Fin b ⊕ Fin c)),
          ∀ i, assign i ∈ S ∧ (7:ℝ)/8 <
            (tangentProjection ((A i).comp (assign i).symm.toContinuousLinearEquiv.toContinuousLinearMap)
              coordinateBaseProjection).toLinearMap.normDet^2 := by
  obtain ⟨S,hS⟩ := exists_finite_tangent_orientation_assignment b c
  refine ⟨S,fun A hA => ?_⟩
  obtain ⟨e,he⟩ := hS (fun i => (A i).ker) hA
  refine ⟨e,fun i => ⟨(he i).1,?_⟩⟩
  rw [orthogonal_tangent_projection_normDet]
  exact (he i).2

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orthogonal_tangent_projection_normDet
#print axioms KakeyaTwoScale.exists_finite_kernel_orientation_assignment
