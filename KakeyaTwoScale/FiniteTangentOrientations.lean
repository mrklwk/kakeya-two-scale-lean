module
public import KakeyaTwoScale.FiniteOrthogonalCover

@[expose] public section

open Set Matrix
noncomputable section
namespace KakeyaTwoScale

/-- The actual isometric inclusion of the base coordinate plane. -/
def coordinateBaseInclusion (b c : ℕ) :
    EuclideanSpace ℝ (Fin b) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c) where
  toLinearMap := euclideanGraphLinear (0 : Matrix (Fin c) (Fin b) ℝ)
  norm_map' x := by
    rw [EuclideanSpace.norm_eq,EuclideanSpace.norm_eq]
    congr 1
    simp [Fintype.sum_sum_type,euclideanGraphLinear_inl,euclideanGraphLinear_inr]

@[simp] theorem coordinateBaseProjection_inclusion (b c : ℕ)
    (x : EuclideanSpace ℝ (Fin b)) :
    coordinateBaseProjection (b := Fin b) (c := Fin c) (coordinateBaseInclusion b c x)=x := by
  ext i
  rw [coordinateBaseProjection_apply]
  exact euclideanGraphLinear_inl (0 : Matrix (Fin c) (Fin b) ℝ) x i

/-- Every actual base-plane isometric embedding extends to an ambient
orthogonal equivalence. -/
theorem exists_orthogonal_extension_of_base_isometry {b c : ℕ}
    (T : EuclideanSpace ℝ (Fin b) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)) :
    ∃ U : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c),
      ∀ x, U (coordinateBaseInclusion b c x)=T x := by
  let i := coordinateBaseInclusion b c
  let L := T.comp i.equivRange.symm.toLinearIsometry
  obtain ⟨U,hU⟩ := exists_equiv_of_normPreserving L.extend.toContinuousLinearMap L.extend.norm_map
  refine ⟨U,fun x => ?_⟩
  have hx : i x ∈ i.toLinearMap.range := ⟨x,rfl⟩
  have he := L.extend_apply (⟨i x,hx⟩ : i.toLinearMap.range)
  have hL : L ⟨i x,hx⟩=T x := by
    change T (i.equivRange.symm ⟨i x,hx⟩)=T x
    congr 1
    exact i.equivRange.symm_apply_apply x
  have heval := congrArg (fun A : EuclideanSpace ℝ (Fin b ⊕ Fin c) →L[ℝ]
    EuclideanSpace ℝ (Fin b ⊕ Fin c) => A (i x)) hU
  exact heval.trans (he.trans hL)

/-- A constructed dimension-only finite orthogonal family covers every
isometrically parametrized b-plane at squared determinant threshold 7/8. -/
theorem exists_finite_tangent_frame_orientations (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      ∀ T : EuclideanSpace ℝ (Fin b) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c),
        ∃ e ∈ S, (7:ℝ)/8 <
          ((coordinateBaseProjection.comp e.toContinuousLinearEquiv.toContinuousLinearMap).comp
            T.toContinuousLinearMap).toLinearMap.normDet^2 := by
  let i := (coordinateBaseInclusion b c).toContinuousLinearMap
  let π : EuclideanSpace ℝ (Fin b ⊕ Fin c) →L[ℝ] EuclideanSpace ℝ (Fin b) :=
    coordinateBaseProjection
  let score := fun A : EuclideanSpace ℝ (Fin b ⊕ Fin c) →L[ℝ]
      EuclideanSpace ℝ (Fin b ⊕ Fin c) => ((π.comp A).comp i).det^2
  have hc : Continuous score := by
    apply Continuous.pow
    exact ContinuousLinearMap.continuous_det.comp (by fun_prop)
  have hi : π.comp i=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin b)) := by
    ext x j
    exact congrArg (fun y : EuclideanSpace ℝ (Fin b) => y j)
      (coordinateBaseProjection_inclusion b c x)
  have hid : (7:ℝ)/8 < score (ContinuousLinearMap.id ℝ _) := by
    simp only [score,ContinuousLinearMap.comp_id,hi]
    change (7:ℝ)/8 < (LinearMap.id : EuclideanSpace ℝ (Fin b) →ₗ[ℝ] _).det^2
    norm_num
  obtain ⟨S,hS⟩ := exists_finite_orthogonal_left_cover score hc ((7:ℝ)/8) hid
  refine ⟨S,fun T => ?_⟩
  obtain ⟨U,hU⟩ := exists_orthogonal_extension_of_base_isometry T
  obtain ⟨e,he,hgood⟩ := hS U
  refine ⟨e,he,?_⟩
  have hcomp : U.toContinuousLinearEquiv.toContinuousLinearMap.comp i=T.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact hU x
  change (7:ℝ)/8 < ((π.comp e.toContinuousLinearEquiv.toContinuousLinearMap).comp
    T.toContinuousLinearMap).toLinearMap.normDet^2
  rw [LinearMap.normDet_eq_abs_det,sq_abs]
  change (7:ℝ)/8 < _ at hgood
  simpa only [score,ContinuousLinearMap.comp_assoc,hcomp] using hgood

/-- The finite family depends only on the two dimensions and covers every
actual b-dimensional tangent subspace, with no supplied frame or net. -/
theorem exists_finite_tangent_plane_orientations (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin b ⊕ Fin c)),
        Module.finrank ℝ W=b → ∃ e ∈ S, (7:ℝ)/8 <
          ((coordinateBaseProjection.comp e.toContinuousLinearEquiv.toContinuousLinearMap).comp
            W.subtypeL).toLinearMap.normDet^2 := by
  obtain ⟨S,hS⟩ := exists_finite_tangent_frame_orientations b c
  refine ⟨S,fun W hW => ?_⟩
  let w : EuclideanSpace ℝ (Fin b) ≃ₗᵢ[ℝ] W :=
    ((stdOrthonormalBasis ℝ W).reindex (finCongr hW)).repr.symm
  let T := W.subtypeₗᵢ.comp w.toLinearIsometry
  obtain ⟨e,he,hgood⟩ := hS T
  refine ⟨e,he,?_⟩
  let A := (coordinateBaseProjection.comp e.toContinuousLinearEquiv.toContinuousLinearMap).comp
    W.subtypeL
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin b))=Module.finrank ℝ W := by
    simpa using hW.symm
  have hn := LinearMap.normDet_comp_of_finrank_eq w.toLinearIsometry.toLinearMap A.toLinearMap hd
  rw [w.toLinearIsometry.normDet_eq_one,mul_one] at hn
  change (7:ℝ)/8 < A.toLinearMap.normDet^2
  rw [← hn]
  exact hgood

/-- An actual orientation assignment for an arbitrary indexed collection
of tangent planes, using a single dimension-only finite family. -/
theorem exists_finite_tangent_orientation_assignment (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      ∀ {ι : Type} (W : ι → Submodule ℝ (EuclideanSpace ℝ (Fin b ⊕ Fin c))),
        (∀ i, Module.finrank ℝ (W i)=b) →
        ∃ assign : ι → (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
            EuclideanSpace ℝ (Fin b ⊕ Fin c)),
          ∀ i, assign i ∈ S ∧ (7:ℝ)/8 <
            ((coordinateBaseProjection.comp (assign i).toContinuousLinearEquiv.toContinuousLinearMap).comp
              (W i).subtypeL).toLinearMap.normDet^2 := by
  classical
  obtain ⟨S,hS⟩ := exists_finite_tangent_plane_orientations b c
  refine ⟨S,fun W hW => ?_⟩
  choose e he hdet using fun i => hS (W i) (hW i)
  exact ⟨e,fun i => ⟨he i,hdet i⟩⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_orthogonal_extension_of_base_isometry
#print axioms KakeyaTwoScale.exists_finite_tangent_frame_orientations

#print axioms KakeyaTwoScale.exists_finite_tangent_plane_orientations
#print axioms KakeyaTwoScale.exists_finite_tangent_orientation_assignment
