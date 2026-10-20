module
public import KakeyaTwoScale.CoordinateNormalProjection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- The actual norm-preserving endomorphisms form a compact set. -/
theorem isCompact_normPreserving {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsCompact {T : E →L[ℝ] E | ∀ x, ‖T x‖=‖x‖} := by
  have hc : IsClosed {T : E →L[ℝ] E | ∀ x, ‖T x‖=‖x‖} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset hc
  intro T hT
  simp only [Metric.mem_closedBall,dist_zero_right]
  apply ContinuousLinearMap.opNorm_le_bound T (by norm_num)
  intro x
  simp only [hT x,one_mul,le_refl]

/-- Every actual norm-preserving endomorphism is an orthogonal equivalence. -/
theorem exists_equiv_of_normPreserving {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : ∀ x, ‖T x‖=‖x‖) :
    ∃ e : E ≃ₗᵢ[ℝ] E, e.toContinuousLinearEquiv.toContinuousLinearMap=T := by
  let L : E →ₗᵢ[ℝ] E := { T.toLinearMap with norm_map' := hT }
  have hs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp L.injective
  exact ⟨LinearIsometryEquiv.ofSurjective L hs,rfl⟩

/-- A finite family of orthogonal changes of coordinates places every
orthogonal frame in any prescribed open neighborhood of the identity.
The family is constructed by compactness, not supplied as a net. -/
theorem exists_finite_orthogonal_left_cover {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (score : (E →L[ℝ] E) → ℝ) (hscore : Continuous score)
    (θ : ℝ) (hid : θ < score (ContinuousLinearMap.id ℝ E)) :
    ∃ S : Finset (E ≃ₗᵢ[ℝ] E), ∀ U : E ≃ₗᵢ[ℝ] E,
      ∃ e ∈ S, θ < score (e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        U.toContinuousLinearEquiv.toContinuousLinearMap) := by
  classical
  let O := {T : E →L[ℝ] E | ∀ x, ‖T x‖=‖x‖}
  let V := fun e : E ≃ₗᵢ[ℝ] E => {T : E →L[ℝ] E |
    θ < score (e.toContinuousLinearEquiv.toContinuousLinearMap.comp T)}
  have ho : ∀ e, IsOpen (V e) := by
    intro e
    apply isOpen_lt continuous_const
    exact hscore.comp (by fun_prop)
  have hcov : O ⊆ ⋃ e, V e := by
    intro T hT
    obtain ⟨e,he⟩ := exists_equiv_of_normPreserving T hT
    apply mem_iUnion.mpr
    refine ⟨e.symm,?_⟩
    change θ < score (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp T)
    rw [← he]
    have hc : e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        e.toContinuousLinearEquiv.toContinuousLinearMap=ContinuousLinearMap.id ℝ E := by
      ext x
      exact e.symm_apply_apply x
    rwa [hc]
  obtain ⟨S,hS⟩ := isCompact_normPreserving (E := E) |>.elim_finite_subcover V ho hcov
  refine ⟨S,fun U => ?_⟩
  have hU := hS (show U.toContinuousLinearEquiv.toContinuousLinearMap ∈ O from
    fun x => U.norm_map x)
  obtain ⟨e,he,hgood⟩ := mem_iUnion₂.mp hU
  exact ⟨e,he,hgood⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.isCompact_normPreserving
#print axioms KakeyaTwoScale.exists_equiv_of_normPreserving
#print axioms KakeyaTwoScale.exists_finite_orthogonal_left_cover
