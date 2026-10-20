module
public import KakeyaTwoScale.PolynomialGaussBarrier
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

open Matrix
noncomputable section
namespace KakeyaTwoScale

theorem normal_minor_ne_zero_of_tangent_normDet {b c : Type*}
    [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    (K : Matrix c b ℝ) (H : Matrix c c ℝ)
    (hne : (tangentProjection (coordinateNormalLinear K H) coordinateBaseProjection).toLinearMap.normDet≠0) :
    H.det≠0 := by
  let T := (tangentProjection (coordinateNormalLinear K H) coordinateBaseProjection).toLinearMap
  have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp (by
    by_contra h
    exact hne (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr h))
  intro hz
  obtain ⟨v,hv,hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  let w : EuclideanSpace ℝ (b ⊕ c) := WithLp.toLp 2 (Sum.elim (fun _ => 0) v)
  have hw : w ∈ (coordinateNormalLinear K H).ker := by
    change coordinateNormalLinear K H w=0
    apply PiLp.ext
    intro i
    simp only [coordinateNormalLinear_apply,w,Sum.elim_inl,Sum.elim_inr]
    change (K.mulVec (0 : b → ℝ)) i + H.mulVec v i=0
    rw [Matrix.mulVec_zero]
    simpa using congrArg (fun x => x i) hHv
  have hTw : T (⟨w,hw⟩ : (coordinateNormalLinear K H).ker)=T 0 := by
    apply PiLp.ext
    intro i
    simp [T,tangentProjection,w]
  have hwzero := congrArg Subtype.val (hinj hTw)
  apply hv
  funext i
  exact congrArg (fun x : EuclideanSpace ℝ (b ⊕ c) => x (Sum.inr i)) hwzero

theorem positive_tangent_normal_ratio {b c : Type*}
    [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    (K : Matrix c b ℝ) (H : Matrix c c ℝ) (t : ℝ) (ht : 0≤t)
    (htag : t < (tangentProjection (coordinateNormalLinear K H) coordinateBaseProjection).toLinearMap.normDet^2) :
    t < H.det^2/(K*K.transpose+H*H.transpose).det := by
  have hne : (tangentProjection (coordinateNormalLinear K H) coordinateBaseProjection).toLinearMap.normDet≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : 2≠0)] at htag
    exact (not_lt_of_ge ht) htag
  rwa [coordinate_tangent_projection_normDet_sq K H
    (normal_minor_ne_zero_of_tangent_normDet K H hne)] at htag

/-- The actual derivative tag implies the polynomial normal-minor ratio,
without assuming that the chosen vertical minor is invertible. -/
theorem polynomial_tangent_tag_normal_ratio {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (x : EuclideanSpace ℝ (Fin b ⊕ Fin c)) (t : ℝ) (ht : 0≤t)
    (htag : t < (tangentProjection (fderiv ℝ (rectangularPolynomialMap P) x)
      coordinateBaseProjection).toLinearMap.normDet^2) :
    t < (polynomialNormalJacobianAt P x).det^2 /
      MvPolynomial.eval x (polynomialNormalGram P) := by
  rw [rectangularPolynomialMap_fderiv_blocks] at htag
  rw [polynomialNormalGram_eval]
  exact positive_tangent_normal_ratio _ _ t ht htag

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normal_minor_ne_zero_of_tangent_normDet
#print axioms KakeyaTwoScale.positive_tangent_normal_ratio

#print axioms KakeyaTwoScale.polynomial_tangent_tag_normal_ratio
