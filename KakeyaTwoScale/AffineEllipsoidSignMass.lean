module
public import KakeyaTwoScale.AffinePolynomialPullback
public import KakeyaTwoScale.AffineBisectionTransport

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- An open affine ellipsoid, with an invertible map and Euclidean unit ball. -/
def affineEllipsoid {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) : Set (Fin N → ℝ) :=
  (fun x => b+B x) '' coordinateEuclideanBall N 1

theorem affineEllipsoid_open {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) :
    IsOpen (affineEllipsoid B b) := by
  change IsOpen (((fun x => b+x) ∘ B) '' coordinateEuclideanBall N 1)
  rw [image_comp]
  exact (Homeomorph.addLeft b).isOpenMap _ (B.toHomeomorph.isOpenMap _ (coordinateEuclideanBall_open _ _))

theorem affine_determinant_positive {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) :
    0 < |B.toContinuousLinearMap.det| := by
  apply abs_pos.mpr
  exact B.toLinearEquiv.isUnit_det'.ne_zero

theorem affineEllipsoid_volume {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) :
    volume (affineEllipsoid B b) =
      ENNReal.ofReal |B.toContinuousLinearMap.det| * volume (coordinateEuclideanBall N 1) :=
  volume_affine_image B b _

theorem affineEllipsoid_finite {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) :
    volume (affineEllipsoid B b) < ∞ := by
  rw [affineEllipsoid_volume]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (coordinateEuclideanBall_finite _ _)

theorem affineEllipsoid_positive {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) :
    0 < volume (affineEllipsoid B b) := by
  rw [affineEllipsoid_volume]
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ENNReal.ofReal_pos.mpr (affine_determinant_positive B)).ne'
    (coordinateEuclideanBall_positive _ _ (by norm_num)).ne')

/-- Exact sign (or any scalar predicate) localization under affine substitution. -/
theorem affineEllipsoid_polynomial_set {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
    (Q : MvPolynomial (Fin N) ℝ) (p : ℝ → Prop) :
    affineEllipsoid B b ∩ {y | p (MvPolynomial.eval y Q)} =
      (fun x => b+B x) '' (coordinateEuclideanBall N 1 ∩
        {x | p (MvPolynomial.eval x (polynomialAffinePullback B b Q))}) := by
  ext y
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩
    exact ⟨x,⟨hx,by simpa only [mem_ofPred_eq,polynomialAffinePullback_eval] using hp⟩,rfl⟩
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,by simpa only [mem_ofPred_eq,polynomialAffinePullback_eval] using hp⟩

/-- Real volumes share one strictly positive finite determinant factor. This
transfers the actual sign masses without any extra density hypothesis. -/
theorem affineEllipsoid_mass_pullback {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ)
    (Q : MvPolynomial (Fin N) ℝ) (p : ℝ → Prop) (a : ℝ)
    (h : a * volume.real (affineEllipsoid B b) ≤
      volume.real (affineEllipsoid B b ∩ {y | p (MvPolynomial.eval y Q)})) :
    a * volume.real (coordinateEuclideanBall N 1) ≤
      volume.real (coordinateEuclideanBall N 1 ∩
        {x | p (MvPolynomial.eval x (polynomialAffinePullback B b Q))}) := by
  rw [affineEllipsoid_polynomial_set] at h
  change a * (volume (affineEllipsoid B b)).toReal ≤
    (volume ((fun x => b+B x) '' _)).toReal at h
  rw [affineEllipsoid_volume,volume_affine_image] at h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)] at h
  have hd := affine_determinant_positive B
  change a * (volume (coordinateEuclideanBall N 1)).toReal ≤ _
  by_contra! hn
  have hbad := mul_pos hd (sub_pos.mpr hn)
  change 0 < |B.toContinuousLinearMap.det| *
    (a * (volume (coordinateEuclideanBall N 1)).toReal -
      (volume (coordinateEuclideanBall N 1 ∩
        {x | p (MvPolynomial.eval x (polynomialAffinePullback B b Q))})).toReal) at hbad
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.affineEllipsoid_open
#print axioms KakeyaTwoScale.affine_determinant_positive
#print axioms KakeyaTwoScale.affineEllipsoid_volume
#print axioms KakeyaTwoScale.affineEllipsoid_finite
#print axioms KakeyaTwoScale.affineEllipsoid_positive
#print axioms KakeyaTwoScale.affineEllipsoid_polynomial_set
#print axioms KakeyaTwoScale.affineEllipsoid_mass_pullback
