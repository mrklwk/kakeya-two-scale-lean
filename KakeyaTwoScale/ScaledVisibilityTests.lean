module
public import KakeyaTwoScale.CoordinateVisibilityLabels
public import KakeyaTwoScale.NormalizedBodyEllipsoid
public import KakeyaTwoScale.EllipsoidTranslatePacking

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def scaledEllipsoidMap {N : ℕ} (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (η : ℝ) (hη : 0<η) : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) :=
  (LinearEquiv.smulOfNeZero ℝ (Fin N → ℝ) η hη.ne').toContinuousLinearEquiv.trans B

@[simp] theorem scaledEllipsoidMap_apply {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (η : ℝ) (hη : 0<η) (x) :
    scaledEllipsoidMap B η hη x = η • B x := B.map_smul η x

theorem scaledEllipsoidMap_set {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (η : ℝ) (hη : 0<η) (b) :
    affineEllipsoid (scaledEllipsoidMap B η hη) b = affineCoordinateBall B b η := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨η • x,?_,by simp⟩
    have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖<1 := by
      simpa [coordinateEuclideanBall] using hx
    simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff]
    change ‖(WithLp.toLp 2 (η • x) : EuclideanSpace ℝ (Fin N))‖<η
    change ‖η • (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖<η
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hη]
    nlinarith
  · rintro ⟨x,hx,rfl⟩
    refine ⟨η⁻¹ • x,?_,?_⟩
    · have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖<η := by
        simpa [coordinateEuclideanBall] using hx
      simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff]
      change ‖η⁻¹ • (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖<1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hη)]
      exact (inv_mul_lt_iff₀ hη).mpr (by simpa using hx')
    · simp [smul_smul,hη.ne']

theorem scaledEllipsoidMap_volume {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (η : ℝ) (hη : 0<η) (b) :
    volume (affineEllipsoid (scaledEllipsoidMap B η hη) b) =
      ENNReal.ofReal (η^N)*volume (affineEllipsoid B 0) := by
  rw [scaledEllipsoidMap_set,affineCoordinateBall_volume B b η hη]

theorem bankShape_outer_bound {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : ℝ)
    (hB : B ∈ boundedEllipsoidClass N (1/4) b)
    (x : Fin N → ℝ) :
    ‖(WithLp.toLp 2 (B x) : EuclideanSpace ℝ (Fin N))‖ ≤
      2*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ := by
  have h := (hB (B x)).1
  rw [B.symm_apply_apply] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (B x) : EuclideanSpace ℝ (Fin N)),
    norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))]

theorem visibilityShapeLabel_volume {N : ℕ} (hN : 0<N)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (h : visibilityShapeLabel p B) :
    volume (coordinateVisibilityBody p) ≤
      ENNReal.ofReal ((4*(N:ℝ)^2)^N)*volume (affineEllipsoid B 0) := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hs : coordinateVisibilityBody p ⊆ affineCoordinateBall B 0 (4*(N:ℝ)^2) := by
    intro x hx
    refine ⟨B.symm x,?_,by simp⟩
    have hh := h.2 x hx
    simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff]
    change ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖<4*(N:ℝ)^2
    nlinarith [sq_pos_of_pos hNr]
  simpa [affineCoordinateBall_volume B 0 _ (by positivity : 0<4*(N:ℝ)^2)] using (measure_mono hs : volume (coordinateVisibilityBody p) ≤ volume _)

theorem visibilityShapeLabel_scaled_budget {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (h : visibilityShapeLabel p B)
    (η : ℝ) (hη : 0<η) :
    (∑ j : Fin N, p (WithLp.toLp 2 (scaledEllipsoidMap B η hη (Pi.single j 1)))) ≤
      4*(N:ℝ)*η := by
  calc
    _ ≤ ∑ _j : Fin N, η*4 := Finset.sum_le_sum (fun j _ => by
      rw [scaledEllipsoidMap_apply]
      change p (η • WithLp.toLp 2 (B (Pi.single j 1))) ≤ η*4
      rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos hη]
      exact mul_le_mul_of_nonneg_left (visibilityShapeLabel_direction p B h j) hη.le)
    _ = _ := by simp; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.scaledEllipsoidMap_volume
#print axioms KakeyaTwoScale.visibilityShapeLabel_volume
#print axioms KakeyaTwoScale.visibilityShapeLabel_scaled_budget
