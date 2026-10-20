module
public import KakeyaTwoScale.ScaledVisibilityTests

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def visibilityBaseline (N : ℕ) : ℝ := volume.real (coordinateEuclideanBall N 2)

theorem visibilityBaseline_pos (N : ℕ) : 0<visibilityBaseline N :=
  ENNReal.toReal_pos (coordinateEuclideanBall_positive N 2 (by norm_num)).ne'
    (coordinateEuclideanBall_finite N 2).ne

theorem coordinateVisibilityBody_baseline {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) :
    volume.real (coordinateVisibilityBody p) ≤ visibilityBaseline N := by
  apply measureReal_mono ?_ (coordinateEuclideanBall_finite N 2).ne
  intro x hx
  have hh := hx.1
  simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff]
  linarith

def visibilityBankBound (n D : ℕ) (r : ℝ) : ℝ :=
  (2*((n+1:ℕ):ℝ)^2/(1/(1+((D:ℝ≥0∞)*volume (closedBall (0:Fin n→ℝ) r)).toReal)))^2

/-- A uniform norm bound puts every actual body in the fixed bank class. -/
theorem seminorm_banked_label {N : ℕ} (hN : 0<N)
    (s : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) (hs : Continuous s)
    (C : ℝ) (hC : 0≤C) (hb : ∀ v, s v≤C*‖v‖)
    (F : Finset ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)))
    (hcover : ∀ A ∈ boundedEllipsoidClass N (1/4) ((2*(N:ℝ)^2/(1/(1+C)))^2),
      ∃ B ∈ F, ellipsoidFormComparable 2 A B) :
    ∃ B ∈ F, visibilityShapeLabel s B := by
  have hi : coordinateEuclideanBall N (1/(1+C)) ⊆ coordinateVisibilityBody s := by
    intro x hx
    apply closedBall_subset_seminormVisibilityBody s C hC hb
    exact ball_subset_closedBall hx
  obtain ⟨A,hAi,hAo,hAc⟩ := exists_banked_body_ellipsoid hN
    (coordinateVisibilityBody s) (coordinateVisibilityBody_compact s hs)
    (coordinateVisibilityBody_convex s)
    (fun x hx => (seminormVisibilityBody_neg s (WithLp.toLp 2 x)).mpr hx)
    (1/(1+C)) (by positivity) hi (fun x hx => hx.1)
  obtain ⟨B,hBF,hAB⟩ := hcover A hAc
  exact ⟨B,hBF,visibilityShapeLabel_of_comparison s A B hAi hAo hAB⟩

/-- Degree fixes the bank class before epsilon and coefficient center. -/
theorem actual_visibility_bank_label {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
    (r : ℝ) (hr : 0≤r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (F : Finset ((Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)))
    (hcover : ∀ A ∈ boundedEllipsoidClass (n+1) (1/4) (visibilityBankBound n D r),
      ∃ B ∈ F, ellipsoidFormComparable 2 A B)
    (ε : ℝ) (hε : 0<ε) (hε2 : ε<2)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ∃ B ∈ F, visibilityShapeLabel
      (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p) B := by
  apply seminorm_banked_label (by omega : 0<n+1)
    (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p) ?_
    (((D:ℝ≥0∞)*volume (closedBall (0:Fin n→ℝ) r)).toReal) ENNReal.toReal_nonneg
    (mollifiedAreaSeminorm_le m hm hdegree U hU hreg r hr hbound ε hε p) F hcover
  have hh := (continuous_mollifiedArea_joint m hm hdegree U hU hreg r hr hbound ε hε hε2).comp
    (show Continuous (fun v : EuclideanSpace ℝ (Fin (n+1)) => (p,v)) from
      continuous_const.prodMk continuous_id)
  exact hh

/-- Bad actual visibility forces the bank's fixed volume eligibility cutoff. -/
theorem visibilityShapeLabel_eligible {N : ℕ} (hN : 0<N)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (h : visibilityShapeLabel p B)
    (M : ℝ) (hM : 0≤M) (hbad : 1<M*volume.real (coordinateVisibilityBody p)) :
    1≤M*((4*(N:ℝ)^2)^N)*volume.real (affineEllipsoid B 0) := by
  have hv := ENNReal.toReal_mono (show
      ENNReal.ofReal ((4*(N:ℝ)^2)^N)*volume (affineEllipsoid B 0)≠∞ by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (affineEllipsoid_finite B 0).ne)
    (visibilityShapeLabel_volume hN p B h)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hv
  have hh := mul_le_mul_of_nonneg_left hv hM
  change M*volume.real (coordinateVisibilityBody p) ≤
    M*((4*(N:ℝ)^2)^N*volume.real (affineEllipsoid B 0)) at hh
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_visibility_bank_label
#print axioms KakeyaTwoScale.visibilityShapeLabel_eligible
