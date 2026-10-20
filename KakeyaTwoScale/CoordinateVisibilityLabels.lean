module
public import KakeyaTwoScale.EllipsoidComparisonStability
public import KakeyaTwoScale.ActualVisibilityStability

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def coordinateVisibilityBody {N : ℕ} (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) :
    Set (Fin N → ℝ) := {x | WithLp.toLp 2 x ∈ seminormVisibilityBody p}

def visibilityShapeLabel {N : ℕ} (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) : Prop :=
  (∀ x ∈ coordinateEuclideanBall N 1, (1/2:ℝ) • B x ∈ coordinateVisibilityBody p) ∧
    ∀ x ∈ coordinateVisibilityBody p,
      ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤ 2*(N:ℝ)^2

theorem coordinateVisibilityBody_convex {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) : Convex ℝ (coordinateVisibilityBody p) :=
  (seminormVisibilityBody_convex p).linear_preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.toLinearMap

theorem coordinateVisibilityBody_compact {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) (hp : Continuous p) :
    IsCompact (coordinateVisibilityBody p) := by
  have he : coordinateVisibilityBody p =
      (PiLp.homeomorph 2 (fun _ : Fin N => ℝ)) '' seminormVisibilityBody p := by
    ext x
    constructor
    · intro hx; exact ⟨WithLp.toLp 2 x,hx,rfl⟩
    · rintro ⟨y,hy,rfl⟩; exact hy
  rw [he]
  exact (seminormVisibilityBody_compact p hp).image (PiLp.homeomorph 2 (fun _ : Fin N => ℝ)).continuous

theorem coordinateVisibilityBody_volume {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) (hp : Continuous p) :
    volume (coordinateVisibilityBody p) = volume (seminormVisibilityBody p) :=
  (PiLp.volume_preserving_toLp (Fin N)).measure_preimage
    (seminormVisibilityBody_compact p hp).measurableSet.nullMeasurableSet

/-- An actually constructed body ellipsoid transfers to a comparable bank label. -/
theorem visibilityShapeLabel_of_comparison {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (A B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (hi : affineEllipsoid A 0 ⊆ coordinateVisibilityBody p)
    (ho : ∀ x ∈ coordinateVisibilityBody p,
      ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤ (N:ℝ)^2)
    (hc : ellipsoidFormComparable 2 A B) : visibilityShapeLabel p B := by
  constructor
  · intro x hx
    have hn : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ < 1 := by
      simpa [coordinateEuclideanBall] using hx
    have hh := (hc (B x)).1
    rw [B.symm_apply_apply] at hh
    have hn' := norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))
    have hb : ‖(WithLp.toLp 2 (A.symm (B x)) : EuclideanSpace ℝ (Fin N))‖ < 2 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (A.symm (B x)) : EuclideanSpace ℝ (Fin N))]
    apply hi
    refine ⟨A.symm ((1/2:ℝ) • B x),?_,by simp⟩
    have he : (WithLp.toLp 2 (A.symm ((1/2:ℝ) • B x)) : EuclideanSpace ℝ (Fin N)) =
        (1/2:ℝ) • WithLp.toLp 2 (A.symm (B x)) := by rw [map_smul]; rfl
    simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff,he,norm_smul,
      Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    linarith
  · intro x hx
    have hax := ho x hx
    have hh := (hc x).2
    have ha := norm_nonneg (WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))
    have hb := norm_nonneg (WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))
    have hN := sq_nonneg (N:ℝ)
    nlinarith

/-- The label alone bounds actual directional seminorm values. Half-unit
coordinates keep the proof strictly inside the open comparison ellipsoid. -/
theorem visibilityShapeLabel_direction {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (h : visibilityShapeLabel p B) (i : Fin N) :
    p (WithLp.toLp 2 (B (Pi.single i 1))) ≤ 4 := by
  have he : (WithLp.toLp 2 ((1/2:ℝ) • Pi.single i (1:ℝ)) : EuclideanSpace ℝ (Fin N)) =
      EuclideanSpace.single i (1/2) := by ext j; simp [Pi.single_apply]
  have hi : (1/2:ℝ) • Pi.single i (1:ℝ) ∈ coordinateEuclideanBall N 1 := by
    simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff,he,PiLp.norm_single]
    norm_num
  have hh := (h.1 _ hi).2
  have he' : (WithLp.toLp 2 ((1/2:ℝ) • B ((1/2:ℝ) • Pi.single i (1:ℝ))) :
      EuclideanSpace ℝ (Fin N)) = (1/4:ℝ) • WithLp.toLp 2 (B (Pi.single i 1)) := by
    rw [map_smul,smul_smul]
    norm_num
  change p (WithLp.toLp 2 ((1/2:ℝ) • B ((1/2:ℝ) • Pi.single i (1:ℝ)))) ≤ 1 at hh
  rw [he',map_smul_eq_mul] at hh
  norm_num at hh
  linarith

/-- Uniform directional error makes actual labels conflict. This supplies the
geometric premise of same-color label equality directly from seminorm error. -/
theorem visibilityShapeLabel_conflict {N : ℕ}
    (p q : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (B C : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (hp : visibilityShapeLabel p B) (hq : visibilityShapeLabel q C)
    (he : ∀ v, |p v-q v| ≤ ‖v‖) :
    ellipsoidFormComparable (256*(N:ℝ)^4) B C := by
  have cross (s t : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
      (L T : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
      (hs : visibilityShapeLabel s L) (ht : visibilityShapeLabel t T)
      (herr : ∀ v, t v ≤ s v+‖v‖) (x) (hx : x ∈ affineEllipsoid L 0) :
      ‖(WithLp.toLp 2 (T.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤ 8*(N:ℝ)^2 := by
    obtain ⟨y,hy,rfl⟩ := hx
    simp only [zero_add]
    have hs' := hs.1 y hy
    have hin := visibilityBody_inner_comparison s t 1 (by norm_num)
      (fun v => by simpa using herr v)
    have hm : (1/4:ℝ) • L y ∈ coordinateVisibilityBody t := by
      have hz := hin ⟨WithLp.toLp 2 ((1/2:ℝ) • L y),hs',rfl⟩
      change (WithLp.toLp 2 ((1/4:ℝ) • L y) : EuclideanSpace ℝ (Fin N)) ∈ seminormVisibilityBody t
      convert hz using 1
      norm_num
      rw [smul_smul]
      norm_num
    have hb := ht.2 _ hm
    have he' : (WithLp.toLp 2 (T.symm ((1/4:ℝ) • L y)) : EuclideanSpace ℝ (Fin N)) =
        (1/4:ℝ) • WithLp.toLp 2 (T.symm (L y)) := by rw [map_smul]; rfl
    rw [he',norm_smul] at hb
    norm_num at hb
    linarith
  have h := ellipsoid_comparable_of_cross_bounds B C (8*(N:ℝ)^2) (by positivity)
    (cross p q B C hp hq (fun v => by have hh := (abs_le.mp (he v)).1; linarith))
    (cross q p C B hq hp (fun v => by have hh := (abs_le.mp (he v)).2; linarith))
  convert h using 1
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateVisibilityBody_convex
#print axioms KakeyaTwoScale.coordinateVisibilityBody_compact
#print axioms KakeyaTwoScale.coordinateVisibilityBody_volume
#print axioms KakeyaTwoScale.visibilityShapeLabel_of_comparison
#print axioms KakeyaTwoScale.visibilityShapeLabel_direction
#print axioms KakeyaTwoScale.visibilityShapeLabel_conflict
