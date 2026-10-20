module
public import KakeyaTwoScale.EllipsoidTranslatePacking

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual test ellipsoids inside the fixed unit ball. The center region and
all constants are independent of B, including its eccentricity and determinant. -/
theorem unit_ball_ellipsoid_packing {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (hB : ∀ x ∈ coordinateEuclideanBall N 1,
      ‖(WithLp.toLp 2 (B x) : EuclideanSpace ℝ (Fin N))‖ ≤ 1/4) :
    ∃ F : Finset (Fin N → ℝ),
      (∀ b ∈ F, ‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin N))‖ ≤ 1/4) ∧
      (↑F : Set (Fin N → ℝ)).PairwiseDisjoint (affineEllipsoid B) ∧
      (∀ b ∈ F, affineEllipsoid B b ⊆ coordinateEuclideanBall N 1) ∧
      (F.card : ℝ≥0∞) * volume (affineEllipsoid B 0) ≤ volume (coordinateEuclideanBall N 1) ∧
      volume (coordinateEuclideanBall N (1/4)) ≤
        (F.card : ℝ≥0∞) * ENNReal.ofReal ((3:ℝ)^N) * volume (affineEllipsoid B 0) := by
  let C := {x : Fin N → ℝ | ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ ≤ 1/4}
  have hC : IsCompact C := by
    have he : C = (PiLp.homeomorph 2 (fun _ : Fin N => ℝ)) ''
        closedBall (0 : EuclideanSpace ℝ (Fin N)) (1/4) := by
      ext x
      constructor
      · intro hx
        exact ⟨WithLp.toLp 2 x,by simpa only [C,mem_ofPred_eq,mem_closedBall_zero_iff] using hx,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        change ‖y‖ ≤ 1/4
        simpa only [mem_closedBall_zero_iff] using hy
    rw [he]
    exact (isCompact_closedBall _ _).image (PiLp.homeomorph 2 (fun _ : Fin N => ℝ)).continuous
  have hCU : ∀ b ∈ C, affineEllipsoid B b ⊆ coordinateEuclideanBall N 1 := by
    intro b hb y hy
    obtain ⟨x,hx,rfl⟩ := hy
    have hbx : (WithLp.toLp 2 (b+B x) : EuclideanSpace ℝ (Fin N)) =
        WithLp.toLp 2 b + WithLp.toLp 2 (B x) := rfl
    have hh := norm_add_le (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin N)) (WithLp.toLp 2 (B x))
    have hx' := hB x hx
    change ‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin N))‖ ≤ 1/4 at hb
    simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff,hbx]
    linarith
  obtain ⟨F,hF,hd,hi,hu,hl⟩ := exists_ellipsoid_translate_packing B C
    (coordinateEuclideanBall N 1) hC hCU
  refine ⟨F,fun b hb => hF hb,hd,hi,hu,le_trans (measure_mono ?_) hl⟩
  intro x hx
  exact le_of_lt (show ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ < 1/4 from by
    simpa [coordinateEuclideanBall] using hx)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.unit_ball_ellipsoid_packing
