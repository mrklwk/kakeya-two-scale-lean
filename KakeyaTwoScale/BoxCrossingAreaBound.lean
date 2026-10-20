module
public import KakeyaTwoScale.CoordinateCrossingArea

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def intervalVolume (c : ℝ) : Measure ℝ := volume.restrict (Ioo (-c) c)

instance intervalVolume_finite (c : ℝ) : IsFiniteMeasure (intervalVolume c) := by
  constructor
  simp [intervalVolume,Real.volume_Ioo]

/-- The mixed transverse coordinate measure is an actual restriction of volume. -/
theorem mixed_interval_transverse_le_volume {n : ℕ} (α b : ℝ) (j : Fin (n+1)) :
    Measure.pi (fun i : Fin n => if (j.succAbove i).val < j.val then intervalVolume b else intervalVolume α) ≤ volume := by
  let S (i : Fin n) : Set ℝ := if (j.succAbove i).val < j.val then Ioo (-b) b else Ioo (-α) α
  have he : Measure.pi (fun i : Fin n => if (j.succAbove i).val < j.val then intervalVolume b else intervalVolume α) =
      (volume : Measure (Fin n → ℝ)).restrict (univ.pi S) := by
    rw [show (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => (volume : Measure ℝ)) from rfl,
      Measure.restrict_pi_pi]
    congr 1
    funext i
    dsimp [S,intervalVolume]
    split_ifs <;> rfl
  rw [he]
  exact Measure.restrict_le_self

/-- Uniform polynomial mixed-path integral bound by the actual localized
coordinate area. Its coefficient consists only of finite interval masses. -/
theorem polynomial_box_crossing_area_bound {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0})
    (α b : ℝ) (j : Fin (n+1)) :
    (∫⁻ z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ),
      ballCoordinateCount (fun v => MvPolynomial.eval v.ofLp P) j
        (coordinateHybrid (WithLp.toLp 2 z.1) (WithLp.toLp 2 z.2) j.val)
      ∂((Measure.pi (fun _ => intervalVolume α)).prod (Measure.pi (fun _ => intervalVolume b)))) ≤
      ((Measure.pi (fun i : Fin (n+1) => if i.val < j.val then intervalVolume α else intervalVolume b)) univ * intervalVolume α univ) *
      (A.restrict {x | (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1))) ∈ ball 0 1}
        ((isOpen_ball.preimage (PiLp.continuous_toLp 2 _)).measurableSet)).directionalArea (Pi.single j 1) := by
  rw [actual_mixed_crossing_integral (fun v => MvPolynomial.eval v.ofLp P) (P.continuous_eval.comp (PiLp.continuous_ofLp 2 _))]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  calc
    _ ≤ ∫⁻ v, transverseBallCount (fun x => MvPolynomial.eval x.ofLp P) j v :=
      lintegral_mono' (mixed_interval_transverse_le_volume α b j) le_rfl
    _ = _ := transverseBallCount_area P A j

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mixed_interval_transverse_le_volume
#print axioms KakeyaTwoScale.polynomial_box_crossing_area_bound
