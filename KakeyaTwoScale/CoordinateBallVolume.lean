module
public import KakeyaTwoScale.SignMassRetention

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def coordinateEuclideanBall (N : ℕ) (r : ℝ) : Set (Fin N → ℝ) :=
  {x | (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) ∈ ball 0 r}

theorem coordinateEuclideanBall_open (N : ℕ) (r : ℝ) : IsOpen (coordinateEuclideanBall N r) :=
  isOpen_ball.preimage (PiLp.continuous_toLp 2 _)

theorem coordinateEuclideanBall_volume (N : ℕ) (r : ℝ) :
    volume (coordinateEuclideanBall N r) = volume (ball (0 : EuclideanSpace ℝ (Fin N)) r) := by
  have he : coordinateEuclideanBall N r = (WithLp.toLp 2) ⁻¹' ball (0 : EuclideanSpace ℝ (Fin N)) r := by
    ext x; simp [coordinateEuclideanBall]
  rw [he]
  exact (PiLp.volume_preserving_toLp (Fin N)).measure_preimage isOpen_ball.measurableSet.nullMeasurableSet

theorem coordinateEuclideanBall_finite (N : ℕ) (r : ℝ) : volume (coordinateEuclideanBall N r) < ∞ := by
  rw [coordinateEuclideanBall_volume]
  exact measure_ball_lt_top

theorem coordinateEuclideanBall_positive (N : ℕ) (r : ℝ) (hr : 0 < r) :
    0 < volume (coordinateEuclideanBall N r) := by
  rw [coordinateEuclideanBall_volume]
  exact pos_iff_ne_zero.mpr (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr hr))

theorem coordinateEuclideanBall_scale (N : ℕ) (r : ℝ) (hr : 0 < r) :
    volume (coordinateEuclideanBall N r) = ENNReal.ofReal (r^N)*volume (coordinateEuclideanBall N 1) := by
  rw [coordinateEuclideanBall_volume,coordinateEuclideanBall_volume,
    Measure.addHaar_ball_of_pos volume 0 hr]
  simp

theorem coordinateEuclideanBall_subset_box (N : ℕ) (r : ℝ) :
    coordinateEuclideanBall N r ⊆ univ.pi (fun _ => Ioo (-r) r) := by
  intro x hx i _
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ < r := by simpa [coordinateEuclideanBall] using hx
  have hh := (PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) i).trans_lt hx'
  simpa only [Real.norm_eq_abs,abs_lt,mem_Ioo] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateEuclideanBall_volume
#print axioms KakeyaTwoScale.coordinateEuclideanBall_finite
#print axioms KakeyaTwoScale.coordinateEuclideanBall_positive
#print axioms KakeyaTwoScale.coordinateEuclideanBall_scale
#print axioms KakeyaTwoScale.coordinateEuclideanBall_subset_box
