module
public import KakeyaTwoScale.SegmentGeometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Metric
open scoped BigOperators ENNReal
namespace KakeyaTwoScale

/-- Actual Euclidean neighborhood volume controlled by a finite ball cover.
This is the geometric covering-to-volume bridge, with explicit dimensional
ball constant; it contains no arithmetic or multilinear assumption. -/
theorem neighborhood_volume_le_cover (n : ℕ) [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (centers : Finset (EuclideanSpace ℝ (Fin n))) (r : ℝ)
    (hcover : K ⊆ ⋃ c ∈ centers, ball c r) :
    volume (thickening r K) ≤
      (centers.card:ℝ≥0∞) * ENNReal.ofReal (2*r)^n *
      ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2+1)) := by
  calc
    volume (thickening r K) ≤ volume (⋃ c ∈ centers, ball c (2*r)) :=
      measure_mono (thickening_cover K centers r hcover)
    _ ≤ ∑ c ∈ centers, volume (ball c (2*r)) := measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [EuclideanSpace.volume_ball, Fintype.card_fin]
      simp [mul_assoc]

 theorem neighborhood_volume_finite_of_cover (n : ℕ) [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (centers : Finset (EuclideanSpace ℝ (Fin n))) (r : ℝ)
    (hcover : K ⊆ ⋃ c ∈ centers, ball c r) :
    volume (thickening r K) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (neighborhood_volume_le_cover n K centers r hcover)
  finiteness

 theorem neighborhood_real_volume_le_cover (n : ℕ) [NeZero n]
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (centers : Finset (EuclideanSpace ℝ (Fin n))) (r : ℝ) (hr : 0 ≤ r)
    (hcover : K ⊆ ⋃ c ∈ centers, ball c r) :
    volume.real (thickening r K) ≤
      (centers.card:ℝ) * (2*r)^n *
      (ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2+1))).toReal := by
  have h := ENNReal.toReal_mono (by finiteness)
    (neighborhood_volume_le_cover n K centers r hcover)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*r)] using h
end KakeyaTwoScale
#print axioms KakeyaTwoScale.neighborhood_volume_le_cover
#print axioms KakeyaTwoScale.neighborhood_real_volume_le_cover
