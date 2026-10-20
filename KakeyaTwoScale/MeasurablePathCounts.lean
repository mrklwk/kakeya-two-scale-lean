module
public import KakeyaTwoScale.CoordinatePathCounts

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

theorem continuous_coordinateLinePoint {N : ℕ} (j : Fin N) :
    Continuous (fun z : EuclideanSpace ℝ (Fin N) × ℝ => coordinateLinePoint j z.1 z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i=j
  · subst i
    simpa [Function.update] using (continuous_snd : Continuous (fun z : EuclideanSpace ℝ (Fin N) × ℝ => z.2))
  · simpa [Function.update,hi,Function.comp_def] using
      ((continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin N => ℝ)).comp continuous_fst))

theorem measurable_ballCoordinateCount {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : Continuous f) (j : Fin N) :
    Measurable (ballCoordinateCount f j) := by
  exact measurable_open_localized_fiber_count _ (hf.comp (continuous_coordinateLinePoint j))
    _ (continuous_coordinateLinePoint j) _ isOpen_ball

theorem continuous_coordinateHybrid {N : ℕ} (k : ℕ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) => coordinateHybrid z.1 z.2 k) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i.val < k
  · simpa only [hi,ite_true,Function.comp_def] using
      ((continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin N => ℝ)).comp continuous_snd))
  · simpa only [hi,ite_false,Function.comp_def] using
      ((continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin N => ℝ)).comp continuous_fst))

/-- Measurability of the actual whole-line count along the mixed path base. -/
theorem measurable_path_count {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : Continuous f) (j : Fin N) :
    Measurable (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) =>
      ballCoordinateCount f j (coordinateHybrid z.1 z.2 j.val)) :=
  (measurable_ballCoordinateCount f hf j).comp (continuous_coordinateHybrid j.val).measurable

end KakeyaTwoScale
#print axioms KakeyaTwoScale.continuous_coordinateLinePoint
#print axioms KakeyaTwoScale.measurable_ballCoordinateCount
#print axioms KakeyaTwoScale.continuous_coordinateHybrid
#print axioms KakeyaTwoScale.measurable_path_count
