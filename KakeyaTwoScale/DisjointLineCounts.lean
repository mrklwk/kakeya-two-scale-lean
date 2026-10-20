module
public import KakeyaTwoScale.ChartIntersectionCount
public import Mathlib.MeasureTheory.Measure.Count

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Function
noncomputable section
namespace KakeyaTwoScale

/-- Exact countable additivity of line intersections for disjoint Borel image
pieces. Counting measure need not be sigma-finite. Infinite fibers are preserved. -/
theorem chartLineCount_iUnion {n : ℕ} (E : ℕ → Set (Fin (n+1) → ℝ))
    (hE : ∀ i, MeasurableSet (E i)) (hd : Pairwise (Disjoint on E))
    (y : Fin n → ℝ) :
    chartLineCount (⋃ i, E i) y = ∑' i, chartLineCount (E i) y := by
  let f : ℝ → (Fin (n+1) → ℝ) := fun t => Fin.cons t y
  have hf : Continuous f := by
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun _ => ?_) j
    · exact continuous_id
    · exact continuous_const
  have hm (i : ℕ) : MeasurableSet (f ⁻¹' E i) := (hE i).preimage hf.measurable
  have hdis : Pairwise (Disjoint on fun i => f ⁻¹' E i) := by
    intro i j hij
    exact (hd hij).preimage f
  have hh := measure_iUnion hdis hm (μ := (Measure.count : Measure ℝ))
  simp_rw [Measure.count_apply (MeasurableSet.iUnion hm), Measure.count_apply (hm _)] at hh
  have he : f ⁻¹' (⋃ i, E i) = ⋃ i, f ⁻¹' E i := preimage_iUnion
  unfold chartLineCount
  change (f ⁻¹' ⋃ i, E i).encard.toENNReal = ∑' i, (f ⁻¹' E i).encard.toENNReal
  rw [he]
  exact hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chartLineCount_iUnion
