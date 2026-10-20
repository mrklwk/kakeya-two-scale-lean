module
public import KakeyaTwoScale.SegmentGeometry
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Fubini turns a uniform lower bound on horizontal section volume over
selected heights into a lower bound on genuine product volume. -/
theorem volume_lower_of_sections {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [SFinite ν]
    (E : Set (T × X)) (hE : MeasurableSet E)
    (I : Set T) (hI : MeasurableSet I) (v : ℝ≥0∞)
    (hsection : ∀ t ∈ I, v ≤ ν ((fun x => (t,x)) ⁻¹' E)) :
    v*μ I ≤ (μ.prod ν) E := by
  rw [Measure.prod_apply hE]
  calc
    v*μ I = ∫⁻ t, I.indicator (fun _ => v) t ∂μ := by
      rw [lintegral_indicator hI]
      simp
    _ ≤ _ := by
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ I
      · simpa [Set.indicator_of_mem ht] using hsection t ht
      · simp [Set.indicator_of_notMem ht]

/-- Whole cells, rather than points on axes, certify volume in a measurable
parent/high-overlap intersection. This is the paper's height-to-volume bridge. -/
theorem volume_lower_of_whole_cells {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [SFinite ν]
    (E : Set (T × X)) (hE : MeasurableSet E)
    (I : Set T) (hI : MeasurableSet I) (cells : T → Set X) (v : ℝ≥0∞)
    (hvolume : ∀ t ∈ I, v ≤ ν (cells t))
    (hcover : ∀ t ∈ I, cells t ⊆ (fun x => (t,x)) ⁻¹' E) :
    v*μ I ≤ (μ.prod ν) E := by
  apply volume_lower_of_sections μ ν E hE I hI v
  intro t ht
  exact (hvolume t ht).trans (measure_mono (hcover t ht))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X]

def horizontalTube (b v : X) (r : ℝ) : Set (ℝ × X) :=
  {p | p.1 ∈ Set.Icc (0:ℝ) 1 ∧ dist p.2 (segmentPoint b v p.1) ≤ r}

 theorem measurableSet_horizontalTube (b v : X) (r : ℝ) :
    MeasurableSet (horizontalTube b v r) := by
  have he : horizontalTube b v r =
      Prod.fst ⁻¹' Set.Icc (0:ℝ) 1 ∩
        {p : ℝ × X | dist p.2 (segmentPoint b v p.1) ≤ r} := by rfl
  rw [he]
  apply MeasurableSet.inter (measurableSet_Icc.preimage measurable_fst)
  apply measurableSet_le _ measurable_const
  exact (continuous_snd.dist (continuous_const.add (continuous_fst.smul continuous_const))).measurable

 omit [MeasurableSpace X] [BorelSpace X] in
 theorem cells_inside_parent (b v bP vP : X) (r t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hb : dist b bP ≤ r) (hv : dist v vP ≤ r)
    (cell : Set X) (hcell : ∀ x ∈ cell, dist x (segmentPoint b v t) ≤ r) :
    cell ⊆ (fun x => (t,x)) ⁻¹' horizontalTube bP vP (3*r) := by
  intro x hx
  exact ⟨ht, whole_cell_parent_containment b v bP vP r t ht hb hv cell hcell hx⟩
end KakeyaTwoScale
#print axioms KakeyaTwoScale.volume_lower_of_whole_cells
#print axioms KakeyaTwoScale.measurableSet_horizontalTube
#print axioms KakeyaTwoScale.cells_inside_parent
