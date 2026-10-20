module
public import KakeyaTwoScale.NestedGrid
public import KakeyaTwoScale.WeightedBrushCounting
public import KakeyaTwoScale.PortionPruning

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

variable {P X : Type*}

def fullCellParents (parents : Finset P) (tubes : P → Set (ℝ × X))
    (cell : Set X) (t : ℝ) : Finset P :=
  parents.filter fun p => cell ⊆ (fun x => (t,x)) ⁻¹' tubes p

def fullCellWeight (parents : Finset P) (tubes : P → Set (ℝ × X))
    (u : ℝ) (cell : Set X) (t : ℝ) : ℝ :=
  u * (fullCellParents parents tubes cell t).card

/-- Whole-cell coverage gives a pointwise lower bound for the ORIGINAL fixed
weighted overlap, at every point of the cell. -/
theorem fullCellWeight_le_overlap [MeasurableSpace X]
    (parents : Finset P) (tubes : P → Set (ℝ × X)) (u : ℝ) (hu : 0 ≤ u)
    (cell : Set X) (t : ℝ) {x : X} (hx : x ∈ cell) :
    fullCellWeight parents tubes u cell t ≤ weightedOverlap parents tubes (fun _ => u) (t,x) := by
  let S := fullCellParents parents tubes cell t
  have he : fullCellWeight parents tubes u cell t =
      ∑ p ∈ S, (tubes p).indicator (fun _ => u) (t,x) := by
    have hterm : ∀ p ∈ S, (tubes p).indicator (fun _ => u) (t,x) = u := by
      intro p hp
      have hpMem : (t,x) ∈ tubes p := (Finset.mem_filter.mp hp).2 hx
      exact Set.indicator_of_mem hpMem _
    rw [Finset.sum_congr rfl hterm]
    simp [fullCellWeight, S, mul_comm]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => Set.indicator_nonneg (fun _ _ => hu) _)

/-- Retaining a whole cell above threshold supplies genuine parent/high-overlap
volume. The cells and rounded parent axis are constructed, not postulated. -/
theorem rounded_parent_high_volume {n : ℕ} (parents : Finset P)
    (tubes : P → Set (ℝ × (Fin n → ℝ)))
    (hm : ∀ p ∈ parents, MeasurableSet (tubes p))
    (u M r : ℝ) (hu : 0 ≤ u) (hr : 0 < r)
    (b v : Fin n → ℝ) (p : P)
    (hp : tubes p = horizontalTube (gridRound r b) (gridRound r v) (3*r))
    (I : Set ℝ) (hI : MeasurableSet I) (hunit : I ⊆ Set.Icc 0 1)
    (hhigh : ∀ t ∈ I,
      M ≤ fullCellWeight parents tubes u (gridCell r (gridIndex r (segmentPoint b v t))) t) :
    ENNReal.ofReal r ^ n * volume I ≤
      volume (tubes p ∩ {z | M ≤ weightedOverlap parents tubes (fun _ => u) z}) := by
  let E := tubes p ∩ {z | M ≤ weightedOverlap parents tubes (fun _ => u) z}
  have hE : MeasurableSet E := by
    apply MeasurableSet.inter
    · rw [hp]; exact measurableSet_horizontalTube _ _ _
    · exact measurableSet_le measurable_const (measurable_weightedOverlap parents tubes _ hm)
  rw [Measure.volume_eq_prod]
  apply volume_lower_of_whole_cells volume volume E hE I hI
    (fun t => gridCell r (gridIndex r (segmentPoint b v t))) (ENNReal.ofReal r ^ n)
  · intro t _
    exact le_of_eq (volume_gridCell r _).symm
  · intro t ht x hx
    constructor
    · rw [hp]
      exact gridCell_inside_rounded_parent hr b v t (hunit ht) hx
    · exact (hhigh t ht).trans (fullCellWeight_le_overlap parents tubes u hu _ t hx)

/-- The final short-portion deletion makes the lower volume bound uniform in
all parents that still have an assigned active segment. -/
theorem rounded_parent_uniform_high_volume {n : ℕ} (parents : Finset P)
    (tubes : P → Set (ℝ × (Fin n → ℝ)))
    (hm : ∀ p ∈ parents, MeasurableSet (tubes p))
    (u M r eta : ℝ) (hu : 0 ≤ u) (hr : 0 < r)
    (b v : Fin n → ℝ) (p : P)
    (hp : tubes p = horizontalTube (gridRound r b) (gridRound r v) (3*r))
    (I : Set ℝ) (hI : MeasurableSet I) (hunit : I ⊆ Set.Icc 0 1)
    (heta : ENNReal.ofReal eta ≤ volume I)
    (hhigh : ∀ t ∈ I,
      M ≤ fullCellWeight parents tubes u (gridCell r (gridIndex r (segmentPoint b v t))) t) :
    ENNReal.ofReal r ^ n * ENNReal.ofReal eta ≤
      volume (tubes p ∩ {z | M ≤ weightedOverlap parents tubes (fun _ => u) z}) :=
  (mul_le_mul_right heta _).trans
    (rounded_parent_high_volume parents tubes hm u M r hu hr b v p hp I hI hunit hhigh)
end KakeyaTwoScale
#print axioms KakeyaTwoScale.fullCellWeight_le_overlap
#print axioms KakeyaTwoScale.rounded_parent_high_volume
#print axioms KakeyaTwoScale.rounded_parent_uniform_high_volume
