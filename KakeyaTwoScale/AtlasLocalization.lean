module
public import KakeyaTwoScale.DisjointChartAtlas

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Function
noncomputable section
namespace KakeyaTwoScale

/-- Localize the actual atlas image pieces to a Borel set, keeping the same charts. -/
def DisjointChartAtlas.restrict {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (B : Set (Fin (n+1) → ℝ)) (hB : MeasurableSet B) :
    DisjointChartAtlas n (Z ∩ B) := by
  classical
  let S (i : ℕ) := A.piece i ∩ (A.chart i).map ⁻¹' B
  have hm (i : ℕ) : MeasurableSet (S i) := by
    have he : S i = A.piece i ∩ ((A.chart i).source ∩ (A.chart i).map ⁻¹' B) := by
      ext x
      exact ⟨fun hx => ⟨hx.1,A.piece_subset i hx.1,hx.2⟩, fun hx => ⟨hx.1,hx.2.2⟩⟩
    rw [he]
    exact (A.measurable_piece i).inter ((A.chart i).measurable_source_preimage hB)
  have hi (i : ℕ) : (A.chart i).map '' S i = (A.chart i).map '' A.piece i ∩ B := by
    exact image_inter_preimage _ _ _
  refine ⟨A.chart,S,hm,(fun i => inter_subset_left.trans (A.piece_subset i)),?_,?_,?_⟩
  · intro i
    rw [hi]
    exact (A.measurable_image i).inter hB
  · intro i j hij
    change Disjoint ((A.chart i).map '' S i) ((A.chart j).map '' S j)
    rw [hi,hi]
    exact (A.disjoint_image hij).mono inter_subset_left inter_subset_left
  · simp_rw [hi]
    rw [← iUnion_inter,A.cover]

theorem DisjointChartAtlas.restrict_chart {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (B : Set (Fin (n+1) → ℝ)) (hB : MeasurableSet B) (i : ℕ) :
    (A.restrict B hB).chart i = A.chart i := rfl

theorem DisjointChartAtlas.restrict_piece {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (B : Set (Fin (n+1) → ℝ)) (hB : MeasurableSet B) (i : ℕ) :
    (A.restrict B hB).piece i = A.piece i ∩ (A.chart i).map ⁻¹' B := rfl

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.restrict
