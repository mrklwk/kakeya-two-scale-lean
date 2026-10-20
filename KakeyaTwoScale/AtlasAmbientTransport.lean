module
public import KakeyaTwoScale.AtlasDirectionalSublinearity
public import KakeyaTwoScale.ChartCofactorCovariance

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Function
noncomputable section
namespace KakeyaTwoScale

def SmoothCoordinateChart.ambientMap {n : ℕ} (C : SmoothCoordinateChart n)
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) : SmoothCoordinateChart n where
  map := B ∘ C.map
  source := C.source
  isOpen_source := C.isOpen_source
  smooth := B.contDiff.comp_contDiffOn C.smooth
  injective := B.injective.injOn.comp C.injective (mapsTo_image _ _)
  measurable_image := by
    rw [image_comp]
    exact B.toHomeomorph.measurableEmbedding.measurableSet_image.mpr C.measurable_image

/-- Ambient transport keeps the SAME parameter pieces. -/
def DisjointChartAtlas.ambientMap {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z)
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) : DisjointChartAtlas n (B '' Z) where
  chart := fun i => (A.chart i).ambientMap B
  piece := A.piece
  measurable_piece := A.measurable_piece
  piece_subset := A.piece_subset
  measurable_image := by
    intro i
    change MeasurableSet ((B ∘ (A.chart i).map) '' A.piece i)
    rw [image_comp]
    exact B.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (A.measurable_image i)
  disjoint_image := by
    intro i j hij
    change Disjoint ((B ∘ (A.chart i).map) '' A.piece i) ((B ∘ (A.chart j).map) '' A.piece j)
    rw [image_comp,image_comp]
    exact (A.disjoint_image hij).image B.injective.injOn (subset_univ _) (subset_univ _)
  cover := by
    change (⋃ i, (B ∘ (A.chart i).map) '' A.piece i) = B '' Z
    simp_rw [image_comp]
    rw [← image_iUnion,A.cover]

/-- Exact directional area covariance under ambient linear equivalence.
The determinant factor is ambient; parameter pieces and parameter measure are unchanged. -/
theorem DisjointChartAtlas.directionalArea_ambientMap {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z)
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (u : Fin (n+1) → ℝ) :
    (A.ambientMap B).directionalArea (B u) =
      ENNReal.ofReal |B.toContinuousLinearMap.det| * A.directionalArea u := by
  have hi (i : ℕ) :
      (∫⁻ x in A.piece i, ENNReal.ofReal |chartCofactor (fderiv ℝ (B ∘ (A.chart i).map) x) (B u)|) =
      ENNReal.ofReal |B.toContinuousLinearMap.det| *
        ∫⁻ x in A.piece i, ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) u| := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (A.measurable_piece i)] with x hx
    have hd := (((A.chart i).smooth.differentiableOn (by simp) x (A.piece_subset i hx)).differentiableAt
      ((A.chart i).isOpen_source.mem_nhds (A.piece_subset i hx))).hasFDerivAt
    rw [(B.hasFDerivAt.comp x hd).fderiv]
    change ENNReal.ofReal |chartCofactor (B.toContinuousLinearMap.comp (fderiv ℝ (A.chart i).map x))
      (B.toContinuousLinearMap u)| = _
    rw [chartCofactor_comp, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  change (∑' i, ∫⁻ x in A.piece i,
      ENNReal.ofReal |chartCofactor (fderiv ℝ (B ∘ (A.chart i).map) x) (B u)|) = _
  simp_rw [hi]
  exact ENNReal.tsum_mul_left

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.ambientMap
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_ambientMap
