module
public import KakeyaTwoScale.PolynomialBallBisection

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def SmoothCoordinateChart.translate {n : ℕ} (C : SmoothCoordinateChart n)
    (b : Fin (n+1) → ℝ) : SmoothCoordinateChart n where
  map := fun x => b+C.map x
  source := C.source
  isOpen_source := C.isOpen_source
  smooth := contDiffOn_const.add C.smooth
  injective := fun _ hx _ hy he => C.injective hx hy (add_left_cancel he)
  measurable_image := by
    change MeasurableSet (((fun x => b+x) ∘ C.map) '' C.source)
    rw [image_comp]
    exact (Homeomorph.addLeft b).measurableEmbedding.measurableSet_image.mpr C.measurable_image

/-- Translation retains every original parameter piece and every singular piece. -/
def DisjointChartAtlas.translate {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (b : Fin (n+1) → ℝ) :
    DisjointChartAtlas n ((fun x => b+x) '' Z) where
  chart := fun i => (A.chart i).translate b
  piece := A.piece
  measurable_piece := A.measurable_piece
  piece_subset := A.piece_subset
  measurable_image := by
    intro i
    change MeasurableSet (((fun x => b+x) ∘ (A.chart i).map) '' A.piece i)
    rw [image_comp]
    exact (Homeomorph.addLeft b).measurableEmbedding.measurableSet_image.mpr (A.measurable_image i)
  disjoint_image := by
    intro i j hij
    change Disjoint (((fun x => b+x) ∘ (A.chart i).map) '' A.piece i)
      (((fun x => b+x) ∘ (A.chart j).map) '' A.piece j)
    rw [image_comp,image_comp]
    exact (A.disjoint_image hij).image (Homeomorph.addLeft b).injective.injOn (subset_univ _) (subset_univ _)
  cover := by
    change (⋃ i, ((fun x => b+x) ∘ (A.chart i).map) '' A.piece i) = _
    simp_rw [image_comp]
    rw [← image_iUnion,A.cover]

theorem DisjointChartAtlas.directionalArea_translate {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (b u : Fin (n+1) → ℝ) :
    (A.translate b).directionalArea u = A.directionalArea u := by
  apply tsum_congr
  intro i
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (A.measurable_piece i)] with x hx
  have hd := (((A.chart i).smooth.differentiableOn (by simp) x (A.piece_subset i hx)).differentiableAt
    ((A.chart i).isOpen_source.mem_nhds (A.piece_subset i hx))).hasFDerivAt
  have he : fderiv ℝ (fun x => b+(A.chart i).map x) x = fderiv ℝ (A.chart i).map x := by
    exact (hd.const_add b).fderiv
  change ENNReal.ofReal |chartCofactor (fderiv ℝ (fun x => b+(A.chart i).map x) x) u| = _
  rw [he]

/-- Exact affine area transport for the same atlas, with no chart-count loss.
Applying this to a restricted atlas transports its actual localized zero set. -/
theorem DisjointChartAtlas.directionalArea_affine {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z)
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b u : Fin (n+1) → ℝ) :
    ((A.ambientMap B).translate b).directionalArea (B u) =
      ENNReal.ofReal |B.toContinuousLinearMap.det| * A.directionalArea u := by
  rw [DisjointChartAtlas.directionalArea_translate,DisjointChartAtlas.directionalArea_ambientMap]

/-- Translation preserves actual ambient volume, including nonmeasurable sets. -/
theorem volume_translate_image {N : ℕ} (b : Fin N → ℝ) (S : Set (Fin N → ℝ)) :
    volume ((fun x => b+x) '' S) = volume S := by
  have he : (fun x => b+x) '' S = (fun x => -b+x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa [add_assoc] using hy
    · intro hx
      exact ⟨-b+x,hx,by simp [← add_assoc]⟩
  rw [he,measure_preimage_add]

/-- The same determinant occurs in affine ambient volume and directional area. -/
theorem volume_affine_image {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) (S : Set (Fin N → ℝ)) :
    volume ((fun x => b+B x) '' S) = ENNReal.ofReal |B.toContinuousLinearMap.det| * volume S := by
  change volume (((fun x => b+x) ∘ B) '' S) = _
  rw [image_comp,volume_translate_image,Measure.addHaar_image_continuousLinearEquiv]
  rfl

/-- Exact transport of an actual localized area lower bound. It applies directly
to the proved unit-ball theorem, with arbitrary translation and invertible axes. -/
theorem DisjointChartAtlas.affine_area_lower_bound {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z)
    (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : Fin (n+1) → ℝ)
    (S : Set (Fin (n+1) → ℝ)) (c : ℝ≥0∞)
    (h : c*volume S ≤ ∑ j : Fin (n+1), A.directionalArea (Pi.single j 1)) :
    c*volume ((fun x => b+B x) '' S) ≤
      ∑ j : Fin (n+1), ((A.ambientMap B).translate b).directionalArea (B (Pi.single j 1)) := by
  simp_rw [DisjointChartAtlas.directionalArea_affine]
  rw [volume_affine_image,← Finset.mul_sum]
  calc
    _ = ENNReal.ofReal |B.toContinuousLinearMap.det| * (c*volume S) := by ring
    _ ≤ _ := mul_le_mul le_rfl h zero_le zero_le

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.translate
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_translate
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_affine
#print axioms KakeyaTwoScale.volume_translate_image
#print axioms KakeyaTwoScale.volume_affine_image
#print axioms KakeyaTwoScale.DisjointChartAtlas.affine_area_lower_bound
