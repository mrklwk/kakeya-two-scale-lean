module
public import KakeyaTwoScale.GlobalRegionGeometry
public import KakeyaTwoScale.DyadicCover

@[expose] public section

open MeasureTheory Metric Filter
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The common positive height rescaling has the same reciprocal Jacobian for
all regions, including those not expressible as height-wise grids. -/
theorem volume_chartPhysical_preimage {n : ℕ} (i : Fin (n+1)) (s : ℝ)
    {L : ℝ} (hL : 0 < L) (E : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hE : MeasurableSet E) :
    volume (chartPhysical i s L ⁻¹' E)=ENNReal.ofReal L⁻¹*volume E := by
  change volume (heightAffine s L ⁻¹' (euclideanUnsplit i ⁻¹' E)) = _
  rw [volume_heightAffine_preimage s hL _ (hE.preimage (euclideanUnsplit_measurePreserving i).measurable),
    (euclideanUnsplit_measurePreserving i).measure_preimage hE.nullMeasurableSet]

 theorem volume_euclideanChartAffine_preimage {n : ℕ} (i : Fin (n+1)) (s : ℝ)
    {L : ℝ} (hL : 0 < L) (E : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hE : MeasurableSet E) :
    volume (euclideanChartAffine i s L ⁻¹' E)=ENNReal.ofReal L⁻¹*volume E := by
  change volume (euclideanSplit i ⁻¹' (chartPhysical i s L ⁻¹' E)) = _
  have hm : Measurable (chartPhysical i s L) :=
    (euclideanUnsplit_measurePreserving i).measurable.comp (measurable_heightAffine s L)
  rw [(euclideanSplit_measurePreserving i).measure_preimage (hE.preimage hm).nullMeasurableSet,
    volume_chartPhysical_preimage i s hL E hE]

 theorem chart_region_volume_le_neighborhood {n : ℕ} (i : Fin (n+1)) (s : ℝ)
    {L : ℝ} (hL : 0 < L) (K : Set (EuclideanSpace ℝ (Fin (n+1)))) (r : ℝ)
    (E : Set (ℝ × (Fin n → ℝ)))
    (hE : E ⊆ chartPhysical i s L ⁻¹' thickening r K)
    (hfin : volume (thickening r K) ≠ ⊤) :
    volume.real E ≤ L⁻¹*volume.real (thickening r K) := by
  have hpre := volume_chartPhysical_preimage i s hL (thickening r K) isOpen_thickening.measurableSet
  have hf : volume (chartPhysical i s L ⁻¹' thickening r K) ≠ ⊤ := by rw [hpre]; finiteness
  have h := measureReal_mono hE hf
  simp only [Measure.real] at h
  rw [hpre,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le)] at h
  exact h

 theorem euclidean_region_volume_le_neighborhood {n : ℕ} (i : Fin (n+1)) (s : ℝ)
    {L : ℝ} (hL : 0 < L) (K : Set (EuclideanSpace ℝ (Fin (n+1)))) (r : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hE : E ⊆ euclideanChartAffine i s L ⁻¹' thickening r K)
    (hfin : volume (thickening r K) ≠ ⊤) :
    volume.real E ≤ L⁻¹*volume.real (thickening r K) := by
  have hpre := volume_euclideanChartAffine_preimage i s hL (thickening r K) isOpen_thickening.measurableSet
  have hf : volume (euclideanChartAffine i s L ⁻¹' thickening r K) ≠ ⊤ := by rw [hpre]; finiteness
  have h := measureReal_mono hE hf
  simp only [Measure.real] at h
  rw [hpre,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le)] at h
  exact h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.volume_chartPhysical_preimage
#print axioms KakeyaTwoScale.volume_euclideanChartAffine_preimage
#print axioms KakeyaTwoScale.chart_region_volume_le_neighborhood
#print axioms KakeyaTwoScale.euclidean_region_volume_le_neighborhood
