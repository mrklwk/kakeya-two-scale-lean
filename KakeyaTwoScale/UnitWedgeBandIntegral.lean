module
public import KakeyaTwoScale.WedgeBandIntegralAssembly

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Every original positive wedge band is bounded by the complete unit-wedge
sum. This uses only unit axes, not a band lower bound. -/
theorem originalWedgeBand_le_unit {n N : ℕ} (k : ℕ)
    (u : Fin N→EuclideanSpace ℝ (Fin n)) (hu : ∀i, ‖u i‖=1)
    (T : Fin N→Set (EuclideanSpace ℝ (Fin n))) (B : ℝ) (j : ℕ) (x) :
    originalWedgeBand k u T B j x≤tinyWedgeSum k u T B 1 x := by
  classical
  unfold originalWedgeBand dyadicWeightBandSum tinyWedgeSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,tupleWedgeVolume_le_one _ (fun i => hu (f i))⟩
  · intro f _ _
    exact mul_nonneg (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
      (Finset.prod_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => by norm_num) x))

/-- A translation-uniform crude integral estimate for each original band.
All integrals and cylinder volumes are actual ENNReal quantities. -/
theorem originalWedgeBand_lintegral_crude {n N k : ℕ} (hk : 0<k)
    (u : Fin N→EuclideanSpace ℝ (Fin n)) (hu : ∀i, ‖u i‖=1)
    (T : Fin N→Set (EuclideanSpace ℝ (Fin n))) (hT : ∀i, MeasurableSet (T i))
    (mu : Measure (EuclideanSpace ℝ (Fin n))) {B : ℝ} (hB : 1<B) (j : ℕ) :
    (∫⁻x, ENNReal.ofReal ((originalWedgeBand k u T B j x)^(B/((k:ℝ)*(B-1)))) ∂mu) ≤
      ENNReal.ofReal ((N:ℝ)^(B/(B-1)-1)) * ∑i, mu (T i) := by
  have hb : 0≤B/((k:ℝ)*(B-1)) := by positivity
  have hh := tinyWedgeSum_lintegral_le hk u T hT mu hB (by norm_num : (0:ℝ)≤1)
  simp only [Real.one_rpow,one_mul] at hh
  apply le_trans _ hh
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (originalWedgeBand_nonneg k u T B j x)
    (originalWedgeBand_le_unit k u hu T B j x) hb

end KakeyaTwoScale
#print axioms KakeyaTwoScale.originalWedgeBand_lintegral_crude
