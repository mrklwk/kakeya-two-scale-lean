module
public import KakeyaTwoScale.HeightRescaling
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section

open Set MeasureTheory
noncomputable section
namespace KakeyaTwoScale

def translatedChartEquiv {n : ℕ} (h : Fin (n+1)) (center : EuclideanSpace ℝ (Fin (n+1))) :
    ((Fin n→ℝ) × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin (n+1)) :=
  MeasurableEquiv.prodComm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) h).symm.trans
      ((MeasurableEquiv.toLp 2 (Fin (n+1)→ℝ)).trans (MeasurableEquiv.addLeft center)))

theorem translatedChartEquiv_apply {n : ℕ} (h : Fin (n+1))
    (center : EuclideanSpace ℝ (Fin (n+1))) (z : (Fin n→ℝ) × ℝ) :
    translatedChartEquiv h center z=center+euclideanUnsplit h (z.2,z.1) := rfl

theorem translatedChartEquiv_measurePreserving {n : ℕ} (h : Fin (n+1))
    (center : EuclideanSpace ℝ (Fin (n+1))) :
    MeasurePreserving (translatedChartEquiv h center) (volume.prod volume) volume := by
  exact ((measurePreserving_add_left volume center).comp (euclideanUnsplit_measurePreserving h)).comp
    Measure.measurePreserving_swap

/-- Exact arbitrary-set outer-volume transport, including swap, coordinate
insertion, Euclidean norm convention, and translation. -/
theorem translated_chart_target_volume {n : ℕ} (h : Fin (n+1))
    (center : EuclideanSpace ℝ (Fin (n+1))) (E : Set (EuclideanSpace ℝ (Fin (n+1)))) :
    (volume.prod volume) {z : (Fin n→ℝ) × ℝ | center+euclideanUnsplit h (z.2,z.1)∈E}=volume E :=
  (translatedChartEquiv_measurePreserving h center).measure_preimage_equiv E

end KakeyaTwoScale
#print axioms KakeyaTwoScale.translated_chart_target_volume
