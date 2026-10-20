module
public import KakeyaTwoScale.TubeCapture
public import KakeyaTwoScale.BrushTubeOverlap

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

def tubeHighSet {d : ℕ} {J : Type*} (G : Finset J)
    (b u : J → EuclideanSpace ℝ (Fin d)) (w : J → ℝ) (r M : ℝ) :=
  {x | M ≤ weightedOverlap G (fun j => euclideanTube (b j) (u j) r) w x}

theorem measurableSet_tubeHighSet {d : ℕ} {J : Type*} (G : Finset J)
    (b u : J → EuclideanSpace ℝ (Fin d)) (w : J → ℝ) (r M : ℝ) :
    MeasurableSet (tubeHighSet G b u w r M) :=
  measurableSet_le measurable_const (measurable_weightedOverlap G _ w
    (fun j _ => (isOpen_euclideanTube (b j) (u j) r).measurableSet))

theorem weightedOverlap_mono_sets {X J : Type*} (G : Finset J)
    (A B : J → Set X) (w : J → ℝ)
    (hw : ∀ j ∈ G, 0 ≤ w j) (hs : ∀ j ∈ G, A j ⊆ B j) (x : X) :
    weightedOverlap G A w x ≤ weightedOverlap G B w x := by
  apply Finset.sum_le_sum
  intro j hj
  by_cases ha : x ∈ A j
  · simp [Set.indicator_of_mem ha,Set.indicator_of_mem (hs j hj ha)]
  · rw [Set.indicator_of_notMem ha]
    exact Set.indicator_nonneg (fun _ _ => hw j hj) x

/-- Actual tube membership at p, not an axis-through-p assumption, is enough
to place the whole low-angle tube in a slightly enlarged plane neighborhood. -/
theorem euclideanTube_near_plane {d : ℕ}
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin d))) [H.HasOrthogonalProjection]
    (b u p : EuclideanSpace ℝ (Fin d)) (C r : ℝ) (hr : 0 < r)
    (hu : ‖u‖=1) (hp : p ∈ euclideanTube b u r) (ha : planeAngle H u ≤ C*r) :
    euclideanTube b u r ⊆ Metric.thickening ((C+3)*r) (affinePlane H p) := by
  obtain ⟨s,hs,hp⟩ := hp
  intro x hx
  obtain ⟨t,ht,hx⟩ := hx
  have hb : ‖normalProjection H (segmentPoint b u s-p)‖ ≤ r :=
    (Hᗮ.norm_starProjection_apply_le _).trans
      (by simpa [segmentPoint,dist_eq_norm,norm_sub_rev] using hp.le)
  exact low_angle_tube_near_plane H p b u x t s C r r ((C+3)*r)
    hu ha ht hs hb hx.le (by nlinarith)

/-- Restricting to the original finite tube union leaves the volume of each
measurable subset unchanged; used to instantiate finite-measure lemmas. -/
theorem restricted_real_eq_of_subset {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (U E : Set X) (hE : MeasurableSet E) (hs : E ⊆ U) :
    (mu.restrict U).real E=mu.real E := by
  rw [Measure.real,Measure.restrict_apply hE,Set.inter_eq_left.mpr hs]
  rfl

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurableSet_tubeHighSet
#print axioms KakeyaTwoScale.weightedOverlap_mono_sets
#print axioms KakeyaTwoScale.euclideanTube_near_plane
#print axioms KakeyaTwoScale.restricted_real_eq_of_subset
