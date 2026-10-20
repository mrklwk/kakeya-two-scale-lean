module
public import KakeyaTwoScale.VariableBrushGeometry
public import KakeyaTwoScale.VariableTubeVolume

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The first geometric stage of the source weighted brush, with actual
capsules and the original weighted high set, for exact lengths in [1,L]. Capture, weighted overlap,
volume caps, localization and finite-measure reduction are all proved here. -/
theorem variable_brush_plane_incidence (n : ℕ) (R lam B L : ℝ)
    (hR : 0 ≤ R) (hlam : 0 < lam) (hB : 0 < B) (hL : 1 ≤ L) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1/2 →
      ∀ {J : Type*} (G S : Finset J), S ⊆ G →
      ∀ (b u : J → EuclideanSpace ℝ (Fin (n+1))) (ell w : J → ℝ),
      (∀ j ∈ G, 1 ≤ ell j ∧ ell j ≤ L) →
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))) [H.HasOrthogonalProjection]
        (p : EuclideanSpace ℝ (Fin (n+1))) (C M : ℝ), 0 ≤ M →
      (∀ j ∈ S, p ∈ euclideanTube (b j) (ell j • u j) r) →
      (∀ j ∈ S, planeAngle H (u j) ≤ C*r) →
      (∀ j ∈ S, lam*volume.real (euclideanTube (b j) (ell j • u j) r) ≤
        volume.real (euclideanTube (b j) (ell j • u j) r ∩ tubeHighSet G b (fun j => ell j • u j) w r M)) →
      c*M*(∑ j ∈ S, w j) ≤
        ∑ j ∈ G.filter (fun j => (euclideanTube (b j) (ell j • u j) r ∩
          Metric.thickening ((L*C+3)*r) (affinePlane H p)).Nonempty), w j := by
  obtain ⟨delta,c0,hd,hc0,hcapture⟩ := variable_tube_retained_capture n R lam hR hlam
  obtain ⟨N,hN⟩ := variable_euclidean_brush_overlap (n+1) delta hd
  let D : ℝ := 2*B*(N+1:ℝ)
  let V : ℝ := 3*L*(2*(n+3:ℝ))^n
  have hD : 0 < D := by dsimp [D]; positivity
  have hLpos : 0 < L := by linarith
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨c0/(D*V),by positivity,?_⟩
  intro r hr hrone J G S hSG b u ell w hell hb hu hw hcap H instH p C M hM hp ha hcaptured
  let T := fun j => euclideanTube (b j) (ell j • u j) r
  let E := tubeHighSet G b (fun j => ell j • u j) w r M
  let pieces := fun j => (T j ∩ E) \ Metric.ball p delta
  let U := ⋃ j ∈ G, T j
  let P := Metric.thickening ((L*C+3)*r) (affinePlane H p)
  let mu : Measure (EuclideanSpace ℝ (Fin (n+1))) := volume.restrict U
  have hT : ∀ j, MeasurableSet (T j) := fun j => (isOpen_euclideanTube (b j) (ell j • u j) r).measurableSet
  have hE : MeasurableSet E := measurableSet_tubeHighSet G b (fun j => ell j • u j) w r M
  have hpieces : ∀ j, MeasurableSet (pieces j) := fun j => ((hT j).inter hE).diff Metric.isOpen_ball.measurableSet
  have hUfinite : volume U ≠ ⊤ := euclideanTube_union_finite G b (fun j => ell j • u j) r
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr hUfinite
  have hTU : ∀ j ∈ G, T j ⊆ U := by
    intro j hj x hx
    exact Set.mem_iUnion₂.mpr ⟨j,hj,hx⟩
  have hrealT : ∀ j ∈ G, mu.real (T j)=volume.real (T j) := by
    intro j hj
    exact restricted_real_eq_of_subset volume U (T j) (hT j) (hTU j hj)
  have hrealPieces : ∀ j ∈ S, mu.real (pieces j)=volume.real (pieces j) := by
    intro j hj
    apply restricted_real_eq_of_subset volume U (pieces j) (hpieces j)
    intro x hx
    exact hTU j (hSG hj) hx.1.1
  have hvolume : ∀ j ∈ S, c0*r^n ≤ mu.real (pieces j) := by
    intro j hj
    rw [hrealPieces j hj]
    exact hcapture r (ell j) hr (hell j (hSG hj)).1 (b j) (u j) p
      (hb j (hSG hj)) (hu j (hSG hj)) E (hcaptured j hj)
  have hupper : ∀ j ∈ G, mu.real (T j) ≤ V*r^n := by
    intro j hj
    rw [hrealT j hj]
    exact variable_tube_volume_upper (b j) (u j) (ell j) L
      (by linarith [(hell j hj).1]) hL (hell j hj).2 hr hrone (hu j hj)
  have hcapS : ∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
      (∑ j ∈ S.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B := by
    intro v hv
    apply le_trans _ (hcap v hv)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨hj,hangle⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hSG hj,hangle⟩
    · intro j hj _
      exact hw j (Finset.mem_filter.mp hj).1
  have hover : ∀ x, weightedOverlap S pieces w x ≤ D := by
    intro x
    by_cases hx : delta ≤ dist x p
    · have hmono := weightedOverlap_mono_sets S pieces T w (fun j hj => hw j (hSG hj))
        (fun j _ _ hz => hz.1.1) x
      have hbound := hN S b u ell w r B hr hB.le (fun j hj => hw j (hSG hj))
        (fun j hj => hu j (hSG hj)) hcapS p x hp hx
      have hlast : 2*B*(N:ℝ) ≤ D := by dsimp [D]; nlinarith
      exact hmono.trans (hbound.trans hlast)
    · have hxball : x ∈ Metric.ball p delta := lt_of_not_ge hx
      have he : weightedOverlap S pieces w x=0 := by
        apply Finset.sum_eq_zero
        intro j hj
        apply Set.indicator_of_notMem
        intro hz
        exact hz.2 hxball
      rw [he]
      exact hD.le
  have hplane : ∀ j ∈ S, pieces j ⊆ P := by
    intro j hj x hx
    exact variable_euclideanTube_near_plane H (b j) (u j) p (ell j) L C r
      (by linarith [(hell j (hSG hj)).1]) (hell j (hSG hj)).2 hr (hu j (hSG hj)) (hp j hj) (ha j hj) hx.1.1
  have hhigh : ∀ j ∈ S, ∀ x ∈ pieces j, M ≤ weightedOverlap G T w x := by
    intro j hj x hx
    exact hx.1.2
  have hinc := brush_plane_incidence mu G S T pieces w P Metric.isOpen_thickening.measurableSet
    (c0*r^n) D M (V*r^n) (fun j _ => hT j) (fun j _ => hpieces j)
    hw (fun j hj => hw j (hSG hj)) hvolume hD.le hM hover hplane hhigh hupper
  have hcancel : M*c0*(∑ j ∈ S, w j) ≤ D*V*(∑ j ∈ G.filter (fun j => (T j ∩ P).Nonempty), w j) := by
    apply (mul_le_mul_iff_left₀ (pow_pos hr n)).mp
    convert hinc using 1 <;> ring
  change (c0/(D*V))*M*(∑ j ∈ S, w j) ≤ _
  rw [show (c0/(D*V))*M*(∑ j ∈ S, w j)=(M*c0*(∑ j ∈ S, w j))/(D*V) by ring]
  exact (div_le_iff₀ (mul_pos hD hV)).mpr (by nlinarith only [hcancel])

end KakeyaTwoScale
#print axioms KakeyaTwoScale.variable_brush_plane_incidence
