module
public import KakeyaTwoScale.VariableBrushIncidence
public import KakeyaTwoScale.ActualBrushBands
public import KakeyaTwoScale.AngularBands

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- An actual dyadic angle band of incident original tubes carries the brush
mass with its precise O(q) loss at r=2^(-q). The original high set and all
original weights are retained through the incidence construction. -/
theorem variable_brush_incident_band (n : ℕ) (R lam B L : ℝ)
    (hR : 0 ≤ R) (hlam : 0 < lam) (hB : 0 < B) (hL : 1 ≤ L) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 1 ≤ q →
      ∀ {J : Type*} (G S : Finset J), S ⊆ G →
      ∀ (b u : J → EuclideanSpace ℝ (Fin (n+1))) (ell w : J → ℝ),
      (∀ j ∈ G, 1 ≤ ell j ∧ ell j ≤ L) →
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ dyadicRadius q), w j) ≤ B) →
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))) [H.HasOrthogonalProjection]
        (p : EuclideanSpace ℝ (Fin (n+1))) (C M : ℝ), 0 ≤ M →
      (∀ j ∈ S, p ∈ euclideanTube (b j) (ell j • u j) (dyadicRadius q)) →
      (∀ j ∈ S, planeAngle H (u j) ≤ C*dyadicRadius q) →
      (∀ j ∈ S, lam*volume.real (euclideanTube (b j) (ell j • u j) (dyadicRadius q)) ≤
        volume.real (euclideanTube (b j) (ell j • u j) (dyadicRadius q) ∩ tubeHighSet G b (fun j => ell j • u j) w (dyadicRadius q) M)) →
      ∃ band < q+2, c*M*(∑ j ∈ S, w j) ≤ (q:ℝ)*
        ∑ j ∈ G.filter (fun j => (euclideanTube (b j) (ell j • u j) (dyadicRadius q) ∩
          Metric.thickening ((L*C+3)*dyadicRadius q) (affinePlane H p)).Nonempty ∧
          dyadicAngleBand q (planeAngle H (u j))=band), w j := by
  obtain ⟨c,hc,hinc⟩ := variable_brush_plane_incidence n R lam B L hR hlam hB hL
  refine ⟨c/3,by positivity,?_⟩
  intro q hq J G S hSG b u ell w hell hb hu hw hcap H instH p C M hM hp ha hcaptured
  have hi := hinc (dyadicRadius q) (Real.exp_pos _) (dyadicRadius_le_half hq)
    G S hSG b u ell w hell hb hu hw hcap H p C M hM hp ha hcaptured
  let incident := G.filter (fun j => (euclideanTube (b j) (ell j • u j) (dyadicRadius q) ∩
    Metric.thickening ((L*C+3)*dyadicRadius q) (affinePlane H p)).Nonempty)
  obtain ⟨band,hband,hmass⟩ := weighted_angular_band incident (fun j => planeAngle H (u j)) w q hq
    (fun j _ => (planeAngle_range H (u j)).2.trans (by linarith [Real.pi_lt_four]))
    (fun j hj => hw j (Finset.mem_filter.mp hj).1)
  refine ⟨band,hband,?_⟩
  have hh := hi.trans hmass
  dsimp [incident] at hh
  rw [Finset.filter_filter] at hh
  nlinarith only [hh]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.variable_brush_incident_band
