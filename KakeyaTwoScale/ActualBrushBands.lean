module
public import KakeyaTwoScale.ActualBrushIncidence
public import KakeyaTwoScale.AngularBands

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem dyadicRadius_le_half {q : ℕ} (hq : 1 ≤ q) : dyadicRadius q ≤ 1/2 := by
  have hr : 0 < dyadicRadius q := Real.exp_pos _
  have hp : (2:ℝ) ≤ (2:ℝ)^q := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hq
  have hh := mul_le_mul_of_nonneg_right hp hr.le
  rw [dyadicRadius_pow_cancel] at hh
  linarith

/-- An actual dyadic angle band of incident original tubes carries the brush
mass with its precise O(q) loss at r=2^(-q). The original high set and all
original weights are retained through the incidence construction. -/
theorem actual_brush_incident_band (n : ℕ) (R lam B : ℝ)
    (hR : 0 ≤ R) (hlam : 0 < lam) (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 1 ≤ q →
      ∀ {J : Type*} (G S : Finset J), S ⊆ G →
      ∀ (b u : J → EuclideanSpace ℝ (Fin (n+1))) (w : J → ℝ),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ dyadicRadius q), w j) ≤ B) →
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))) [H.HasOrthogonalProjection]
        (p : EuclideanSpace ℝ (Fin (n+1))) (C M : ℝ), 0 ≤ M →
      (∀ j ∈ S, p ∈ euclideanTube (b j) (u j) (dyadicRadius q)) →
      (∀ j ∈ S, planeAngle H (u j) ≤ C*dyadicRadius q) →
      (∀ j ∈ S, lam*volume.real (euclideanTube (b j) (u j) (dyadicRadius q)) ≤
        volume.real (euclideanTube (b j) (u j) (dyadicRadius q) ∩ tubeHighSet G b u w (dyadicRadius q) M)) →
      ∃ band < q+2, c*M*(∑ j ∈ S, w j) ≤ (q:ℝ)*
        ∑ j ∈ G.filter (fun j => (euclideanTube (b j) (u j) (dyadicRadius q) ∩
          Metric.thickening ((C+3)*dyadicRadius q) (affinePlane H p)).Nonempty ∧
          dyadicAngleBand q (planeAngle H (u j))=band), w j := by
  obtain ⟨c,hc,hinc⟩ := actual_brush_plane_incidence n R lam B hR hlam hB
  refine ⟨c/3,by positivity,?_⟩
  intro q hq J G S hSG b u w hb hu hw hcap H instH p C M hM hp ha hcaptured
  have hi := hinc (dyadicRadius q) (Real.exp_pos _) (dyadicRadius_le_half hq)
    G S hSG b u w hb hu hw hcap H p C M hM hp ha hcaptured
  let incident := G.filter (fun j => (euclideanTube (b j) (u j) (dyadicRadius q) ∩
    Metric.thickening ((C+3)*dyadicRadius q) (affinePlane H p)).Nonempty)
  obtain ⟨band,hband,hmass⟩ := weighted_angular_band incident (fun j => planeAngle H (u j)) w q hq
    (fun j _ => (planeAngle_range H (u j)).2.trans (by linarith [Real.pi_lt_four]))
    (fun j hj => hw j (Finset.mem_filter.mp hj).1)
  refine ⟨band,hband,?_⟩
  have hh := hi.trans hmass
  dsimp [incident] at hh
  rw [Finset.filter_filter] at hh
  nlinarith only [hh]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadicRadius_le_half
#print axioms KakeyaTwoScale.actual_brush_incident_band
