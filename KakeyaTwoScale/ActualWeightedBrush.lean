module
public import KakeyaTwoScale.DyadicBandBrush

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The actual weighted brush estimate at the source's dyadic widths.
Ambient dimension is n+1; the base plane has dimension k+1, so the source
brush exponent is n+(k+1)*theta. Every volume, capture and angular cap is
stated on the original capsules and weights. All intermediate geometric,
arithmetic, shortening, overlap and band estimates are proved internally. -/
theorem actual_weighted_brush (n k : ℕ) (R lam B C : ℝ)
    (hR : 0 ≤ R) (hlam : 0 < lam) (hB : 0 < B) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 1 ≤ q →
      ∀ {J : Type*} (G S : Finset J), S ⊆ G →
      ∀ (b u : J → EuclideanSpace ℝ (Fin (n+1))) (w : J → ℝ),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ dyadicRadius q), w j) ≤ B) →
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
        (p : EuclideanSpace ℝ (Fin (n+1))) (M : ℝ),
      Module.finrank ℝ H=k+1 → 0 ≤ M →
      (∀ j ∈ S, p ∈ euclideanTube (b j) (u j) (dyadicRadius q)) →
      (∀ j ∈ S, planeAngle H (u j) ≤ C*dyadicRadius q) →
      (∀ j ∈ S, lam*volume.real (euclideanTube (b j) (u j) (dyadicRadius q)) ≤
        volume.real (euclideanTube (b j) (u j) (dyadicRadius q) ∩ tubeHighSet G b u w (dyadicRadius q) M)) →
      c*(dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta*M*(∑ j ∈ S, w j) ≤
        (q:ℝ)*volume.real (⋃ j ∈ G, euclideanTube (b j) (u j) (dyadicRadius q)) := by
  obtain ⟨ci,hci,hinc⟩ := actual_brush_incident_band n R lam B hR hlam hB
  obtain ⟨cv,hcv,hvol⟩ := dyadic_band_brush_volume n k R B (C+3) hR hB (by linarith)
  refine ⟨cv*ci,mul_pos hcv hci,?_⟩
  intro q hq J G S hSG b u w hb hu hw hcap H p M hdim hM hp ha hcaptured
  obtain ⟨band,_,hmass⟩ := hinc q hq G S hSG b u w hb hu hw hcap H p C M hM hp ha hcaptured
  let r := dyadicRadius q
  let F := G.filter (fun j => (euclideanTube (b j) (u j) r ∩
    Metric.thickening ((C+3)*r) (affinePlane H p)).Nonempty ∧
    dyadicAngleBand q (planeAngle H (u j))=band)
  have hFG : F ⊆ G := Finset.filter_subset _ _
  have hv := hvol q hq H p hdim band F b u w
    (fun j hj => hb j (hFG hj)) (fun j hj => hu j (hFG hj))
    (fun j hj => hw j (hFG hj))
    (fun j hj => (Finset.mem_filter.mp hj).2.2)
    (fun j hj => (Finset.mem_filter.mp hj).2.1)
    (angular_weight_cap_subset G F hFG u w r B hw hcap)
  have huvol : volume.real (⋃ j ∈ F, euclideanTube (b j) (u j) r) ≤
      volume.real (⋃ j ∈ G, euclideanTube (b j) (u j) r) := by
    apply measureReal_mono _ (euclideanTube_union_finite G b u r)
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j,hFG hj,hx⟩
  have hfactor : 0 ≤ cv*r^n*(r^(k+1))^theta := by
    have hr : 0 < r := Real.exp_pos _
    positivity
  have hh := mul_le_mul_of_nonneg_left hmass hfactor
  have hlast := mul_le_mul_of_nonneg_left (hv.trans huvol) (Nat.cast_nonneg q : (0:ℝ) ≤ q)
  change cv*r^n*(r^(k+1))^theta*(ci*M*(∑ j ∈ S, w j)) ≤
    cv*r^n*(r^(k+1))^theta*((q:ℝ)*∑ j ∈ F, w j) at hh
  calc
    _ = cv*r^n*(r^(k+1))^theta*(ci*M*(∑ j ∈ S, w j)) := by ring
    _ ≤ cv*r^n*(r^(k+1))^theta*((q:ℝ)*∑ j ∈ F, w j) := hh
    _ = (q:ℝ)*(cv*r^n*(r^(k+1))^theta*(∑ j ∈ F, w j)) := by ring
    _ ≤ _ := hlast

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_weighted_brush
