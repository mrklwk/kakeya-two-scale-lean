module
public import KakeyaTwoScale.VariableDyadicBandBrush
public import KakeyaTwoScale.VariableBrushBands

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
theorem variable_weighted_brush (n k : ℕ) (R lam B C L : ℝ)
    (hR : 0 ≤ R) (hlam : 0 < lam) (hB : 0 < B) (hC : 0 ≤ C) (hL : 1 ≤ L) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 1 ≤ q →
      ∀ {J : Type*} (G S : Finset J), S ⊆ G →
      ∀ (b u : J → EuclideanSpace ℝ (Fin (n+1))) (ell w : J → ℝ),
      (∀ j ∈ G, 1 ≤ ell j ∧ ell j ≤ L) →
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ dyadicRadius q), w j) ≤ B) →
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
        (p : EuclideanSpace ℝ (Fin (n+1))) (M : ℝ),
      Module.finrank ℝ H=k+1 → 0 ≤ M →
      (∀ j ∈ S, p ∈ euclideanTube (b j) (ell j • u j) (dyadicRadius q)) →
      (∀ j ∈ S, planeAngle H (u j) ≤ C*dyadicRadius q) →
      (∀ j ∈ S, lam*volume.real (euclideanTube (b j) (ell j • u j) (dyadicRadius q)) ≤
        volume.real (euclideanTube (b j) (ell j • u j) (dyadicRadius q) ∩ tubeHighSet G b (fun j => ell j • u j) w (dyadicRadius q) M)) →
      c*(dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta*M*(∑ j ∈ S, w j) ≤
        (q:ℝ)*volume.real (⋃ j ∈ G, euclideanTube (b j) (ell j • u j) (dyadicRadius q)) := by
  obtain ⟨ci,hci,hinc⟩ := variable_brush_incident_band n R lam B L hR hlam hB hL
  obtain ⟨cv,hcv,hvol⟩ := dyadic_band_variable_brush_volume n k R L B (L*C+3) hR hL hB (by nlinarith)
  refine ⟨cv*ci,mul_pos hcv hci,?_⟩
  intro q hq J G S hSG b u ell w hell hb hu hw hcap H p M hdim hM hp ha hcaptured
  obtain ⟨band,_,hmass⟩ := hinc q hq G S hSG b u ell w hell hb hu hw hcap H p C M hM hp ha hcaptured
  let r := dyadicRadius q
  let F := G.filter (fun j => (euclideanTube (b j) (ell j • u j) r ∩
    Metric.thickening ((L*C+3)*r) (affinePlane H p)).Nonempty ∧
    dyadicAngleBand q (planeAngle H (u j))=band)
  have hFG : F ⊆ G := Finset.filter_subset _ _
  have hv := hvol q hq H p hdim band F b u ell w
    (fun j hj => hell j (hFG hj))
    (fun j hj => hb j (hFG hj)) (fun j hj => hu j (hFG hj))
    (fun j hj => hw j (hFG hj))
    (fun j hj => (Finset.mem_filter.mp hj).2.2)
    (fun j hj => (Finset.mem_filter.mp hj).2.1)
    (angular_weight_cap_subset G F hFG u w r B hw hcap)
  have huvol : volume.real (⋃ j ∈ F, euclideanTube (b j) (ell j • u j) r) ≤
      volume.real (⋃ j ∈ G, euclideanTube (b j) (ell j • u j) r) := by
    apply measureReal_mono _ (euclideanTube_union_finite G b (fun j => ell j • u j) r)
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

/-- Exact conversion of a fixed power-of-two radius enlargement. -/
theorem dyadicRadius_enlarge (shift q : ℕ) (hq : shift ≤ q) :
    (2:ℝ)^shift*dyadicRadius q=dyadicRadius (q-shift) := by
  apply mul_left_cancel₀ (pow_ne_zero (q-shift) (by norm_num : (2:ℝ) ≠ 0))
  calc
    (2:ℝ)^(q-shift)*((2:ℝ)^shift*dyadicRadius q) = (2:ℝ)^q*dyadicRadius q := by
      rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hq]
    _ = 1 := dyadicRadius_pow_cancel q
    _ = (2:ℝ)^(q-shift)*dyadicRadius (q-shift) := (dyadicRadius_pow_cancel (q-shift)).symm

/-- The variable-length brush at any fixed dyadic enlargement of the source
radius. Its conclusion retains the original rho exponent and original q
loss. Plane concentration is allowed at the finer original radius. -/
theorem scaled_variable_weighted_brush (n k : ℕ) (R lam B C L : ℝ)
    (hR : 0 ≤ R) (hlam : 0 < lam) (hB : 0 < B) (hC : 0 ≤ C) (hL : 1 ≤ L) :
    ∃ c : ℝ, 0 < c ∧ ∀ shift q : ℕ, shift+1 ≤ q →
      ∀ {J : Type*} (G S : Finset J), S ⊆ G →
      ∀ (b u : J → EuclideanSpace ℝ (Fin (n+1))) (ell w : J → ℝ),
      (∀ j ∈ G, 1 ≤ ell j ∧ ell j ≤ L) →
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ (2:ℝ)^shift*dyadicRadius q), w j) ≤ B) →
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
        (p : EuclideanSpace ℝ (Fin (n+1))) (M : ℝ),
      Module.finrank ℝ H=k+1 → 0 ≤ M →
      (∀ j ∈ S, p ∈ euclideanTube (b j) (ell j • u j) ((2:ℝ)^shift*dyadicRadius q)) →
      (∀ j ∈ S, planeAngle H (u j) ≤ C*dyadicRadius q) →
      (∀ j ∈ S, lam*volume.real (euclideanTube (b j) (ell j • u j) ((2:ℝ)^shift*dyadicRadius q)) ≤
        volume.real (euclideanTube (b j) (ell j • u j) ((2:ℝ)^shift*dyadicRadius q) ∩
          tubeHighSet G b (fun j => ell j • u j) w ((2:ℝ)^shift*dyadicRadius q) M)) →
      c*(dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta*M*(∑ j ∈ S, w j) ≤
        (q:ℝ)*volume.real (⋃ j ∈ G, euclideanTube (b j) (ell j • u j) ((2:ℝ)^shift*dyadicRadius q)) := by
  obtain ⟨c,hc,hbrush⟩ := variable_weighted_brush n k R lam B C L hR hlam hB hC hL
  refine ⟨c,hc,?_⟩
  intro shift q hq J G S hSG b u ell w hell hb hu hw hcap H p M hdim hM hp ha hcapture
  have hsq : shift ≤ q := by omega
  have he := dyadicRadius_enlarge shift q hsq
  have hr : 0 < dyadicRadius q := Real.exp_pos _
  have hrs : 0 < dyadicRadius (q-shift) := Real.exp_pos _
  have hmono : dyadicRadius q ≤ dyadicRadius (q-shift) := by
    rw [← he]
    exact le_mul_of_one_le_left hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hcap' := hcap
  have hp' := hp
  have hcapture' := hcapture
  rw [he] at hcap' hp' hcapture'
  have ha' : ∀ j ∈ S, planeAngle H (u j) ≤ C*dyadicRadius (q-shift) := by
    intro j hj
    exact (ha j hj).trans (mul_le_mul_of_nonneg_left hmono hC)
  have hh := hbrush (q-shift) (by omega) G S hSG b u ell w hell hb hu hw hcap'
    H p M hdim hM hp' ha' hcapture'
  have hW : 0 ≤ ∑ j ∈ S, w j := Finset.sum_nonneg (fun j hj => hw j (hSG hj))
  have hpowers : c*(dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta*M*(∑ j ∈ S, w j) ≤
      c*(dyadicRadius (q-shift))^n*((dyadicRadius (q-shift))^(k+1))^theta*M*(∑ j ∈ S, w j) := by
    gcongr
    norm_num [theta]
  have hqcast : (q-shift:ℕ) ≤ q := Nat.sub_le _ _
  have hlast := mul_le_mul_of_nonneg_right (show ((q-shift:ℕ):ℝ) ≤ q by exact_mod_cast hqcast)
    (show 0 ≤ volume.real (⋃ j ∈ G, euclideanTube (b j) (ell j • u j) (dyadicRadius (q-shift))) from measureReal_nonneg)
  rw [he]
  exact hpowers.trans (hh.trans hlast)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.variable_weighted_brush
#print axioms KakeyaTwoScale.dyadicRadius_enlarge
#print axioms KakeyaTwoScale.scaled_variable_weighted_brush
