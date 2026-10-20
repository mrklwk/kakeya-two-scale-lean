module
public import KakeyaTwoScale.PlaneWeightCap
public import KakeyaTwoScale.WeightedTubeVolume

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The source's linear weighted plane-piece volume bound, for actual capsules.
Neither the arithmetic volume bound nor the sharp plane-weight cap is assumed.
Here the plane has dimension k+1 and ambient dimension n+1. -/
theorem plane_weighted_capsule_volume (n k : ℕ) (R L B C : ℝ)
    (hR : 0 ≤ R) (hL : 0 < L) (hLone : L ≤ 1) (hB : 0 < B) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))) [H.HasOrthogonalProjection],
      Module.finrank ℝ H=k+1 → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ {J : Type*} (G : Finset J) (b u : J → EuclideanSpace ℝ (Fin (n+1))) (w : J → ℝ),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ j ∈ G, planeAngle H (u j) ≤ C*r) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      c*r^n*(r^k)^theta*(∑ j ∈ G, w j) ≤
        volume.real (⋃ j ∈ G, euclideanTube (b j) (L • u j) r) := by
  obtain ⟨cv,hcv,hvol⟩ := weighted_short_euclidean_tubes_volume n R L B hR hL hLone hB
  obtain ⟨K,hK,hcap⟩ := plane_direction_weight_cap (n+1) k C hC
  refine ⟨cv*(K*B)^(a-1),by positivity,?_⟩
  intro H instH hdim r hr hrone J G b u w hb hu hw ha hcaps
  have hW : 0 ≤ ∑ j ∈ G, w j := Finset.sum_nonneg hw
  have hc := hcap H hdim r B hr hrone hB.le G u w hu hw ha hcaps
  have hc' : (∑ j ∈ G, w j) ≤ K*B/r^k := (le_div_iff₀ (pow_pos hr k)).mpr hc
  have hlinear := capped_weight_linearization (∑ j ∈ G, w j) (K*B/r^k) a hW hc' (by norm_num [a])
  have he : (K*B/r^k)^(a-1)=(K*B)^(a-1)*(r^k)^theta := by
    rw [Real.div_rpow (by positivity) (pow_nonneg hr.le k)]
    conv_lhs => rhs; rw [show a-1= -theta by norm_num [a,theta],Real.rpow_neg (pow_nonneg hr.le k)]
    rw [div_inv_eq_mul]
  rw [he] at hlinear
  have hh := mul_le_mul_of_nonneg_left hlinear (show 0 ≤ cv*r^n by positivity)
  have hv := hvol r hr G b u w hb hu hw hcaps
  have hf := hh.trans hv
  convert hf using 1; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.plane_weighted_capsule_volume
