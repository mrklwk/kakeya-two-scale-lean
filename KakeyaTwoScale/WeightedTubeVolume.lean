module
public import KakeyaTwoScale.ShortEuclideanTubes
public import KakeyaTwoScale.BrushTubeOverlap

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem euclideanTube_mono_radius {d : ℕ} (b u : EuclideanSpace ℝ (Fin d))
    {r s : ℝ} (hrs : r ≤ s) : euclideanTube b u r ⊆ euclideanTube b u s := by
  rintro x ⟨t,ht,hx⟩
  exact ⟨t,ht,hx.trans_le hrs⟩

/-- The source angular cap condition suffices for the weighted arithmetic
volume estimate on actual fixed-length capsules. No separated subfamily or
volume lower bound is assumed, and zero total weight is included. -/
theorem weighted_short_euclidean_tubes_volume (n : ℕ) (R L B : ℝ)
    (hR : 0 ≤ R) (hL : 0 < L) (hLone : L ≤ 1) (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ {J : Type*} (G : Finset J) (b u : J → EuclideanSpace ℝ (Fin (n+1))) (w : J → ℝ),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      c*r^n*(∑ j ∈ G, w j)^a ≤ volume.real (⋃ j ∈ G, euclideanTube (b j) (L • u j) r) := by
  obtain ⟨C,hC,hvol⟩ := short_separated_euclidean_tubes_volume n R L hR hL hLone
  let eta : ℝ := 2/Real.pi
  have he : 0 < eta := by dsimp [eta]; positivity
  have heone : eta ≤ 1 := by dsimp [eta]; apply (div_le_iff₀ Real.pi_pos).mpr; linarith [Real.pi_gt_three]
  refine ⟨C*eta^n/(2*B)^a,by positivity,?_⟩
  intro r hr J G b u w hb hu hw hcap
  let W := ∑ j ∈ G, w j
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  by_cases hz : W=0
  · change _*r^n*W^a ≤ _
    rw [hz,Real.zero_rpow (by norm_num [a]),mul_zero]
    exact measureReal_nonneg
  have hWpos : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
  obtain ⟨S,hSG,hsep,hweight⟩ := angular_weight_separated_extraction G u w r B hr hw hu
    (source_cap_to_oriented G u w r B hw hu hcap)
  have hS : S.Nonempty := by
    by_contra hh
    have hs := Finset.not_nonempty_iff_eq_empty.mp hh
    rw [hs] at hweight
    simp only [Finset.card_empty,Nat.cast_zero,mul_zero] at hweight
    exact (not_le_of_gt hWpos) hweight
  have hseps : ∀ j ∈ S, ∀ k ∈ S, j ≠ k →
      eta*r ≤ Real.arccos |inner ℝ (u j) (u k)| := by
    intro j hj k hk hjk
    have hh := hsep j hj k hk hjk
    apply (source_angle_separation_iff (u j) (u k) (hu j (hSG hj)) (hu k (hSG hk)) (eta*r)).mpr
    constructor
    · convert hh.2.2.1 using 1; dsimp [eta]; ring
    · convert hh.2.2.2 using 1; dsimp [eta]; ring
  have hv := hvol (eta*r) (mul_pos he hr) S hS b u
    (fun j hj => hb j (hSG hj)) (fun j hj => hu j (hSG hj)) hseps
  have hsub : (⋃ j ∈ S, euclideanTube (b j) (L • u j) (eta*r)) ⊆
      ⋃ j ∈ G, euclideanTube (b j) (L • u j) r := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j,hSG hj,euclideanTube_mono_radius _ _
      (mul_le_of_le_one_left hr.le heone) hx⟩
  have hv' := hv.trans (measureReal_mono hsub (euclideanTube_union_finite G b (fun j => L • u j) r))
  have hp := extracted_weight_power W B (S.card:ℝ) a hW hB.le (Nat.cast_nonneg _) (by norm_num [a]) hweight
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ C*eta^n*r^n by positivity)
  have hmul := mul_le_mul_of_nonneg_right hv' (show 0 ≤ (2*B)^a by positivity)
  rw [mul_pow] at hmul
  have hfinal : C*eta^n*r^n*W^a ≤
      volume.real (⋃ j ∈ G, euclideanTube (b j) (L • u j) r)*(2*B)^a := by
    nlinarith only [hm,hmul]
  have hh := (div_le_iff₀ (show 0 < (2*B)^a by positivity)).mpr hfinal
  change _*r^n*W^a ≤ _
  convert hh using 1; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclideanTube_mono_radius
#print axioms KakeyaTwoScale.weighted_short_euclidean_tubes_volume
