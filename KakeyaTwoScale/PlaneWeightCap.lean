module
public import KakeyaTwoScale.PlaneDirectionPacking
public import KakeyaTwoScale.BrushTubeOverlap

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Source plane-direction weight cap, with the sharp power k for a
(k+1)-dimensional plane. It is derived from the original angular caps; no
plane packing or plane-weight bound is assumed. -/
theorem plane_direction_weight_cap (d k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin d))) [H.HasOrthogonalProjection],
      Module.finrank ℝ H=k+1 → ∀ r B : ℝ, 0 < r → r ≤ 1 → 0 ≤ B →
      ∀ {J : Type*} (G : Finset J) (u : J → EuclideanSpace ℝ (Fin d)) (w : J → ℝ),
      (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ j ∈ G, planeAngle H (u j) ≤ C*r) →
      (∀ v : EuclideanSpace ℝ (Fin d), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      (∑ j ∈ G, w j)*r^k ≤ K*B := by
  let eta : ℝ := 2/Real.pi
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heone : eta ≤ 1 := by
    dsimp [eta]; apply (div_le_iff₀ Real.pi_pos).mpr; linarith [Real.pi_gt_three]
  obtain ⟨K,hK,hpack⟩ := near_plane_direction_packing d k (C/eta) (by positivity)
  refine ⟨2*K/eta^k,by positivity,?_⟩
  intro H instH hdim r B hr hrone hB J G u w hu hw ha hcap
  obtain ⟨S,hSG,hsep,hweight⟩ := angular_weight_separated_extraction G u w r B hr hw hu
    (source_cap_to_oriented G u w r B hw hu hcap)
  have hnear : ∀ j ∈ S, ‖normalProjection H (u j)‖ ≤ (C/eta)*(eta*r) := by
    intro j hj
    have hh := (planeAngle_speed_bounds H (u j) (hu j (hSG hj))).2.trans (ha j (hSG hj))
    convert hh using 1; field_simp
  have hseps : ∀ j ∈ S, ∀ l ∈ S, j ≠ l →
      eta*r ≤ dist (u j) (u l) ∧ eta*r ≤ dist (u j) (-u l) := by
    intro j hj l hl hjl
    have he : eta*r=2*r/Real.pi := by dsimp [eta]; ring
    rw [he]
    exact ⟨(hsep j hj l hl hjl).1,(hsep j hj l hl hjl).2.1⟩
  have hcard := hpack H hdim (eta*r) (mul_pos heta hr)
    ((mul_le_of_le_one_left hr.le heone).trans hrone) S u
    (fun j hj => hu j (hSG hj)) hnear hseps
  rw [mul_pow] at hcard
  have hcard' : (S.card:ℝ)*r^k ≤ K/eta^k := by
    apply (le_div_iff₀ (pow_pos heta k)).mpr
    nlinarith only [hcard]
  have hh := mul_le_mul_of_nonneg_right hweight (pow_nonneg hr.le k)
  have hm := mul_le_mul_of_nonneg_left hcard' (show 0 ≤ 2*B by positivity)
  have he : (2*K/eta^k)*B=2*B*(K/eta^k) := by ring
  rw [he]
  nlinarith only [hh,hm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.plane_direction_weight_cap
