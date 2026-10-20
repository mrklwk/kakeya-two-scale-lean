module
public import KakeyaTwoScale.EuclideanTubes

@[expose] public section

open Metric
noncomputable section
namespace KakeyaTwoScale

/-- A flat open coaxial cylinder, specified without a choice of rotation. -/
def flatCylinder {d : ℕ} (b u : EuclideanSpace ℝ (Fin d)) (L r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ t : ℝ, 0 < t ∧ t < L ∧
    inner ℝ u (x-(b+t • u)) = 0 ∧ ‖x-(b+t • u)‖ < r}

theorem unit_transverse_error {d : ℕ} (u e : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖=1) : ‖e-(inner ℝ u e) • u‖ ≤ ‖e‖ := by
  have hsq := norm_sub_sq_real e ((inner ℝ u e) • u)
  rw [norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
    inner_smul_right] at hsq
  have hcomm : inner ℝ e u = inner ℝ u e := real_inner_comm _ _
  simp only [hcomm] at hsq
  nlinarith [sq_nonneg (inner ℝ u e), norm_nonneg (e-(inner ℝ u e) • u), norm_nonneg e]

/-- All endpoint caps are contained in a flat cylinder with a strict margin.
The start point is shifted backwards by r and the length is 1+2r. -/
theorem euclideanTube_subset_flatCylinder {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hu : ‖u‖=1) :
    euclideanTube b u r ⊆ flatCylinder (b-r • u) u (1+2*r) r := by
  intro x hx
  obtain ⟨t,ht,hx⟩ := hx
  let e := x-(b+t • u)
  let c := inner ℝ u e
  have he : ‖e‖<r := by simpa [e,dist_eq_norm] using hx
  have hc : |c| < r := by
    have h := abs_real_inner_le_norm u e
    rw [hu,one_mul] at h
    exact h.trans_lt he
  have hc' := abs_lt.mp hc
  have heq : x-((b-r • u)+(t+c+r) • u) = e-c • u := by
    dsimp [e]
    module
  refine ⟨t+c+r,by linarith [ht.1],by linarith [ht.2],?_,?_⟩
  · rw [heq,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu]
    dsimp [c]
    ring
  · rw [heq]
    exact (unit_transverse_error u e hu).trans_lt he

theorem flatCylinder_mono_length {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) {L L' r : ℝ} (hL : L ≤ L') :
    flatCylinder b u L r ⊆ flatCylinder b u L' r := by
  rintro x ⟨t,ht0,htL,hi,hr⟩
  exact ⟨t,ht0,htL.trans_le hL,hi,hr⟩

theorem capsule_subset_uniform_cylinder {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (C δ : ℝ)
    (hu : ‖u‖=1) (hC : 0 ≤ C) (hδ : δ ≤ 1) :
    euclideanTube b u (C*δ) ⊆
      flatCylinder (b-(C*δ) • u) u (2*C+3) (C*δ) := by
  apply Set.Subset.trans (euclideanTube_subset_flatCylinder b u (C*δ) hu)
  apply flatCylinder_mono_length
  nlinarith [mul_le_mul_of_nonneg_left hδ hC]

theorem flatCylinder_dilate {d : ℕ}
    (b u x : EuclideanSpace ℝ (Fin d)) (L r : ℝ) (hL : 0 < L)
    (hx : x ∈ flatCylinder b u L r) :
    L⁻¹ • x ∈ flatCylinder (L⁻¹ • b) u 1 (r/L) := by
  obtain ⟨t,ht0,htL,hi,hr⟩ := hx
  have heq : L⁻¹ • x-(L⁻¹ • b+(t/L) • u) = L⁻¹ • (x-(b+t • u)) := by
    simp only [div_eq_mul_inv]
    module
  refine ⟨t/L,div_pos ht0 hL,(div_lt_one hL).mpr htL,?_,?_⟩
  · rw [heq,inner_smul_right,hi,mul_zero]
  · rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL)]
    simpa [div_eq_mul_inv,mul_comm] using (mul_lt_mul_of_pos_left hr (inv_pos.mpr hL))

theorem rescaled_cylinder_width_le {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    C*δ/(2*C+3) ≤ δ := by
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [mul_nonneg hC hδ]

theorem capsule_dilate_into_unit_cylinder {d : ℕ}
    (b u x : EuclideanSpace ℝ (Fin d)) (C δ : ℝ)
    (hu : ‖u‖=1) (hC : 0 ≤ C) (hδ : δ ≤ 1)
    (hx : x ∈ euclideanTube b u (C*δ)) :
    (2*C+3)⁻¹ • x ∈ flatCylinder
      ((2*C+3)⁻¹ • (b-(C*δ) • u)) u 1 (C*δ/(2*C+3)) :=
  flatCylinder_dilate _ _ _ _ _ (by positivity)
    (capsule_subset_uniform_cylinder b u C δ hu hC hδ hx)

theorem cylinder_rescaled_projective_separation {d : ℕ} {J : Type*}
    (G : Finset J) (u : J → EuclideanSpace ℝ (Fin d)) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hsep : ProjectiveSeparated G u δ) :
    ProjectiveSeparated G u (C*δ/(2*C+3)) := by
  intro j hj k hk hjk
  have h := hsep j hj k hk hjk
  have hwidth := rescaled_cylinder_width_le hC hδ
  exact ⟨hwidth.trans h.1,hwidth.trans h.2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.unit_transverse_error
#print axioms KakeyaTwoScale.euclideanTube_subset_flatCylinder
#print axioms KakeyaTwoScale.flatCylinder_mono_length
#print axioms KakeyaTwoScale.capsule_subset_uniform_cylinder
#print axioms KakeyaTwoScale.flatCylinder_dilate
#print axioms KakeyaTwoScale.rescaled_cylinder_width_le
#print axioms KakeyaTwoScale.capsule_dilate_into_unit_cylinder
#print axioms KakeyaTwoScale.cylinder_rescaled_projective_separation
