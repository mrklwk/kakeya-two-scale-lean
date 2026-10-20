module
public import KakeyaTwoScale.BrushWeights

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open InnerProductGeometry
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Exact chord formula for unit vectors, including equal and antipodal cases. -/
theorem unit_direction_chord (x y : X) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    dist x y = 2 * Real.sin (angle x y / 2) := by
  have hnorm := norm_sub_pow_two_real x y
  rw [hx, hy, inner_eq_cos_angle_of_norm_eq_one hx hy] at hnorm
  have htrig := Real.cos_two_mul (angle x y / 2)
  have hsc := Real.sin_sq_add_cos_sq (angle x y / 2)
  have he : 2 * (angle x y / 2) = angle x y := by ring
  rw [he] at htrig
  have hs : 0 ≤ Real.sin (angle x y / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [angle_nonneg x y])
      (by linarith [angle_le_pi x y, Real.pi_pos])
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x-y)]

/-- Spherical angle and chord distance have global, dimension-free constants. -/
theorem unit_direction_angle_bounds (x y : X) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    dist x y ≤ angle x y ∧ angle x y ≤ (Real.pi/2)*dist x y := by
  have h0 : 0 ≤ angle x y / 2 := by linarith [angle_nonneg x y]
  have hpi : angle x y / 2 ≤ Real.pi/2 := by linarith [angle_le_pi x y]
  rw [unit_direction_chord x y hx hy]
  constructor
  · linarith [Real.sin_le h0]
  · have h := Real.mul_le_sin h0 hpi
    have hm := mul_le_mul_of_nonneg_left h Real.pi_pos.le
    have hc : Real.pi * (2 / Real.pi * (angle x y / 2)) = angle x y := by
      field_simp
    rw [hc] at hm
    nlinarith

/-- A spherical cap of radius r contains the chord ball of radius 2r/pi.
There is no small-angle restriction and constants do not depend on dimension. -/
theorem chord_lt_implies_angle_lt (x y : X) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (r : ℝ) (hd : dist x y < 2*r/Real.pi) : angle x y < r := by
  have hb := (unit_direction_angle_bounds x y hx hy).2
  have hm := mul_lt_mul_of_pos_left hd (by positivity : 0 < Real.pi/2)
  have hc : (Real.pi/2)*(2*r/Real.pi) = r := by field_simp
  rw [hc] at hm
  exact hb.trans_lt hm

/-- Chord separation also implies spherical separation, with no constant loss. -/
theorem chord_separated_implies_angle_separated (x y : X)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (r : ℝ) (hd : r ≤ dist x y) :
    r ≤ angle x y := hd.trans (unit_direction_angle_bounds x y hx hy).1

/-- A source spherical cap bound implies the chord cap bound at the exact
radius 2r/pi, preserving the original cap constant. -/
theorem angular_weight_cap_to_chord {J : Type*} (family : Finset J)
    (a : J → X) (w : J → ℝ) (r B : ℝ)
    (hw : ∀ j ∈ family, 0 ≤ w j) (hunit : ∀ j ∈ family, ‖a j‖ = 1)
    (hcap : ∀ x : X, ‖x‖ = 1 →
      (∑ j ∈ family.filter (fun j => angle (a j) x < r), w j) ≤ B) :
    ∀ x : X, ‖x‖ = 1 →
      (∑ j ∈ family.filter (fun j => dist (a j) x < 2*r/Real.pi), w j) ≤ B := by
  classical
  intro x hx
  apply le_trans _ (hcap x hx)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨hj, hd⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hj, chord_lt_implies_angle_lt (a j) x
      (hunit j hj) hx r hd⟩
  · intro j hj _
    exact hw j (Finset.mem_filter.mp hj).1

/-- Actual separated-subfamily extraction from the source angular cap bound.
Both spherical and chord separation are output, including the antipodal sign.
All losses (2 in weight, 2/pi in radius) are explicit uniform constants. -/
theorem angular_weight_separated_extraction {J : Type*} (family : Finset J)
    (a : J → X) (w : J → ℝ) (r B : ℝ) (hr : 0 < r)
    (hw : ∀ j ∈ family, 0 ≤ w j) (hunit : ∀ j ∈ family, ‖a j‖ = 1)
    (hcap : ∀ x : X, ‖x‖ = 1 →
      (∑ j ∈ family.filter (fun j => angle (a j) x < r), w j) ≤ B) :
    ∃ selected : Finset J, selected ⊆ family ∧
      (∀ j ∈ selected, ∀ k ∈ selected, j ≠ k →
        2*r/Real.pi ≤ dist (a j) (a k) ∧
        2*r/Real.pi ≤ dist (a j) (-a k) ∧
        2*r/Real.pi ≤ angle (a j) (a k) ∧
        2*r/Real.pi ≤ angle (a j) (-a k)) ∧
      (∑ j ∈ family, w j) ≤ 2*B*(selected.card : ℝ) := by
  obtain ⟨selected, hsub, hsep, hweight⟩ := weighted_unit_direction_extraction
    family a w (2*r/Real.pi) B (by positivity) hw hunit
    (angular_weight_cap_to_chord family a w r B hw hunit hcap)
  refine ⟨selected, hsub, ?_, hweight⟩
  intro j hj k hk hne
  obtain ⟨hp, hn⟩ := hsep j hj k hk hne
  have hjunit := hunit j (hsub hj)
  have hkunit := hunit k (hsub hk)
  exact ⟨hp, hn,
    chord_separated_implies_angle_separated _ _ hjunit hkunit _ hp,
    chord_separated_implies_angle_separated _ _ hjunit (by simpa using hkunit) _ hn⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.unit_direction_chord
#print axioms KakeyaTwoScale.unit_direction_angle_bounds
#print axioms KakeyaTwoScale.chord_lt_implies_angle_lt
#print axioms KakeyaTwoScale.chord_separated_implies_angle_separated

#print axioms KakeyaTwoScale.angular_weight_cap_to_chord
#print axioms KakeyaTwoScale.angular_weight_separated_extraction
