module
public import KakeyaTwoScale.MultilinearMass

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- A translated half-scale unit capsule lies strictly inside the unit flat
cylinder. The transverse radius is smaller and both endpoints have margin. -/
theorem half_capsule_subset_flatCylinder {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    (fun x => (2 : ℝ) • x) ⁻¹' euclideanTube ((2 : ℝ) • b + (1 / 2 : ℝ) • u) u r ⊆
      flatCylinder b u 1 r := by
  rintro x ⟨t, ht, hx⟩
  let e := (2 : ℝ) • x - ((2 : ℝ) • b + (1 / 2 : ℝ) • u + t • u)
  let c := inner ℝ u e
  have he : ‖e‖ < r := by simpa [e, dist_eq_norm] using hx
  have hc : |c| < r := by
    have hh : |c| ≤ ‖e‖ := by simpa [c, hu] using abs_real_inner_le_norm u e
    exact hh.trans_lt he
  have hc' := abs_lt.mp hc
  have heq : x - (b + (1 / 4 + t / 2 + c / 2) • u) =
      (1 / 2 : ℝ) • (e - c • u) := by
    dsimp [e]
    module
  refine ⟨1 / 4 + t / 2 + c / 2, by linarith [ht.1], by linarith [ht.2], ?_, ?_⟩
  · rw [heq, inner_smul_right, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hu]
    dsimp [c]
    ring
  · rw [heq, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hh := unit_transverse_error u e hu
    linarith

/-- Dimension-only lower mass for literal flat unit cylinders at every
0<r≤1/2, independent of positions and unit directions. -/
theorem flatCylinder_volume_lower_unrestricted (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      ∀ b u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ = 1 →
      c * r ^ n ≤ volume.real (flatCylinder b u 1 r) := by
  obtain ⟨c, hc, hvol⟩ := euclideanTube_volume_lower_unrestricted n
  refine ⟨(1 / 2 : ℝ) ^ (n + 1) * c, by positivity, ?_⟩
  intro r hr hrhalf b u hu
  let E := euclideanTube ((2 : ℝ) • b + (1 / 2 : ℝ) • u) u r
  have hE : MeasurableSet E := (isOpen_euclideanTube _ _ _).measurableSet
  have hm : volume ((fun x : EuclideanSpace ℝ (Fin (n + 1)) => (2 : ℝ) • x) ⁻¹' E) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) * volume E := by
    have hh := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin (n + 1))) => μ E)
      (volume_map_inverse_dilation (n + 1) (show (0 : ℝ) < 1 / 2 by norm_num))
    have hscale : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) => (2 : ℝ) • x) := by fun_prop
    simp only [one_div, inv_inv] at hh
    simpa only [Measure.map_apply hscale hE, Measure.smul_apply, smul_eq_mul, one_div] using hh
  have hmreal : volume.real ((fun x : EuclideanSpace ℝ (Fin (n + 1)) => (2 : ℝ) • x) ⁻¹' E) =
      (1 / 2 : ℝ) ^ (n + 1) * volume.real E := by
    simp only [Measure.real, hm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ (1 / 2 : ℝ) ^ (n + 1) by positivity)]
  have hlo := mul_le_mul_of_nonneg_left (hvol r hr ((2 : ℝ) • b + (1 / 2 : ℝ) • u) u hu)
    (show 0 ≤ (1 / 2 : ℝ) ^ (n + 1) by positivity)
  have hmono := measureReal_mono (half_capsule_subset_flatCylinder b u hu hr hrhalf)
    (flatCylinder_unit_finite b u r)
  rw [hmreal] at hmono
  have hlo' : (1 / 2 : ℝ) ^ (n + 1) * c * r ^ n ≤ (1 / 2 : ℝ) ^ (n + 1) * volume.real E := by
    simpa only [E, mul_assoc] using hlo
  exact hlo'.trans hmono

end KakeyaTwoScale
#print axioms KakeyaTwoScale.half_capsule_subset_flatCylinder
#print axioms KakeyaTwoScale.flatCylinder_volume_lower_unrestricted
