module
public import KakeyaTwoScale.MultilinearScale
public import KakeyaTwoScale.VariableTubeVolume

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Dilation of an exact finite variable-length capsule into a unit capsule.
Only its normalized segment is extended, inside the comparison family; the
original capsule, directions and overlap function are unchanged. -/
theorem variable_capsule_dilate_unit {n : ℕ}
    (b u x : EuclideanSpace ℝ (Fin n)) (ell L r : ℝ)
    (hL : 0 < L) (hell : 0 ≤ ell) (hellL : ell ≤ L)
    (hx : x∈euclideanTube b (ell • u) r) :
    L⁻¹ • x ∈ euclideanTube (L⁻¹ • b) u (r/L) := by
  obtain ⟨t,ht,hx⟩ := hx
  have he : L⁻¹ • x-(L⁻¹ • b+(t*ell/L) • u)=L⁻¹ • (x-(b+t • (ell • u))) := by
    simp only [div_eq_mul_inv,smul_smul]
    module
  refine ⟨t*ell/L,⟨div_nonneg (mul_nonneg ht.1 hell) hL.le,?_⟩,?_⟩
  · apply (div_le_one hL).mpr
    exact (mul_le_of_le_one_left hell ht.2).trans hellL
  · rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL)]
    simpa [div_eq_mul_inv,mul_comm,dist_eq_norm] using
      mul_lt_mul_of_pos_left hx (inv_pos.mpr hL)

/-- Actual variable-axis multilinear norm transport, with its exact dilation
factor and genuine extended-real norms. -/
theorem variable_capsule_multilinear_norm_dilate_le {n N : ℕ} (k : ℕ)
    (b u : Fin N → EuclideanSpace ℝ (Fin n)) (ell : Fin N → ℝ)
    (B L r : ℝ) (hL : 0 < L) (hell : ∀ j, 0 ≤ ell j ∧ ell j ≤ L) (p : ENNReal) :
    eLpNorm (multilinearKakeyaFunction k u
      (fun j => euclideanTube (b j) (ell j • u j) r) B) p volume ≤
    ENNReal.ofReal (L^((n:ℝ)/p.toReal))*
      eLpNorm (multilinearKakeyaFunction k u
        (fun j => euclideanTube (L⁻¹ • b j) (u j) (r/L)) B) p volume := by
  let T := fun j => euclideanTube (b j) (ell j • u j) r
  let S := fun j => euclideanTube (L⁻¹ • b j) (u j) (r/L)
  let F := multilinearKakeyaFunction k u S B
  have hF : Measurable F :=
    (measurable_multilinearKakeyaFunction k u S B (fun j => (isOpen_euclideanTube _ _ _).measurableSet))
  have hnorm : eLpNorm (multilinearKakeyaFunction k u T B) p volume ≤
      eLpNorm (fun x => F (L⁻¹ • x)) p volume := by
    apply eLpNorm_mono_ae
      (measurable_multilinearKakeyaFunction k u T B (fun j => (isOpen_euclideanTube _ _ _).measurableSet)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    simp only [F,Real.norm_eq_abs,abs_of_nonneg (multilinearKakeyaFunction_nonneg k u T B x),
      abs_of_nonneg (multilinearKakeyaFunction_nonneg k u S B (L⁻¹ • x))]
    apply multilinearKakeyaFunction_le_of_membership
    intro j hj
    exact variable_capsule_dilate_unit (b j) (u j) x (ell j) L r hL (hell j).1 (hell j).2 hj
  exact hnorm.trans_eq (eLpNorm_inverse_dilation_rpow F hF p hL)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.variable_capsule_dilate_unit
#print axioms KakeyaTwoScale.variable_capsule_multilinear_norm_dilate_le
