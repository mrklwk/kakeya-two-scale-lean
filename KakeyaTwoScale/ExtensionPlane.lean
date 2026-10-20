module
public import KakeyaTwoScale.PlaneWeightedVolume
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

def extensionSubspace (H : Submodule ℝ X) (a : X) : Submodule ℝ X := H ⊔ ℝ ∙ a

theorem extensionSubspace_finrank (H : Submodule ℝ X) (a : X)
    (ha : a ∈ Hᗮ) (haunit : ‖a‖=1) :
    Module.finrank ℝ (extensionSubspace H a)=Module.finrank ℝ H+1 := by
  have hane : a ≠ 0 := by intro he; simp [he] at haunit
  have hs : ℝ ∙ a ≤ Hᗮ := Submodule.span_le.mpr (by intro x hx; simpa using Set.mem_singleton_iff.mp hx ▸ ha)
  have hd : Disjoint H (ℝ ∙ a) := H.orthogonal_disjoint.mono_right hs
  have hh := Submodule.finrank_sup_add_finrank_inf_eq H (ℝ ∙ a)
  rw [hd.eq_bot,finrank_bot,add_zero,finrank_span_singleton hane] at hh
  exact hh

theorem extension_normal_bound (H : Submodule ℝ X) (a u : X) (c e : ℝ)
    (he : ‖normalProjection H u-c • a‖ ≤ e) :
    ‖normalProjection (extensionSubspace H a) u‖ ≤ e := by
  let L := extensionSubspace H a
  have hmem : H.starProjection u+c • a ∈ L := by
    apply L.add_mem
    · exact (show H ≤ L from le_sup_left) (H.starProjection_apply_mem u)
    · exact (show ℝ ∙ a ≤ L from le_sup_right) (Submodule.smul_mem (ℝ ∙ a) c (Submodule.subset_span (by simp)))
  have heq : u-(H.starProjection u+c • a)=normalProjection H u-c • a := by
    rw [normalProjection,Submodule.starProjection_orthogonal_val]; abel
  have hh : normalProjection L (u-(H.starProjection u+c • a))=normalProjection L u := by
    rw [map_sub,normalProjection_zero L hmem,sub_zero]
  have hbound := Lᗮ.norm_starProjection_apply_le (u-(H.starProjection u+c • a))
  change ‖normalProjection L (u-(H.starProjection u+c • a))‖ ≤ _ at hbound
  rw [hh,heq] at hbound
  exact hbound.trans he

theorem extension_plane_angle_bound (H : Submodule ℝ X) (a u : X) (r : ℝ)
    (hu : ‖u‖=1) (he : ∃ c : ℝ, ‖normalProjection H u-c • a‖ ≤ 2*r) :
    planeAngle (extensionSubspace H a) u ≤ Real.pi*r := by
  obtain ⟨c,hc⟩ := he
  have hb := (planeAngle_speed_bounds (extensionSubspace H a) u hu).1.trans
    (extension_normal_bound H a u c (2*r) hc)
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ Real.pi/2 by positivity)
  have hid : (Real.pi/2)*((2/Real.pi)*planeAngle (extensionSubspace H a) u)=
      planeAngle (extensionSubspace H a) u := by field_simp
  rw [hid] at hh
  nlinarith only [hh]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.extensionSubspace_finrank
#print axioms KakeyaTwoScale.extension_normal_bound
#print axioms KakeyaTwoScale.extension_plane_angle_bound
