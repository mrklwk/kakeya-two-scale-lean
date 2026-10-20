module
public import KakeyaTwoScale.MultilinearContainment
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem mem_flatCylinder_iff_coordinates {n : ℕ}
    (b u x : EuclideanSpace ℝ (Fin n)) (L r : ℝ) (hu : ‖u‖=1) :
    x∈flatCylinder b u L r ↔
      0 < inner ℝ u (x-b) ∧ inner ℝ u (x-b)<L ∧
        ‖x-(b+(inner ℝ u (x-b)) • u)‖<r := by
  constructor
  · rintro ⟨t,ht0,htL,hi,hr⟩
    have he : x-(b+t • u)=(x-b)-t • u := by module
    rw [he,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu] at hi
    have ht : inner ℝ u (x-b)=t := by nlinarith
    simpa only [ht] using (show 0<t ∧ t<L ∧ ‖x-(b+t • u)‖<r from ⟨ht0,htL,hr⟩)
  · rintro ⟨ht0,htL,hr⟩
    refine ⟨inner ℝ u (x-b),ht0,htL,?_,hr⟩
    have he : x-(b+(inner ℝ u (x-b)) • u)=(x-b)-(inner ℝ u (x-b)) • u := by module
    rw [he,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu]
    ring

theorem isOpen_flatCylinder {n : ℕ}
    (b u : EuclideanSpace ℝ (Fin n)) (L r : ℝ) (hu : ‖u‖=1) :
    IsOpen (flatCylinder b u L r) := by
  have he : flatCylinder b u L r = {x | 0 < inner ℝ u (x-b)} ∩
      {x | inner ℝ u (x-b)<L} ∩ {x | ‖x-(b+(inner ℝ u (x-b)) • u)‖<r} := by
    ext x
    rw [mem_flatCylinder_iff_coordinates b u x L r hu]
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,and_assoc]
  rw [he]
  apply IsOpen.inter
  · exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const)
  · exact isOpen_lt (by fun_prop) continuous_const

/-- Exact Haar pushforward under positive inverse dilation. -/
theorem volume_map_inverse_dilation (n : ℕ) {L : ℝ} (hL : 0<L) :
    Measure.map (fun x : EuclideanSpace ℝ (Fin n) => L⁻¹ • x) volume =
      ENNReal.ofReal (L^n) • volume := by
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hL.ne')]
  simp [inv_pow,abs_of_pos (pow_pos hL n)]

/-- Extended-real Lp dilation, without finiteness of the function norm.
The formula also includes p=0 and p=infinity under mathlib conventions. -/
theorem eLpNorm_inverse_dilation {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    (p : ℝ≥0∞) {L : ℝ} (hL : 0<L) :
    eLpNorm (fun x => f (L⁻¹ • x)) p volume =
      (ENNReal.ofReal (L^n))^((1/p).toReal) * eLpNorm f p volume := by
  have hd : Measurable (fun x : EuclideanSpace ℝ (Fin n) => L⁻¹ • x) := by fun_prop
  have he := eLpNorm_map_measure (p:=p) (μ:=volume)
    (f:=fun x : EuclideanSpace ℝ (Fin n) => L⁻¹ • x)
    hf.aestronglyMeasurable hd.aemeasurable
  rw [volume_map_inverse_dilation n hL] at he
  rw [eLpNorm_smul_measure_of_ne_zero (by positivity)] at he
  exact he.symm

/-- Equivalent conventional factor L^(n/p), retained in ENNReal. -/
theorem eLpNorm_inverse_dilation_rpow {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    (p : ℝ≥0∞) {L : ℝ} (hL : 0<L) :
    eLpNorm (fun x => f (L⁻¹ • x)) p volume =
      ENNReal.ofReal (L^((n:ℝ)/p.toReal)) * eLpNorm f p volume := by
  rw [eLpNorm_inverse_dilation f hf p hL]
  congr 1
  rw [ENNReal.ofReal_rpow_of_pos (pow_pos hL n)]
  congr 1
  rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
  simp [div_eq_mul_inv]

/-- Actual multilinear capsule norm controlled by normalized cylinders,
including infinite norm values. No cylinder estimate is assumed here. -/
theorem capsule_multilinear_norm_dilate_le {n N : ℕ} (k : ℕ)
    (b u : Fin N → EuclideanSpace ℝ (Fin n)) (B C δ : ℝ) (p : ℝ≥0∞)
    (hu : ∀ j, ‖u j‖=1) (hC : 0≤C) (hδ : δ≤1) :
    eLpNorm (multilinearKakeyaFunction k u
      (fun j => euclideanTube (b j) (u j) (C*δ)) B) p volume ≤
    ENNReal.ofReal ((2*C+3)^((n:ℝ)/p.toReal)) *
      eLpNorm (multilinearKakeyaFunction k u
        (fun j => flatCylinder ((2*C+3)⁻¹ • (b j-(C*δ) • u j))
          (u j) 1 (C*δ/(2*C+3))) B) p volume := by
  let T := fun j => euclideanTube (b j) (u j) (C*δ)
  let S := fun j => flatCylinder ((2*C+3)⁻¹ • (b j-(C*δ) • u j))
    (u j) 1 (C*δ/(2*C+3))
  let F := multilinearKakeyaFunction k u S B
  have hF : Measurable F := measurable_multilinearKakeyaFunction k u S B
    (fun j => (isOpen_flatCylinder _ _ _ _ (hu j)).measurableSet)
  have hnorm : eLpNorm (multilinearKakeyaFunction k u T B) p volume ≤
      eLpNorm (fun x => F ((2*C+3)⁻¹ • x)) p volume := by
    apply eLpNorm_mono_ae (measurable_multilinearKakeyaFunction k u T B
      (fun j => (isOpen_euclideanTube _ _ _).measurableSet)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    simp only [F,Real.norm_eq_abs,abs_of_nonneg (multilinearKakeyaFunction_nonneg k u T B x),
      abs_of_nonneg (multilinearKakeyaFunction_nonneg k u S B ((2*C+3)⁻¹ • x))]
    exact capsule_multilinear_dilate_le k b u B C δ hu hC hδ x
  exact hnorm.trans_eq (eLpNorm_inverse_dilation_rpow F hF p (by positivity))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mem_flatCylinder_iff_coordinates
#print axioms KakeyaTwoScale.isOpen_flatCylinder
#print axioms KakeyaTwoScale.volume_map_inverse_dilation
#print axioms KakeyaTwoScale.eLpNorm_inverse_dilation

#print axioms KakeyaTwoScale.eLpNorm_inverse_dilation_rpow
#print axioms KakeyaTwoScale.capsule_multilinear_norm_dilate_le
