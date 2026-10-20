module
public import KakeyaTwoScale.DeterminantPencilIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Algebra.Group.Matrix

@[expose] public section

open MeasureTheory Matrix Set
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual union of the segments y ↦ ((A+tB)y,t), with y in S. -/
def affineLineSweep {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (S : Set (Fin m → ℝ)) (a L : ℝ) : Set ((Fin m → ℝ) × ℝ) :=
  (fun z : (Fin m → ℝ) × ℝ => ((A + z.2 • B).mulVec z.1, z.2)) '' (S ×ˢ Icc a (a+L))

/-- The swept union is compact, so its volume is measurable and finite. -/
theorem affineLineSweep_isCompact {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    {S : Set (Fin m → ℝ)} (hS : IsCompact S) (a L : ℝ) :
    IsCompact (affineLineSweep A B S a L) := by
  apply (hS.prod isCompact_Icc).image
  apply Continuous.prodMk _ continuous_snd
  apply continuous_pi
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

private theorem affineLineSweep_slice {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (S : Set (Fin m → ℝ)) (a L t : ℝ) :
    (fun x => (x,t)) ⁻¹' affineLineSweep A B S a L =
      if t ∈ Icc a (a+L) then (Matrix.toLin' (A+t • B)) '' S else ∅ := by
  ext x
  by_cases ht : t ∈ Icc a (a+L)
  · simp only [ite_eq_left ht, mem_preimage, affineLineSweep, mem_image, mem_prod,
      Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨y,s,⟨hy,hs⟩,he,hes⟩
      subst s
      exact ⟨y,hy,he⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y,t,⟨hy,ht⟩,he,rfl⟩
  · simp only [ite_eq_right ht, mem_empty_iff_false, iff_false, mem_preimage,
      affineLineSweep, mem_image, mem_prod, Prod.exists, Prod.mk.injEq]
    rintro ⟨y,s,⟨hy,hs⟩,he,hes⟩
    exact ht (hes ▸ hs)

/-- Exact Tonelli slice formula for an actual affine line union. Singular slices
are covered by the Haar image theorem, without a nonsingularity assumption. -/
theorem affineLineSweep_volume {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    {S : Set (Fin m → ℝ)} (hS : IsCompact S) (a L : ℝ) :
    (volume.prod volume) (affineLineSweep A B S a L) =
      (∫⁻ t in Icc a (a+L), ENNReal.ofReal |Matrix.det (A+t • B)|) * volume S := by
  rw [Measure.prod_apply_symm (affineLineSweep_isCompact A B hS a L).measurableSet]
  simp_rw [affineLineSweep_slice]
  have hs (t : ℝ) : volume (if t ∈ Icc a (a+L) then
      Matrix.toLin' (A+t • B) '' S else ∅) =
      (Icc a (a+L)).indicator (fun t => ENNReal.ofReal |Matrix.det (A+t • B)| * volume S) t := by
    split_ifs with ht
    · rw [Set.indicator_of_mem ht, Measure.addHaar_image_linearMap, LinearMap.det_toLin']
    · simp [ht]
  simp_rw [hs]
  rw [lintegral_indicator measurableSet_Icc, lintegral_mul_const]
  exact (ENNReal.continuous_ofReal.comp ((continuous_const.add (continuous_id.smul continuous_const)).matrix_det.abs)).measurable

/-- Exact real-volume formula, with all measurability and finiteness derived
from the compact parameter set. -/
theorem affineLineSweep_real_volume {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    {S : Set (Fin m → ℝ)} (hS : IsCompact S) (a L : ℝ) (hL : 0 ≤ L) :
    (volume.prod volume).real (affineLineSweep A B S a L) =
      (∫ t in a..(a+L), |Matrix.det (A+t • B)|) * volume.real S := by
  rw [measureReal_def, affineLineSweep_volume A B hS, ENNReal.toReal_mul]
  congr 1
  rw [← integral_toReal]
  · simp_rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  · exact (ENNReal.continuous_ofReal.comp
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det.abs).measurable.aemeasurable
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- Direction-volume forces actual swept line-union volume for affine
position/direction parametrizations. The constant depends only on dimension. -/
theorem affineLineSweep_direction_volume (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : Matrix (Fin m) (Fin m) ℝ)
      (S : Set (Fin m → ℝ)), IsCompact S → ∀ a L : ℝ, 0 < L →
      volume.real (Matrix.toLin' B '' S) * L^(m+1) ≤
        C * (volume.prod volume).real (affineLineSweep A B S a L) := by
  obtain ⟨C,hC,h⟩ := determinant_pencil_integral m
  refine ⟨C,hC,?_⟩
  intro A B S hS a L hL
  rw [affineLineSweep_real_volume A B hS a L hL.le]
  have hdir : volume.real (Matrix.toLin' B '' S) = |Matrix.det B| * volume.real S := by
    rw [measureReal_def, Measure.addHaar_image_linearMap, LinearMap.det_toLin', ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)]
    rfl
  rw [hdir]
  nlinarith [mul_le_mul_of_nonneg_right (h A B a L hL) (measureReal_nonneg (μ := volume) (s := S))]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.affineLineSweep_isCompact
#print axioms KakeyaTwoScale.affineLineSweep_volume

#print axioms KakeyaTwoScale.affineLineSweep_real_volume
#print axioms KakeyaTwoScale.affineLineSweep_direction_volume
