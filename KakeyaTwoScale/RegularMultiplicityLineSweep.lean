module
public import KakeyaTwoScale.BoundedMultiplicityJacobian

@[expose] public section

open MeasureTheory Matrix Set
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

private theorem sweep_compact {m : ℕ} (F G : (Fin m → ℝ) → (Fin m → ℝ))
    (hF : Continuous F) (hG : Continuous G) {S : Set (Fin m → ℝ)} (hS : IsCompact S)
    (a L : ℝ) : IsCompact (differentiableLineSweep F G S a L) := by
  apply (hS.prod isCompact_Icc).image
  exact ((hF.comp continuous_fst).add (continuous_snd.smul (hG.comp continuous_fst))).prodMk continuous_snd

private theorem sweep_slice {m : ℕ} (F G : (Fin m → ℝ) → (Fin m → ℝ))
    (S : Set (Fin m → ℝ)) (a L t : ℝ) :
    (fun x => (x,t)) ⁻¹' differentiableLineSweep F G S a L =
      if t ∈ Icc a (a+L) then (fun y => F y+t • G y) '' S else ∅ := by
  ext x
  by_cases ht : t ∈ Icc a (a+L)
  · simp only [ite_eq_left ht, mem_preimage, differentiableLineSweep, mem_image, mem_prod,
      Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨y,s,⟨hy,hs⟩,he,hes⟩
      subst s
      exact ⟨y,hy,he⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y,t,⟨hy,ht⟩,he,rfl⟩
  · simp only [ite_eq_right ht, mem_empty_iff_false, iff_false, mem_preimage,
      differentiableLineSweep, mem_image, mem_prod, Prod.exists, Prod.mk.injEq]
    rintro ⟨y,s,⟨hy,hs⟩,he,hes⟩
    exact ht (hes ▸ hs)

/-- The actual swept Jacobian is bounded by N times the actual union volume,
assuming at most N regular preimages per time slice. Singular fibers are unrestricted. -/
theorem regularMultiplicityLineSweep_jacobian {m : ℕ}
    (F G : (Fin m → ℝ) → (Fin m → ℝ))
    (DF DG : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)))
    (hcDF : Continuous DF) (hcDG : Continuous DG)
    (hF : ∀ y, HasFDerivAt F (DF y) y) (hG : ∀ y, HasFDerivAt G (DG y) y)
    {S : Set (Fin m → ℝ)} (hS : IsCompact S) (a L : ℝ) (N : ℕ)
    (hmult : ∀ t ∈ Icc a (a+L), ∀ z,
      ({y | y∈S ∧ (DF y+t • DG y).det≠0 ∧ F y+t • G y=z} : Set (Fin m → ℝ)).encard ≤ N) :
    (∫⁻ t in Icc a (a+L), ∫⁻ y in S, ENNReal.ofReal |(DF y+t • DG y).det|) ≤
      (N : ℝ≥0∞) * (volume.prod volume) (differentiableLineSweep F G S a L) := by
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun y => (hF y).continuousAt
  have hcG : Continuous G := continuous_iff_continuousAt.mpr fun y => (hG y).continuousAt
  have hv : (volume.prod volume) (differentiableLineSweep F G S a L) =
      ∫⁻ t in Icc a (a+L), volume ((fun y => F y+t • G y) '' S) := by
    rw [Measure.prod_apply_symm (sweep_compact F G hcF hcG hS a L).measurableSet]
    simp_rw [sweep_slice]
    have hs (t : ℝ) : volume (if t ∈ Icc a (a+L) then
        (fun y => F y+t • G y) '' S else ∅) =
        (Icc a (a+L)).indicator (fun t => volume ((fun y => F y+t • G y) '' S)) t := by
      split_ifs with ht <;> simp [ht]
    simp_rw [hs]
    exact lintegral_indicator measurableSet_Icc _
  rw [hv, ← lintegral_const_mul' _ _ (by simp : (N : ℝ≥0∞) ≠ ∞)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact regular_fiber_jacobian_bound (fun y => F y+t • G y) (fun y => DF y+t • DG y)
    (hcDF.add (hcDG.const_smul t))
    (fun y => (hF y).add ((hG y).const_smul t)) hS N (hmult t ht)

private theorem clm_pencil_estimate {m : ℕ} (C : ℝ)
    (h : ∀ (A B : Matrix (Fin m) (Fin m) ℝ) (a L : ℝ), 0 < L →
      |Matrix.det B| * L^(m+1) ≤ C * ∫ t in a..(a+L), |Matrix.det (A+t • B)|)
    (A B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) (a L : ℝ) (hL : 0 < L) :
    |B.det| * L^(m+1) ≤ C * ∫ t in a..(a+L), |(A+t • B).det| := by
  have hp := h (LinearMap.toMatrix' A.toLinearMap) (LinearMap.toMatrix' B.toLinearMap) a L hL
  simpa only [← map_smul, ← map_add, LinearMap.det_toMatrix', ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul] using hp

/-- A genuine direction-volume/swept-volume inequality for differentiable
position and slope maps with continuous derivatives and bounded regular fibers in each time slice.
No Jacobian integral or volume comparison is assumed. -/
theorem regularMultiplicityLineSweep_direction_volume (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀
      (F G : (Fin m → ℝ) → (Fin m → ℝ))
      (DF DG : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ))),
      Continuous DF → Continuous DG →
      (∀ y, HasFDerivAt F (DF y) y) → (∀ y, HasFDerivAt G (DG y) y) →
      ∀ (S : Set (Fin m → ℝ)), IsCompact S → ∀ a L : ℝ, 0 < L →
      ∀ N : ℕ,
      (∀ t ∈ Icc a (a+L), ∀ z,
        ({y | y∈S ∧ (DF y+t • DG y).det≠0 ∧ F y+t • G y=z} : Set (Fin m → ℝ)).encard ≤ N) →
      volume (G '' S) * ENNReal.ofReal (L^(m+1)) ≤
        (ENNReal.ofReal C * N) * (volume.prod volume) (differentiableLineSweep F G S a L) := by
  obtain ⟨C,hC,h⟩ := determinant_pencil_integral m
  refine ⟨C,hC,?_⟩
  intro F G DF DG hcDF hcDG hF hG S hS a L hL N hmult
  have hpoint (y : Fin m → ℝ) :
      ENNReal.ofReal |(DG y).det| * ENNReal.ofReal (L^(m+1)) ≤
      ENNReal.ofReal C * ∫⁻ t in Icc a (a+L), ENNReal.ofReal |(DF y+t • DG y).det| := by
    have hc : Continuous (fun t : ℝ => |(DF y+t • DG y).det|) :=
      (ContinuousLinearMap.continuous_det.comp
        (continuous_const.add (continuous_id.smul continuous_const))).abs
    have hp := ENNReal.ofReal_le_ofReal (clm_pencil_estimate C h (DF y) (DG y) a L hL)
    rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul hC.le] at hp
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)] at hp
    exact hp
  have hj : AEMeasurable (fun z : (Fin m → ℝ) × ℝ =>
      ENNReal.ofReal |(DF z.1+z.2 • DG z.1).det|)
      ((volume.restrict S).prod (volume.restrict (Icc a (a+L)))) := by
    exact (ENNReal.continuous_ofReal.comp (ContinuousLinearMap.continuous_det.comp
      ((hcDF.comp continuous_fst).add (continuous_snd.smul (hcDG.comp continuous_fst)))).abs).measurable.aemeasurable
  calc
    volume (G '' S) * ENNReal.ofReal (L^(m+1)) ≤
        (∫⁻ y in S, ENNReal.ofReal |(DG y).det|) * ENNReal.ofReal (L^(m+1)) := by
      exact mul_le_mul (addHaar_image_le_lintegral_abs_det_fderiv volume hS.measurableSet
        (fun y _ => (hG y).hasFDerivWithinAt)) le_rfl zero_le zero_le
    _ = ∫⁻ y in S, ENNReal.ofReal |(DG y).det| * ENNReal.ofReal (L^(m+1)) := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y in S, ENNReal.ofReal C *
        ∫⁻ t in Icc a (a+L), ENNReal.ofReal |(DF y+t • DG y).det| := lintegral_mono hpoint
    _ = ENNReal.ofReal C * ∫⁻ t in Icc a (a+L),
        ∫⁻ y in S, ENNReal.ofReal |(DF y+t • DG y).det| := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hj]
    _ ≤ ENNReal.ofReal C * ((N : ℝ≥0∞) *
        (volume.prod volume) (differentiableLineSweep F G S a L)) :=
      mul_le_mul le_rfl (regularMultiplicityLineSweep_jacobian F G DF DG hcDF hcDG hF hG hS a L N hmult)
        zero_le zero_le
    _ = _ := by rw [mul_assoc]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.regularMultiplicityLineSweep_jacobian
#print axioms KakeyaTwoScale.regularMultiplicityLineSweep_direction_volume
