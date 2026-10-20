module
public import KakeyaTwoScale.ZahlContract
public import KakeyaTwoScale.CapsuleCylinder

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Pointwise containment transports the complete ordered-tuple function,
without a transversality assumption or a loss depending on family size. -/
theorem multilinearKakeyaFunction_le_of_membership {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T S : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ)
    (x y : EuclideanSpace ℝ (Fin n))
    (hsub : ∀ j, x ∈ T j → y ∈ S j) :
    multilinearKakeyaFunction k u T B x ≤ multilinearKakeyaFunction k u S B y := by
  unfold multilinearKakeyaFunction
  apply Real.rpow_le_rpow
  · apply Finset.sum_nonneg
    intro f _
    apply mul_nonneg (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
    exact Finset.prod_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)
  · apply Finset.sum_le_sum
    intro f _
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
    apply Finset.prod_le_prod₀
    · intro i _
      exact Set.indicator_nonneg (fun _ _ => by norm_num) x
    · intro i _
      by_cases hx : x ∈ T (f i)
      · simp [Set.indicator_of_mem hx,Set.indicator_of_mem (hsub (f i) hx)]
      · rw [Set.indicator_of_notMem hx]
        exact Set.indicator_nonneg (fun _ _ => by norm_num) y
  · positivity

/-- Norm monotonicity uses the genuine extended-real norm, including its
infinite case. Only the smaller function's measurability is required. -/
theorem multilinearKakeyaFunction_norm_mono {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T S : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ) (p : ℝ≥0∞)
    (hT : ∀ j, MeasurableSet (T j)) (hsub : ∀ j, T j ⊆ S j) :
    eLpNorm (multilinearKakeyaFunction k u T B) p volume ≤
      eLpNorm (multilinearKakeyaFunction k u S B) p volume := by
  apply eLpNorm_mono_ae (measurable_multilinearKakeyaFunction k u T B hT).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simp only [Real.norm_eq_abs,abs_of_nonneg (multilinearKakeyaFunction_nonneg k u T B x),
      abs_of_nonneg (multilinearKakeyaFunction_nonneg k u S B x)]
    exact multilinearKakeyaFunction_le_of_membership k u T S B x x (fun j hx => hsub j hx)

/-- Actual capsule/cylinder normalization transports the full multilinear
function pointwise, including endpoint caps. Analytic dilation and the
cylinder estimate remain separate obligations. -/
theorem capsule_multilinear_dilate_le {n N : ℕ} (k : ℕ)
    (b u : Fin N → EuclideanSpace ℝ (Fin n)) (B C δ : ℝ)
    (hu : ∀ j, ‖u j‖=1) (hC : 0 ≤ C) (hδ : δ ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    multilinearKakeyaFunction k u (fun j => euclideanTube (b j) (u j) (C*δ)) B x ≤
      multilinearKakeyaFunction k u (fun j => flatCylinder
        ((2*C+3)⁻¹ • (b j-(C*δ) • u j)) (u j) 1 (C*δ/(2*C+3))) B ((2*C+3)⁻¹ • x) := by
  apply multilinearKakeyaFunction_le_of_membership
  intro j hx
  exact capsule_dilate_into_unit_cylinder (b j) (u j) x C δ (hu j) hC hδ hx

end KakeyaTwoScale
#print axioms KakeyaTwoScale.multilinearKakeyaFunction_le_of_membership
#print axioms KakeyaTwoScale.multilinearKakeyaFunction_norm_mono
#print axioms KakeyaTwoScale.capsule_multilinear_dilate_le
