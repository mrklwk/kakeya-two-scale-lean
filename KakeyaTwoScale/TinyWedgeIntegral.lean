module
public import KakeyaTwoScale.TinyWedgePointwise
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

theorem finite_indicator_multiplicity_rpow_le {X : Type*} {N : ℕ}
    (T : Fin N → Set X) {p : ℝ} (hp : 1 ≤ p) (x : X) :
    (∑ j, (T j).indicator (fun _ => (1 : ℝ)) x) ^ p ≤
      (N : ℝ) ^ (p - 1) * ∑ j, (T j).indicator (fun _ => (1 : ℝ)) x := by
  classical
  let m : ℝ := ∑ j, (T j).indicator (fun _ => (1 : ℝ)) x
  have hm : 0 ≤ m := Finset.sum_nonneg fun j _ =>
    Set.indicator_nonneg (fun _ _ => by norm_num) x
  have hmN : m ≤ N := by
    calc
      m ≤ ∑ _j : Fin N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hx : x ∈ T j <;> simp [hx]
      _ = N := by simp
  have he : m ^ p = m ^ (p - 1) * m := by
    simpa only [sub_add_cancel] using
      (Real.rpow_add_one' hm (show p - 1 + 1 ≠ 0 by linarith))
  change m ^ p ≤ _ * m
  rw [he]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm hmN (by linarith)) hm

/-- The tiny-wedge integral bound keeps actual cylinder/set volumes in
ENNReal. No finiteness or toReal conversion can erase an infinite integral. -/
theorem tinyWedgeSum_lintegral_le {n N k : ℕ} (hk : 0 < k)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ j, MeasurableSet (T j)) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {B η : ℝ} (hB : 1 < B) (hη : 0 ≤ η) :
    (∫⁻ x, ENNReal.ofReal ((tinyWedgeSum k u T B η x) ^
      (B / ((k : ℝ) * (B - 1)))) ∂μ) ≤
      ENNReal.ofReal (η ^ (1 / (B - 1)) * (N : ℝ) ^ (B / (B - 1) - 1)) *
        ∑ j, μ (T j) := by
  classical
  let C : ℝ := η ^ (1 / (B - 1)) * (N : ℝ) ^ (B / (B - 1) - 1)
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg hη _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hp : 1 ≤ B / (B - 1) := le_of_lt (zahl_holder_conjugacy hB).1
  have hpoint (x) : (tinyWedgeSum k u T B η x) ^ (B / ((k : ℝ) * (B - 1))) ≤
      C * ∑ j, (T j).indicator (fun _ => (1 : ℝ)) x := by
    exact (tinyWedgeSum_rpow_le hk u T hB hη x).trans
      (by simpa only [C, mul_assoc] using (mul_le_mul_of_nonneg_left
        (finite_indicator_multiplicity_rpow_le T hp x) (Real.rpow_nonneg hη (1 / (B - 1)))))
  have he (x) : ENNReal.ofReal (∑ j, (T j).indicator (fun _ => (1 : ℝ)) x) =
      ∑ j, (T j).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      Set.indicator_nonneg (fun _ _ => by norm_num) x)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hx : x ∈ T j <;> simp [hx]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal C * ∑ j, (T j).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [ENNReal.ofReal_mul hC, he x] using ENNReal.ofReal_le_ofReal (hpoint x)
    _ = ENNReal.ofReal C * ∑ j, μ (T j) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum _ (fun j _ => measurable_const.indicator (hT j))]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp [lintegral_indicator (hT j)]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_indicator_multiplicity_rpow_le
#print axioms KakeyaTwoScale.tinyWedgeSum_lintegral_le
