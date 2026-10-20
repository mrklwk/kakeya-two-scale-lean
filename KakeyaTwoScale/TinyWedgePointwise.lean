module
public import KakeyaTwoScale.ZahlContract
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Literal restriction of the ordered original tuples to wedges at most η.
Zero and repeated tuples are retained harmlessly, so no lower bound on a
nonzero wedge is assumed. -/
def tinyWedgeSum {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B η : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ f ∈ (Finset.univ.filter fun f : Fin k → Fin N =>
      tupleWedgeVolume (fun i => u (f i)) ≤ η),
    (tupleWedgeVolume (fun i => u (f i))) ^ ((k : ℝ) / B) *
      ∏ i, (T (f i)).indicator (fun _ => (1 : ℝ)) x

theorem tinyWedgeSum_nonneg {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (T) (B η : ℝ) (x) :
    0 ≤ tinyWedgeSum k u T B η x := by
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
    (Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)

/-- The small-wedge tail is bounded by the full multiplicity, uniformly in
the number and sizes of arbitrarily tiny positive wedge values. -/
theorem tinyWedgeSum_le {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    {B η : ℝ} (hB : 0 < B) (hη : 0 ≤ η) (x) :
    tinyWedgeSum k u T B η x ≤
      η ^ ((k : ℝ) / B) * (∑ j, (T j).indicator (fun _ => (1 : ℝ)) x) ^ k := by
  classical
  let a (j : Fin N) : ℝ := (T j).indicator (fun _ => (1 : ℝ)) x
  have ha (j) : 0 ≤ a j := Set.indicator_nonneg (fun _ _ => by norm_num) x
  let S := Finset.univ.filter fun f : Fin k → Fin N =>
    tupleWedgeVolume (fun i => u (f i)) ≤ η
  calc
    tinyWedgeSum k u T B η x ≤ ∑ f ∈ S, η ^ ((k : ℝ) / B) * ∏ i, a (f i) := by
      apply Finset.sum_le_sum
      intro f hf
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (tupleWedgeVolume_nonneg _) (Finset.mem_filter.mp hf).2
          (div_nonneg (Nat.cast_nonneg _) hB.le))
        (Finset.prod_nonneg fun i _ => ha (f i))
    _ ≤ ∑ f : Fin k → Fin N, η ^ ((k : ℝ) / B) * ∏ i, a (f i) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun f _ _ => mul_nonneg (Real.rpow_nonneg hη _)
          (Finset.prod_nonneg fun i _ => ha (f i)))
    _ = η ^ ((k : ℝ) / B) * (∑ j, a j) ^ k := by
      rw [← Finset.mul_sum, ← Fintype.sum_pow]

/-- The exact target integral exponent is β=B/(k(B−1)), rather than the
archive exponent 1/(k−1). -/
theorem tinyWedgeSum_rpow_le {n N k : ℕ} (hk : 0 < k)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n)))
    {B η : ℝ} (hB : 1 < B) (hη : 0 ≤ η) (x) :
    (tinyWedgeSum k u T B η x) ^ (B / ((k : ℝ) * (B - 1))) ≤
      η ^ (1 / (B - 1)) *
        (∑ j, (T j).indicator (fun _ => (1 : ℝ)) x) ^ (B / (B - 1)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hB0 : 0 < B := by linarith
  have hBm : 0 < B - 1 := by linarith
  have hm : 0 ≤ ∑ j, (T j).indicator (fun _ => (1 : ℝ)) x :=
    Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => by norm_num) x
  have h := Real.rpow_le_rpow (tinyWedgeSum_nonneg (k := k) u T B η x)
    (tinyWedgeSum_le (k := k) u T hB0 hη x)
    (show 0 ≤ B / ((k : ℝ) * (B - 1)) by positivity)
  rw [Real.mul_rpow (Real.rpow_nonneg hη _) (pow_nonneg hm _),
    ← Real.rpow_mul hη, ← Real.rpow_natCast_mul hm] at h
  have he₁ : (k : ℝ) / B * (B / ((k : ℝ) * (B - 1))) = 1 / (B - 1) := by
    field_simp
  have he₂ : (k : ℝ) * (B / ((k : ℝ) * (B - 1))) = B / (B - 1) := by
    field_simp
  simpa only [he₁, he₂] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tinyWedgeSum_le
#print axioms KakeyaTwoScale.tinyWedgeSum_rpow_le
