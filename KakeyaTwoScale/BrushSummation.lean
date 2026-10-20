module
public import KakeyaTwoScale.WeightedBrushCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Finite weighted pigeonholing with the exact number of angular bands.
The assignment is total on the original family; no weight is discarded. -/
theorem weighted_band_pigeonhole {J B : Type*} [DecidableEq B]
    (family : Finset J) (bands : Finset B) (hne : bands.Nonempty)
    (band : J → B) (w : J → ℝ) (hmap : ∀ j ∈ family, band j ∈ bands) :
    ∃ b ∈ bands, (∑ j ∈ family, w j) ≤
      (bands.card : ℝ) * ∑ j ∈ family.filter (fun j => band j = b), w j := by
  let W := fun b => ∑ j ∈ family.filter (fun j => band j = b), w j
  obtain ⟨b,hb,hmax⟩ := bands.exists_max_image W hne
  refine ⟨b,hb,?_⟩
  calc
    _ = ∑ b ∈ bands, W b := (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ _b ∈ bands, W b := Finset.sum_le_sum hmax
    _ = _ := by simp [W]

/-- The concave arithmetic volume bound becomes linear when the total weight
in each plane has a uniform cap. Includes zero-weight pieces. -/
theorem capped_weight_linearization (W C a : ℝ) (hW : 0 ≤ W)
    (hC : W ≤ C) (ha : a ≤ 1) : C^(a-1)*W ≤ W^a := by
  rcases eq_or_lt_of_le hW with he | hp
  · rw [← he, mul_zero]
    exact Real.rpow_nonneg (by norm_num) _
  · have hpow := Real.rpow_le_rpow_of_nonpos hp hC (by linarith : a-1 ≤ 0)
    calc
      _ ≤ W^(a-1)*W := mul_le_mul_of_nonneg_right hpow hW
      _ = W^(a-1)*W^(1:ℝ) := by rw [Real.rpow_one]
      _ = W^a := by rw [← Real.rpow_add hp]; congr 1; ring

/-- Sum arithmetic estimates on shortened plane pieces with bounded overlap.
The arithmetic lower bounds, the plane-weight cap, and the geometric overlap
bound remain explicit inputs; the summation itself is dependency closed. -/
theorem plane_piece_volume_lower {X P : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (planes : Finset P) (pieces : P → Set X) (W : P → ℝ)
    (c C a L total : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) (ha : a ≤ 1)
    (hm : ∀ p ∈ planes, MeasurableSet (pieces p))
    (hW : ∀ p ∈ planes, 0 ≤ W p) (hcap : ∀ p ∈ planes, W p ≤ C)
    (harith : ∀ p ∈ planes, c*(W p)^a ≤ μ.real (pieces p))
    (hoverlap : ∀ x, weightedOverlap planes pieces (fun _ => (1:ℝ)) x ≤ L)
    (htotal : total ≤ ∑ p ∈ planes, W p) :
    c*C^(a-1)*total ≤ L*μ.real (⋃ p ∈ planes, pieces p) := by
  have hCn : 0 ≤ C^(a-1) := Real.rpow_nonneg hC _
  calc
    _ ≤ c*C^(a-1)*(∑ p ∈ planes, W p) :=
      mul_le_mul_of_nonneg_left htotal (mul_nonneg hc hCn)
    _ = ∑ p ∈ planes, c*(C^(a-1)*W p) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ ∑ p ∈ planes, μ.real (pieces p) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (mul_le_mul_of_nonneg_left
        (capped_weight_linearization (W p) C a (hW p hp) (hcap p hp) ha) hc).trans (harith p hp)
    _ ≤ _ := by simpa using weighted_union_volume μ planes pieces (fun _ => (1:ℝ)) L hm hoverlap
end KakeyaTwoScale
#print axioms KakeyaTwoScale.weighted_band_pigeonhole
#print axioms KakeyaTwoScale.capped_weight_linearization
#print axioms KakeyaTwoScale.plane_piece_volume_lower
