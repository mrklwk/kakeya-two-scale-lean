module
public import KakeyaTwoScale.ProgressionParameters
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def sampleCount (N : ℕ) (A : Set ℝ) (x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, A.indicator (fun _ => (1:ℝ)) (x+(i:ℝ)*y)

/-- Exact first moment in the progression sampling rectangle; translation
invariance and the containing interval supply the equality, not an assumption. -/
theorem sampleCount_inner_integral (N : ℕ) (hN : 0 < N)
    (A : Set ℝ) (hA : MeasurableSet A) (hsub : A ⊆ Set.Icc 0 1)
    (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) (1/(N:ℝ))) :
    (∫ x in Set.Icc (-1:ℝ) 1, sampleCount N A x y) = (N:ℝ)*volume.real A := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hid (i : ℕ) :
      (fun x : ℝ => A.indicator (fun _ => (1:ℝ)) (x+(i:ℝ)*y)) =
        ((fun x : ℝ => x+(i:ℝ)*y) ⁻¹' A).indicator (fun _ => (1:ℝ)) := by
    funext x
    classical
    by_cases hx : x+(i:ℝ)*y ∈ A <;> simp [Set.indicator, hx]
  have hint (i : ℕ) : IntegrableOn
      (fun x : ℝ => A.indicator (fun _ => (1:ℝ)) (x+(i:ℝ)*y)) (Set.Icc (-1:ℝ) 1) := by
    have hj : MeasurableSet ((fun x : ℝ => x+(i:ℝ)*y) ⁻¹' A) :=
      hA.preimage (measurable_id.add_const _)
    rw [hid]
    exact
      (integrable_const (1:ℝ) (μ := volume.restrict (Set.Icc (-1:ℝ) 1))).indicator hj
  unfold sampleCount
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have he (i : ℕ) (hi : i ∈ Finset.range N) :
      (∫ x in Set.Icc (-1:ℝ) 1,
        A.indicator (fun _ => (1:ℝ)) (x+(i:ℝ)*y)) = volume.real A := by
    have hiN : (i:ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hshift0 : 0 ≤ (i:ℝ)*y := mul_nonneg (by positivity) hy.1
    have hshift1 : (i:ℝ)*y ≤ 1 := by
      have hny := (le_div_iff₀ hNp).mp hy.2
      have hm := mul_le_mul_of_nonneg_right hiN hy.1
      nlinarith
    have hj : MeasurableSet ((fun x : ℝ => x+(i:ℝ)*y) ⁻¹' A) :=
      hA.preimage (measurable_id.add_const _)
    have hjsub : (fun x : ℝ => x+(i:ℝ)*y) ⁻¹' A ⊆ Set.Icc (-1:ℝ) 1 := by
      intro x hx
      have hh := hsub hx
      constructor <;> linarith [hh.1,hh.2]
    rw [hid]
    calc
      _ = (volume.restrict (Set.Icc (-1:ℝ) 1)).real
          ((fun x : ℝ => x+(i:ℝ)*y) ⁻¹' A) := by
        simpa using (integral_indicator_const (μ := volume.restrict (Set.Icc (-1:ℝ) 1)) (1:ℝ) hj)
      _ = _ := by
        rw [Measure.real, Measure.restrict_apply hj, Set.inter_eq_left.mpr hjsub,
          measure_preimage_add_right]
        rfl
  calc
    _ = ∑ _i ∈ Finset.range N, volume.real A := Finset.sum_congr rfl he
    _ = _ := by simp

 theorem sampleCount_rectangle_integral (N : ℕ) (hN : 0 < N)
    (A : Set ℝ) (hA : MeasurableSet A) (hsub : A ⊆ Set.Icc 0 1) :
    (∫ y in Set.Icc (0:ℝ) (1/(N:ℝ)),
      ∫ x in Set.Icc (-1:ℝ) 1, sampleCount N A x y) = volume.real A := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  calc
    _ = ∫ _y in Set.Icc (0:ℝ) (1/(N:ℝ)), (N:ℝ)*volume.real A := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact sampleCount_inner_integral N hN A hA hsub y hy
    _ = _ := by
      rw [setIntegral_const]
      simp only [Measure.real, Real.volume_Icc, sub_zero, smul_eq_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(N:ℝ))]
      field_simp
end KakeyaTwoScale
#print axioms KakeyaTwoScale.sampleCount_inner_integral
#print axioms KakeyaTwoScale.sampleCount_rectangle_integral
