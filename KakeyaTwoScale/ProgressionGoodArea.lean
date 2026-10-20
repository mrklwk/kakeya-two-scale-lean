module
public import KakeyaTwoScale.ProgressionSampling
public import KakeyaTwoScale.MeasureSelection
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

def samplingRectangle (N : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (1/(N:ℝ))

theorem sampleCount_eq_card (N : ℕ) (A : Set ℝ) (x y : ℝ) :
    sampleCount N A x y =
      (((Finset.range N).filter fun i : ℕ => x+(i:ℝ)*y ∈ A).card : ℝ) := by
  simp [sampleCount, Set.indicator]

theorem measurable_sampleCount (N : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable (fun p : ℝ × ℝ => sampleCount N A p.1 p.2) := by
  unfold sampleCount
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_const.indicator hA).comp
      (measurable_fst.add (measurable_const.mul measurable_snd))

theorem integrable_sampleCount (N : ℕ) {A : Set ℝ} (hA : MeasurableSet A)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun p : ℝ × ℝ => sampleCount N A p.1 p.2) μ := by
  have he : (fun p : ℝ × ℝ => sampleCount N A p.1 p.2) =
      membershipCount (Finset.range N)
        (fun i => (fun p : ℝ × ℝ => p.1+(i:ℝ)*p.2) ⁻¹' A) := by
    funext p
    simp [sampleCount_eq_card, membershipCount_eq_card]
  rw [he]
  exact integrable_membershipCount μ _ _ fun i _ =>
    hA.preimage (measurable_fst.add (measurable_const.mul measurable_snd))

theorem sampleCount_area_integral (N : ℕ) (hN : 0 < N)
    (A : Set ℝ) (hA : MeasurableSet A) (hsub : A ⊆ Set.Icc 0 1) :
    (∫ p in samplingRectangle N, sampleCount N A p.1 p.2) = volume.real A := by
  rw [samplingRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod_symm _ (integrable_sampleCount N hA _)]
  exact sampleCount_rectangle_integral N hN A hA hsub

/-- A first-moment estimate with all integrability obligations explicit. -/
theorem superlevel_measure_lower {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ)
    (hf : Measurable f) (hi : Integrable f μ) (M t : ℝ)
    (ht : 0 ≤ t) (hM : ∀ x, f x ≤ M) :
    (∫ x, f x ∂μ) ≤ t * μ.real Set.univ + M * μ.real {x | t ≤ f x} := by
  have hG : MeasurableSet {x | t ≤ f x} := measurableSet_le measurable_const hf
  have hI : Integrable (({x | t ≤ f x} : Set X).indicator (fun _ => M)) μ :=
    (integrable_const M).indicator hG
  calc
    _ ≤ ∫ x, t + ({x | t ≤ f x} : Set X).indicator (fun _ => M) x ∂μ := by
      apply integral_mono hi ((integrable_const t).add hI)
      intro x
      change f x ≤ t + _
      by_cases hx : t ≤ f x
      · simpa [Set.indicator, hx] using (le_add_of_nonneg_left ht : M ≤ t+M) |>.trans' (hM x)
      · simp only [Set.indicator, Set.mem_ofPred_eq, hx, ↓reduceIte, add_zero]
        exact le_of_lt (lt_of_not_ge hx)
    _ = _ := by
      rw [integral_add (integrable_const t) hI, integral_const, integral_indicator_const M hG]
      simp [smul_eq_mul, mul_comm]

def goodSamples (N : ℕ) (A : Set ℝ) (lam : ℝ) : Set (ℝ × ℝ) :=
  samplingRectangle N ∩ {p | lam*(N:ℝ)/4 ≤ sampleCount N A p.1 p.2}

theorem goodSamples_area_lower (N : ℕ) (hN : 0 < N)
    (A : Set ℝ) (hA : MeasurableSet A) (hsub : A ⊆ Set.Icc 0 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (hmass : lam ≤ volume.real A) :
    lam/(2*(N:ℝ)) ≤ volume.real (goodSamples N A lam) := by
  let μ : Measure (ℝ × ℝ) := volume.restrict (samplingRectangle N)
  have hrect : MeasurableSet (samplingRectangle N) := measurableSet_Icc.prod measurableSet_Icc
  have hfin : volume (samplingRectangle N) < ⊤ := by
    rw [samplingRectangle, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hfin⟩
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hu : μ.real Set.univ = 2/(N:ℝ) := by
    simp only [μ, Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [samplingRectangle, Measure.volume_eq_prod, Measure.prod_prod,
      ENNReal.toReal_mul, Real.volume_Icc, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1-(-1)),
      ENNReal.toReal_ofReal (by simp only [sub_zero]; exact le_of_lt (one_div_pos.mpr hNp) : (0:ℝ) ≤ 1/(N:ℝ)-0)]
    ring
  have hg : μ.real {p : ℝ × ℝ | lam*(N:ℝ)/4 ≤ sampleCount N A p.1 p.2} =
      volume.real (goodSamples N A lam) := by
    rw [Measure.real, Measure.restrict_apply (measurableSet_le measurable_const
      (measurable_sampleCount N hA))]
    simp [goodSamples, Measure.real, Set.inter_comm]
  have hb := superlevel_measure_lower μ (fun p => sampleCount N A p.1 p.2)
    (measurable_sampleCount N hA) (integrable_sampleCount N hA μ)
    (N:ℝ) (lam*(N:ℝ)/4) (by positivity) (fun p => by
      rw [sampleCount_eq_card]
      exact_mod_cast (le_trans (Finset.card_filter_le (Finset.range N) _) (by simp : (Finset.range N).card ≤ N)))
  change (∫ p in samplingRectangle N, sampleCount N A p.1 p.2) ≤ _ at hb
  rw [sampleCount_area_integral N hN A hA hsub, hu, hg] at hb
  apply (div_le_iff₀ (by positivity : 0 < 2*(N:ℝ))).mpr
  have hc : lam*(N:ℝ)/4*(2/(N:ℝ)) = lam/2 := by field_simp; ring
  rw [hc] at hb
  nlinarith
end KakeyaTwoScale
#print axioms KakeyaTwoScale.goodSamples_area_lower
