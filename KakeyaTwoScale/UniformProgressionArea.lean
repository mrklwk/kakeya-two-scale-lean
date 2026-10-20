module
public import KakeyaTwoScale.ProgressionGoodArea
public import KakeyaTwoScale.ProgressionFiniteUnion

@[expose] public section

open MeasureTheory
namespace KakeyaTwoScale
open Classical

/-- Removing the zero-step horizontal line does not change area. -/
theorem volume_goodSamples_le_densePositiveSamples (N : ℕ) (A : Set ℝ) (lam : ℝ) :
    volume (goodSamples N A lam) ≤ volume (densePositiveSamples N (lam/4) A) := by
  let line : Set (ℝ × ℝ) := Set.univ ×ˢ ({0} : Set ℝ)
  have hnull : volume line = 0 := by
    simp [line, Measure.volume_eq_prod, Measure.prod_prod]
  have hsub : goodSamples N A lam \ line ⊆ densePositiveSamples N (lam/4) A := by
    intro p hp
    have hnonneg : 0 ≤ p.2 := hp.1.1.2.1
    have hne : p.2 ≠ 0 := by
      intro he
      exact hp.2 (by simp [line, he])
    refine ⟨lt_of_le_of_ne hnonneg (Ne.symm hne), ?_⟩
    have hc := hp.1.2
    change lam*(N:ℝ)/4 ≤ sampleCount N A p.1 p.2 at hc
    rw [sampleCount_eq_card] at hc
    convert hc using 1
    ring
  calc
    volume (goodSamples N A lam) = volume (goodSamples N A lam \ line) :=
      (measure_sdiff_null hnull).symm
    _ ≤ _ := measure_mono hsub

/-- A uniform positive parameter area for measurable sets of mass at least lam.
The sampling size depends only on length and lam, through finite Szemerédi. -/
theorem uniform_progression_area (ell : ℕ) (hell : 2 ≤ ell)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ N : ℕ, 0 < N ∧ ∀ (A : Set ℝ), MeasurableSet A → A ⊆ Set.Icc 0 1 →
      lam ≤ volume.real A →
      lam/(2*(N:ℝ)^3) ≤ volume.real (progressionParameters ell A) := by
  obtain ⟨N,hN,hSz⟩ := finite_szemeredi ell (lam/4) (by positivity)
  refine ⟨N,hN,?_⟩
  intro A hA hsub hmass
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hfin : volume (progressionParameters ell A) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt
      (measure_mono (progressionParameters_subset_unit_square hell hsub)) measure_Icc_lt_top)
  have hbound := (volume_goodSamples_le_densePositiveSamples N A lam).trans
    (volume_densePositiveSamples_le hell (lam/4) hSz hA)
  have hboundR := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) hbound
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hboundR
  change volume.real (goodSamples N A lam) ≤
    (N:ℝ)^2 * volume.real (progressionParameters ell A) at hboundR
  have hlower := goodSamples_area_lower N hN A hA hsub lam hlam.le hmass
  have hmain := hlower.trans hboundR
  apply (div_le_iff₀ (by positivity : 0 < 2*(N:ℝ)^3)).mpr
  have hh := (div_le_iff₀ (by positivity : 0 < 2*(N:ℝ))).mp hmain
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.volume_goodSamples_le_densePositiveSamples
#print axioms KakeyaTwoScale.uniform_progression_area
