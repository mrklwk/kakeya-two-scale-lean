module
public import KakeyaTwoScale.ProgressionParameters
public import KakeyaTwoScale.MeasureSelection
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

def shortStepStrip (c : ℝ) : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) c

theorem volume_shortStepStrip {c : ℝ} (_hc : 0 ≤ c) :
    volume (shortStepStrip c) = ENNReal.ofReal c := by
  rw [shortStepStrip, Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Icc]

def separatedProgressionParameters (ell : ℕ) (A : Set ℝ) (c : ℝ) : Set (ℝ × ℝ) :=
  progressionParameters ell A \ shortStepStrip c

theorem measurableSet_separatedProgressionParameters (ell : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (c : ℝ) :
    MeasurableSet (separatedProgressionParameters ell A c) :=
  (measurableSet_progressionParameters ell hA).diff
    (measurableSet_Icc.prod measurableSet_Icc)

theorem separatedProgressionParameters_step {ell : ℕ} (hell : 2 ≤ ell)
    {A : Set ℝ} (hA : A ⊆ Set.Icc 0 1) {c : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ separatedProgressionParameters ell A c) : c < p.2 := by
  have hsq := progressionParameters_subset_unit_square hell hA hp.1
  have hpos := hp.1.1
  by_contra h
  apply hp.2
  exact ⟨⟨hsq.1.1,hsq.2.1⟩,⟨le_of_lt hpos,le_of_not_gt h⟩⟩

/-- Discarding steps at most c loses area at most c. -/
theorem separatedProgressionParameters_area_lower (ell : ℕ) (A : Set ℝ)
    {c : ℝ} (hc : 0 ≤ c) (harea : 2*c ≤ volume.real (progressionParameters ell A)) :
    c ≤ volume.real (separatedProgressionParameters ell A c) := by
  have hs : volume.real (shortStepStrip c) = c := by
    rw [Measure.real, volume_shortStepStrip hc, ENNReal.toReal_ofReal hc]
  have hf : volume (shortStepStrip c) ≠ ⊤ := by rw [volume_shortStepStrip hc]; finiteness
  have hb := le_measureReal_sdiff (μ := (volume : Measure (ℝ × ℝ)))
    (s₁ := progressionParameters ell A) (s₂ := shortStepStrip c) hf
  rw [hs] at hb
  change c ≤ volume.real (progressionParameters ell A \ shortStepStrip c)
  linarith
/-- A uniform positive area yields simultaneous heights for a positive
fraction of any nonempty finite family, with a uniform lower step bound. -/
theorem common_separated_progression {J : Type*} [DecidableEq J]
    (family : Finset J) (hne : family.Nonempty) (sets : J → Set ℝ)
    {ell : ℕ} (hell : 2 ≤ ell) {c : ℝ} (hc : 0 < c)
    (hm : ∀ j ∈ family, MeasurableSet (sets j))
    (hsub : ∀ j ∈ family, sets j ⊆ Set.Icc 0 1)
    (ha : ∀ j ∈ family, 2*c ≤ volume.real (progressionParameters ell (sets j))) :
    ∃ p : ℝ × ℝ, c < p.2 ∧ c*family.card ≤
      ((family.filter fun j => p ∈ progressionParameters ell (sets j)).card : ℝ) := by
  classical
  let U : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1
  let μ : Measure (ℝ × ℝ) := volume.restrict U
  have hU : volume U = 1 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    norm_num [Real.volume_Icc]
  let : IsProbabilityMeasure μ := ⟨by simp [μ, hU]⟩
  let S := fun j => separatedProgressionParameters ell (sets j) c
  have hS (j) (hj : j ∈ family) : S j ⊆ U := by
    intro p hp
    have hh := progressionParameters_subset_unit_square hell (hsub j hj) hp.1
    exact ⟨⟨hh.1.1,hh.2.1⟩,⟨hh.1.2,hh.2.2⟩⟩
  have hSm (j) (hj : j ∈ family) : MeasurableSet (S j) :=
    measurableSet_separatedProgressionParameters ell (hm j hj) c
  have hSa (j) (hj : j ∈ family) : c ≤ μ.real (S j) := by
    rw [Measure.real, Measure.restrict_apply (hSm j hj), Set.inter_eq_left.mpr (hS j hj)]
    exact separatedProgressionParameters_area_lower ell (sets j) hc.le (ha j hj)
  obtain ⟨p,hp⟩ := common_parameter_of_measure_lower μ family S c hSm hSa
  rw [membershipCount_eq_card] at hp
  have hpos : 0 < ((family.filter fun j => p ∈ S j).card : ℝ) :=
    lt_of_lt_of_le (mul_pos hc (by exact_mod_cast Finset.card_pos.mpr hne)) hp
  have hn : (family.filter fun j => p ∈ S j).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hpos)
  obtain ⟨j,hj⟩ := hn
  obtain ⟨hj,hpj⟩ := Finset.mem_filter.mp hj
  refine ⟨p,separatedProgressionParameters_step hell (hsub j hj) hpj,le_trans hp ?_⟩
  exact_mod_cast Finset.card_le_card (show
    (family.filter fun j => p ∈ S j) ⊆
      (family.filter fun j => p ∈ progressionParameters ell (sets j)) from by
    intro j hj
    obtain ⟨hj,hpj⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hj,hpj.1⟩)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.separatedProgressionParameters_area_lower
#print axioms KakeyaTwoScale.separatedProgressionParameters_step

#print axioms KakeyaTwoScale.common_separated_progression
