module
public import KakeyaTwoScale.FiniteRootIntervals

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- Padding is clipped to the ACTUAL parent, including near its endpoints. -/
def paddedAxisInterval (L δ : ℝ) (a : ℝ × ℝ) : ℝ × ℝ :=
  (max 0 (a.1-δ), min L (a.2+δ))

theorem padded_axis_bounds {L δ : ℝ} (hδ : 0 < δ) (hL : δ ≤ L)
    {a : ℝ × ℝ} (ha : 0 ≤ a.1 ∧ a.1 ≤ a.2 ∧ a.2 ≤ L) :
    0 ≤ (paddedAxisInterval L δ a).1 ∧
    (paddedAxisInterval L δ a).1 + δ ≤ (paddedAxisInterval L δ a).2 ∧
    (paddedAxisInterval L δ a).2 ≤ L := by
  dsimp [paddedAxisInterval]
  refine ⟨le_max_left _ _,?_,min_le_left _ _⟩
  by_cases hz : 0 ≤ a.1-δ
  · rw [max_eq_right hz]
    apply le_min <;> linarith [ha.2.1,ha.2.2]
  · rw [max_eq_left (le_of_not_ge hz)]
    apply le_min <;> linarith [ha.1,ha.2.1]

theorem padded_axis_incidence {L δ t : ℝ} (hδ : 0 < δ)
    {a : ℝ × ℝ} (ht : t ∈ Icc a.1 a.2) (hp : t ∈ Ioo (0:ℝ) L) :
    t ∈ Ioo (paddedAxisInterval L δ a).1 (paddedAxisInterval L δ a).2 := by
  dsimp [paddedAxisInterval]
  constructor
  · exact max_lt hp.1 (by linarith [ht.1])
  · exact lt_min hp.2 (by linarith [ht.2])

/-- Padding does not create an axial point farther than delta from its
original closed interval. This survives exact-union merging. -/
theorem padded_axis_near_source {L δ t : ℝ} {a : ℝ × ℝ}
    (hδ : 0 ≤ δ) (ha : a.1 ≤ a.2)
    (ht : t ∈ Icc (paddedAxisInterval L δ a).1 (paddedAxisInterval L δ a).2) :
    ∃ s ∈ Icc a.1 a.2, |t-s| ≤ δ := by
  dsimp [paddedAxisInterval] at ht
  have hlo := (le_max_right 0 (a.1-δ)).trans ht.1
  have hhi := ht.2.trans (min_le_right L (a.2+δ))
  refine ⟨max a.1 (min t a.2),?_,?_⟩
  · exact ⟨le_max_left _ _,max_le ha (min_le_right _ _)⟩
  · by_cases hta : t ≤ a.1
    · rw [max_eq_left ((min_le_left t a.2).trans hta)]
      rw [abs_of_nonpos (by linarith)]
      linarith
    · by_cases htb : t ≤ a.2
      · rw [min_eq_left htb,max_eq_right (le_of_not_ge hta),sub_self,abs_zero]
        linarith
      · rw [min_eq_right (le_of_not_ge htb),max_eq_right ha]
        rw [abs_of_nonneg (by linarith)]
        linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.padded_axis_bounds
#print axioms KakeyaTwoScale.padded_axis_incidence
#print axioms KakeyaTwoScale.padded_axis_near_source
