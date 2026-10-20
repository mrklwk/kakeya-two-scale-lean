module
public import Mathlib.Data.Finset.Max
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def rootNext (R : Finset ℝ) (L a : ℝ) : ℝ :=
  (insert L (R.filter (a < ·))).min' (Finset.insert_nonempty _ _)

theorem rootNext_mem (R : Finset ℝ) (L a : ℝ) :
    rootNext R L a = L ∨ rootNext R L a ∈ R ∧ a < rootNext R L a := by
  have h := Finset.min'_mem (insert L (R.filter (a < ·))) (Finset.insert_nonempty _ _)
  simpa only [rootNext,Finset.mem_insert,Finset.mem_filter] using h

theorem rootNext_bounds (R : Finset ℝ) (L a : ℝ) (ha : a < L) :
    a < rootNext R L a ∧ rootNext R L a ≤ L := by
  constructor
  · apply (Finset.lt_min'_iff _ _).mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ha
    · exact (Finset.mem_filter.mp hr).2
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem rootNext_le_root (R : Finset ℝ) (L a r : ℝ)
    (hr : r ∈ R) (har : a < r) : rootNext R L a ≤ r :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hr,har⟩))

theorem root_interval_free (R : Finset ℝ) (L a : ℝ) :
    ∀ t ∈ Ioo a (rootNext R L a), t ∉ R := by
  intro t ht hr
  exact (not_le_of_gt ht.2) (rootNext_le_root R L a t hr ht.1)

/-- Actual maximal root gaps are indexed by their left endpoint. Distinct
gaps are counted separately even when the ambient cell is revisited. -/
theorem root_intervals_cover (R : Finset ℝ) (L : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) L) (htr : t ∉ R) :
    ∃ a ∈ insert 0 R, t ∈ Ioo a (rootNext R L a) := by
  let S := insert 0 (R.filter (· < t))
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  let a := S.max' hS
  have ham : a ∈ S := Finset.max'_mem _ _
  have hat : a < t := by
    apply (Finset.max'_lt_iff _ _).mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ht.1
    · exact (Finset.mem_filter.mp hr).2
  have ha : a ∈ insert 0 R := by
    rcases Finset.mem_insert.mp ham with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mp h).1
  refine ⟨a,ha,hat,?_⟩
  have hab := (rootNext_bounds R L a (hat.trans ht.2)).1
  by_contra! hbt
  rcases rootNext_mem R L a with hb | ⟨hb,hba⟩
  · rw [hb] at hbt
    linarith [ht.2]
  · have hne : rootNext R L a ≠ t := fun h => htr (h ▸ hb)
    have hmem : rootNext R L a ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hb,lt_of_le_of_ne hbt hne⟩)
    have hle : rootNext R L a ≤ a := Finset.le_max' _ _ hmem
    linarith

theorem root_intervals_disjoint (R : Finset ℝ) (L : ℝ)
    (hR : ∀ r ∈ R, 0 < r) :
    PairwiseDisjoint (↑(insert 0 R) : Set ℝ) (fun a => Ioo a (rootNext R L a)) := by
  intro a ha b hb hne
  have hnonneg : ∀ r ∈ insert 0 R, 0 ≤ r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact le_rfl
    · exact (hR r hr).le
  wlog hab : a < b generalizing a b
  · exact (this hb ha hne.symm (lt_of_le_of_ne (not_lt.mp hab) hne.symm)).symm
  have hbR : b ∈ R := by
    rcases Finset.mem_insert.mp hb with hb0 | hbR
    · have hh := hnonneg a ha
      rw [hb0] at hab
      linarith
    · exact hbR
  have hnext := rootNext_le_root R L a b hbR hab
  apply Set.disjoint_left.mpr
  intro t ht₁ ht₂
  linarith [ht₁.2,ht₂.1]

/-- A zero-free interval containing a point of a gap cannot leave that gap.
This preserves the full long gap, using a short interval only as a certificate. -/
theorem root_interval_contains_interval (R : Finset ℝ) (L a s e t : ℝ)
    (ha : a ∈ insert 0 R) (hs : 0 ≤ s) (he : e ≤ L)
    (ht : t ∈ Ioo s e) (hgap : t ∈ Ioo a (rootNext R L a))
    (hfree : ∀ r ∈ Ioo s e, r ∉ R) :
    a ≤ s ∧ e ≤ rootNext R L a := by
  constructor
  · by_contra! h
    rcases Finset.mem_insert.mp ha with h0 | har
    · rw [h0] at h
      linarith
    · exact hfree a ⟨h,hgap.1.trans ht.2⟩ har
  · by_contra! h
    rcases rootNext_mem R L a with hL | ⟨hr,_⟩
    · rw [hL] at h
      linarith
    · exact hfree _ ⟨ht.1.trans hgap.2,h⟩ hr

/-- No loss of axial length at a cellular split: all gaps together fit inside
the original parent. This bounds arbitrary retained subfamilies by monotonicity. -/
theorem root_intervals_total_length (R : Finset ℝ) (L : ℝ) (hL : 0 < L)
    (hR : ∀ r ∈ R, r ∈ Ioo (0:ℝ) L) :
    (insert 0 R).sum (fun a => rootNext R L a - a) ≤ L := by
  have ha : ∀ a ∈ insert 0 R, 0 ≤ a ∧ a < L := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨le_rfl,hL⟩
    · exact ⟨(hR a ha).1.le,(hR a ha).2⟩
  have hvol := measureReal_biUnion_finset (μ:=volume)
    (root_intervals_disjoint R L (fun r hr => (hR r hr).1))
    (fun _ _ => measurableSet_Ioo) (fun _ _ => by simp [Real.volume_Ioo])
  have hsub : (⋃ a ∈ insert 0 R, Ioo a (rootNext R L a)) ⊆ Ioo (0:ℝ) L := by
    intro t ht
    obtain ⟨a,ha',ht⟩ := Set.mem_iUnion₂.mp ht
    exact ⟨lt_of_le_of_lt (ha a ha').1 ht.1,
      lt_of_lt_of_le ht.2 (rootNext_bounds R L a (ha a ha').2).2⟩
  have hm := measureReal_mono (μ:=volume) hsub (by simp [Real.volume_Ioo])
  rw [hvol,Real.volume_real_Ioo_of_le hL.le,sub_zero] at hm
  convert hm using 1
  apply Finset.sum_congr rfl
  intro a haa
  exact (Real.volume_real_Ioo_of_le (rootNext_bounds R L a (ha a haa).2).1.le).symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.root_intervals_cover
#print axioms KakeyaTwoScale.root_intervals_disjoint
#print axioms KakeyaTwoScale.root_intervals_total_length
#print axioms KakeyaTwoScale.root_interval_contains_interval
