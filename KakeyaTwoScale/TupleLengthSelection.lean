module
public import KakeyaTwoScale.NonlinearTupleSelection

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A real length has an actual dyadic band, with an explicit finite budget. -/
theorem exists_length_band {δ l : ℝ} {B : ℕ} (hδ : 0 < δ)
    (hlo : δ ≤ l) (hhi : l ≤ δ * (2:ℝ)^B) :
    ∃ i : Fin (B+1), δ*(2:ℝ)^i.val ≤ l ∧ l < δ*(2:ℝ)^(i.val+1) := by
  let m := ⌊l/δ⌋₊
  have hratio : 1 ≤ l/δ := (le_div_iff₀ hδ).mpr (by simpa using hlo)
  have hm : 0 < m := Nat.floor_pos.mpr hratio
  have hf : (m:ℝ) ≤ l/δ := Nat.floor_le (by positivity)
  have hg : l/δ < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have hb : m ≤ 2^B := by
    have hh : (m:ℝ) ≤ (2:ℝ)^B := hf.trans ((div_le_iff₀ hδ).mpr (by nlinarith [hhi]))
    exact_mod_cast hh
  have hi := ParentLevel.log2_le_of_card_bound hb
  refine ⟨⟨m.log2,by omega⟩,?_,?_⟩
  · have hh : (2:ℝ)^m.log2 ≤ (m:ℝ) := by
      exact_mod_cast (Nat.le_log2 hm.ne').mp (le_refl m.log2)
    simpa only [mul_comm] using (le_div_iff₀ hδ).mp (hh.trans hf)
  · have hh : (m:ℝ)+1 ≤ (2:ℝ)^(m.log2+1) := by
      exact_mod_cast (Nat.log2_lt hm.ne').mp (Nat.lt_succ_self m.log2)
    have ht := (div_lt_iff₀ hδ).mp (hg.trans_le hh)
    simpa only [mul_comm] using ht

/-- Construct joint length bands by filtering original tuples. The nonlinear
objective uses the new fibers and loses at most (B+1)^k. Actual lengths are
kept, within a factor two in each family; no shortening is assumed. -/
theorem exists_joint_length_selection {T Q : Type*} [DecidableEq T] [DecidableEq Q]
    {k B : ℕ} (Y : Finset T) (cube : T → Q) (cubes : Finset Q)
    (length : T → Fin k → ℝ) {δ p : ℝ} (hδ : 0 < δ)
    (hlen : ∀ y ∈ Y, ∀ j, δ ≤ length y j ∧ length y j ≤ δ*(2:ℝ)^B)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ (band : Fin k → Fin (B+1)) (Z : Finset T), Z ⊆ Y ∧
      tupleCubeMass Y cube cubes p / ((B+1:ℕ)^k:ℕ) ≤ tupleCubeMass Z cube cubes p ∧
      ∀ y ∈ Z, ∀ j, δ*(2:ℝ)^(band j).val ≤ length y j ∧
        length y j < δ*(2:ℝ)^((band j).val+1) := by
  classical
  have hex : ∀ y, ∀ j : Fin k, ∃ i : Fin (B+1), y ∈ Y →
      δ*(2:ℝ)^i.val ≤ length y j ∧ length y j < δ*(2:ℝ)^(i.val+1) := by
    intro y j
    by_cases hy : y ∈ Y
    · obtain ⟨i,hi⟩ := exists_length_band hδ (hlen y hy j).1 (hlen y hy j).2
      exact ⟨i,fun _ => hi⟩
    · exact ⟨⟨0,by omega⟩,fun h => False.elim (hy h)⟩
  choose color hcolor using hex
  obtain ⟨band,_,hband⟩ := exists_tuple_color_mass Y cube cubes Finset.univ
    Finset.univ_nonempty color (by simp) hp hp1
  refine ⟨band,Y.filter (fun y => color y=band),Finset.filter_subset _ _,?_,?_⟩
  · simpa using hband
  · intro y hy j
    obtain ⟨hy,hc⟩ := Finset.mem_filter.mp hy
    simpa only [hc] using hcolor y j hy

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_length_band
#print axioms KakeyaTwoScale.exists_joint_length_selection
