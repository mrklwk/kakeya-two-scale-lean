module
public import KakeyaTwoScale.ParentLevel
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The actual nonlinear objective on a fixed finite set of cube labels.
For a selected subset of original tuples and p>0, absent fibers contribute zero. -/
def tupleCubeMass {T Q : Type*} [DecidableEq Q]
    (Y : Finset T) (cube : T → Q) (cubes : Finset Q) (p : ℝ) : ℝ :=
  ∑ q ∈ cubes, (ParentLevel.capacity Y cube q : ℝ)^p

theorem finite_rpow_subadd {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : ∀ i ∈ S, 0 ≤ a i) :
    (∑ i ∈ S, a i)^p ≤ ∑ i ∈ S, (a i)^p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp.ne']
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (Real.rpow_add_le_add_rpow (ha i (by simp))
      (Finset.sum_nonneg fun j hj => ha j (by simp [hj])) hp.le hp1).trans
      (add_le_add le_rfl (ih (fun j hj => ha j (by simp [hj]))))

/-- Splitting ORIGINAL tuples into actual colors increases total concave
cube mass. No retained-mass premise or Cartesian-product hypothesis is used. -/
theorem tuple_colors_mass {T Q C : Type*} [DecidableEq T] [DecidableEq Q] [DecidableEq C]
    (Y : Finset T) (cube : T → Q) (cubes : Finset Q) (colors : Finset C)
    (color : T → C) (hcolor : ∀ y ∈ Y, color y ∈ colors)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    tupleCubeMass Y cube cubes p ≤
      ∑ c ∈ colors, tupleCubeMass (Y.filter fun y => color y=c) cube cubes p := by
  unfold tupleCubeMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro q hq
  have he : ∑ c ∈ colors, ParentLevel.capacity (Y.filter fun y => color y=c) cube q =
      ParentLevel.capacity Y cube q := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s:=Y.filter fun y => cube y=q) (t:=colors) (f:=color)
      (fun y hy => hcolor y (Finset.mem_filter.mp hy).1)
    simpa only [ParentLevel.capacity,Finset.filter_filter,and_comm] using h.symm
  have he' : (∑ c ∈ colors, (ParentLevel.capacity (Y.filter fun y => color y=c) cube q:ℝ)) =
      (ParentLevel.capacity Y cube q : ℝ) := by exact_mod_cast he
  rw [← he']
  exact finite_rpow_subadd colors _ hp hp1 (fun _ _ => Nat.cast_nonneg _)

/-- Construct a single global color class with quantified nonlinear retention.
The retained relation is the literal filter of Y, using its NEW fiber counts. -/
theorem exists_tuple_color_mass {T Q C : Type*} [DecidableEq T] [DecidableEq Q] [DecidableEq C]
    (Y : Finset T) (cube : T → Q) (cubes : Finset Q) (colors : Finset C)
    (hc : colors.Nonempty) (color : T → C) (hcolor : ∀ y ∈ Y, color y ∈ colors)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ c ∈ colors, tupleCubeMass Y cube cubes p / colors.card ≤
      tupleCubeMass (Y.filter fun y => color y=c) cube cubes p := by
  have hpos : (0:ℝ) < colors.card := by exact_mod_cast Finset.card_pos.mpr hc
  have hsum : ∑ _c ∈ colors, tupleCubeMass Y cube cubes p / colors.card ≤
      ∑ c ∈ colors, tupleCubeMass (Y.filter fun y => color y=c) cube cubes p := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_div_cancel₀ _ hpos.ne'] using
      tuple_colors_mass Y cube cubes colors color hcolor hp hp1
  exact Finset.exists_le_of_sum_le hc hsum

/-- A label depending only on the cube preserves its complete original fiber.
Summing over all labels gives exact nonlinear mass conservation for p>0. -/
theorem cube_label_mass_eq {T Q C : Type*} [DecidableEq T] [DecidableEq Q] [DecidableEq C]
    (Y : Finset T) (cube : T → Q) (cubes : Finset Q) (label : Q → C)
    {p : ℝ} (hp : 0 < p) :
    (∑ c ∈ cubes.image label, tupleCubeMass (Y.filter fun y => label (cube y)=c) cube cubes p) =
      tupleCubeMass Y cube cubes p := by
  classical
  have hf (q : Q) (c : C) :
      ParentLevel.capacity (Y.filter fun y => label (cube y)=c) cube q =
        if label q=c then ParentLevel.capacity Y cube q else 0 := by
    unfold ParentLevel.capacity
    by_cases h : label q=c
    · rw [ite_eq_left h]
      congr 1
      ext y
      simp only [Finset.mem_filter]
      constructor
      · exact fun hy => ⟨hy.1.1,hy.2⟩
      · intro hy
        exact ⟨⟨hy.1,by simpa only [hy.2] using h⟩,hy.2⟩
    · rw [ite_eq_right h]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨⟨_,hc⟩,hq⟩ := Finset.mem_filter.mp hy |>.imp_left Finset.mem_filter.mp
      exact h (by simpa only [hq] using hc)
  unfold tupleCubeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [hf,Nat.cast_ite,Nat.cast_zero]
  simp_rw [ite_pow]
  simp [Real.zero_rpow hp.ne',Finset.mem_image_of_mem label hq]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_rpow_subadd
#print axioms KakeyaTwoScale.tuple_colors_mass
#print axioms KakeyaTwoScale.exists_tuple_color_mass
#print axioms KakeyaTwoScale.cube_label_mass_eq
