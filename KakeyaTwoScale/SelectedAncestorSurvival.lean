module
public import KakeyaTwoScale.JointGrainBalancing

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem tuple_mass_mono {T C : Type*} [DecidableEq T] [DecidableEq C]
    (Y Z : Finset T) (cube : T → C) (cubes : Finset C) (hZY : Z ⊆ Y)
    {p : ℝ} (hp : 0 ≤ p) : tupleCubeMass Z cube cubes p ≤ tupleCubeMass Y cube cubes p := by
  apply Finset.sum_le_sum
  intro q hq
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hZY)
  · exact hp

/-- Actual mass can charge only the ancestor grains represented by the
selected original tuples. This is a proved domination, not a survival premise. -/
theorem selected_mass_le_ancestor_mass {T C G : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq G]
    (Y Z : Finset T) (cube : T → C) (cubes : Finset C) (ancestor : C → G)
    (hZY : Z ⊆ Y) {p : ℝ} (hp : 0 < p) :
    tupleCubeMass Z cube cubes p ≤ ∑ g ∈ Z.image (ancestor ∘ cube),
      tupleCubeMass (Y.filter fun y => ancestor (cube y)=g) cube cubes p := by
  rw [← grain_subset_mass Y cube cubes ancestor (Z.image (ancestor ∘ cube)) hp]
  apply tuple_mass_mono _ _ cube cubes _ hp.le
  intro y hy
  exact Finset.mem_filter.mpr ⟨hZY hy,Finset.mem_image_of_mem (ancestor ∘ cube) hy⟩

/-- Retaining actual nonlinear tuple mass forces quantitative ancestor
cardinality survival when the OLD grain masses are upper balanced. Empty or
nonrepresented cube labels cannot inflate the counted survivor set. -/
theorem selected_ancestor_card_survival {T C G : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq G]
    (Y Z : Finset T) (cube : T → C) (cubes : Finset C) (ancestor : C → G)
    (hZY : Z ⊆ Y) {p A eta : ℝ} (hp : 0 < p)
    (hpos : 0 < tupleCubeMass Y cube cubes p)
    (hret : eta*tupleCubeMass Y cube cubes p ≤ tupleCubeMass Z cube cubes p)
    (hbalance : ∀ g ∈ Y.image (ancestor ∘ cube),
      tupleCubeMass (Y.filter fun y => ancestor (cube y)=g) cube cubes p ≤
        A*tupleCubeMass Y cube cubes p/((Y.image (ancestor ∘ cube)).card:ℝ)) :
    eta*((Y.image (ancestor ∘ cube)).card:ℝ) ≤ A*((Z.image (ancestor ∘ cube)).card:ℝ) := by
  have hYne : Y.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he,tupleCubeMass,ParentLevel.capacity,Finset.filter_empty,Finset.card_empty,
      Nat.cast_zero,Real.zero_rpow hp.ne',Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  have hh : (0:ℝ) < (Y.image (ancestor ∘ cube)).card := by exact_mod_cast Finset.card_pos.mpr (hYne.image _)
  have hsum := Finset.sum_le_sum (fun g (hg : g ∈ Z.image (ancestor ∘ cube)) =>
    hbalance g (Finset.image_subset_image hZY hg))
  have hle := hret.trans ((selected_mass_le_ancestor_mass Y Z cube cubes ancestor hZY hp).trans hsum)
  simp only [Finset.sum_const,nsmul_eq_mul] at hle
  have hmul := (le_div_iff₀ hh).mp (show eta*tupleCubeMass Y cube cubes p ≤
      (((Z.image (ancestor ∘ cube)).card:ℝ)*A*tupleCubeMass Y cube cubes p)/((Y.image (ancestor ∘ cube)).card:ℝ) by
    convert hle using 1
    ring)
  nlinarith

/-- A genuine parent map bounds represented parent count by represented child
count. This supplies the combinatorial part of the degree-floor estimate. -/
theorem represented_parent_card_le {T C G H : Type*}
    [DecidableEq T] [DecidableEq G] [DecidableEq H]
    (Z : Finset T) (cube : T → C) (parent : C → G) (child : C → H) (lift : H → G)
    (hlift : ∀ y ∈ Z, lift (child (cube y))=parent (cube y)) :
    (Z.image (parent ∘ cube)).card ≤ (Z.image (child ∘ cube)).card := by
  have he : Z.image (parent ∘ cube) = (Z.image (child ∘ cube)).image lift := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro y hy
    exact (hlift y hy).symm
  rw [he]
  exact Finset.card_image_le

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tuple_mass_mono
#print axioms KakeyaTwoScale.selected_mass_le_ancestor_mass
#print axioms KakeyaTwoScale.selected_ancestor_card_survival
#print axioms KakeyaTwoScale.represented_parent_card_le
