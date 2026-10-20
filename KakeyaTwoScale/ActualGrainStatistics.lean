module
public import KakeyaTwoScale.JointGrainBalancing

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem tuple_mass_le_card {T C : Type*} [DecidableEq T] [DecidableEq C]
    (Y : Finset T) (cube : T → C) (cubes : Finset C)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : tupleCubeMass Y cube cubes p ≤ Y.card := by
  have hpoint (q : C) : (ParentLevel.capacity Y cube q:ℝ)^p ≤ ParentLevel.capacity Y cube q := by
    by_cases hzero : ParentLevel.capacity Y cube q=0
    · simp [hzero,Real.zero_rpow hp.ne']
    · exact Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ ParentLevel.capacity Y cube q by omega)) hp1
  have he := Finset.sum_card_fiberwise_eq_card_filter Y cubes cube
  have he' : (∑ q ∈ cubes, (ParentLevel.capacity Y cube q:ℝ)) =
      ((Y.filter fun y => cube y ∈ cubes).card:ℝ) := by exact_mod_cast he
  exact (Finset.sum_le_sum (fun q _ => hpoint q)).trans
    (he'.le.trans (by exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun y => cube y ∈ cubes) Y)))

theorem tuple_mass_one_le {T C : Type*} [DecidableEq T] [DecidableEq C]
    (Y : Finset T) (cube : T → C) (cubes : Finset C)
    {p : ℝ} (hp : 0 ≤ p) {y : T} (hy : y ∈ Y) (hq : cube y ∈ cubes) :
    1 ≤ tupleCubeMass Y cube cubes p := by
  have hf : 1 ≤ ParentLevel.capacity Y cube (cube y) := by
    exact Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,rfl⟩⟩
  have hh := Real.one_le_rpow (show (1:ℝ) ≤ ParentLevel.capacity Y cube (cube y) by exact_mod_cast hf) hp
  exact hh.trans (Finset.single_le_sum (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hq)

/-- Actual positive mass statistics on represented grains have a fixed range
controlled by the initial tuple cardinality; empty cube labels are excluded. -/
theorem represented_grain_mass_bounds {T C G : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq G]
    (Y : Finset T) (cube : T → C) (cubes : Finset C) (grain : C → G)
    (hcubes : ∀ y ∈ Y, cube y ∈ cubes) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    {g : G} (hg : g ∈ Y.image (grain ∘ cube)) :
    1 ≤ tupleCubeMass (Y.filter fun y => grain (cube y)=g) cube cubes p ∧
      tupleCubeMass (Y.filter fun y => grain (cube y)=g) cube cubes p ≤ Y.card := by
  obtain ⟨y,hy,hg⟩ := Finset.mem_image.mp hg
  constructor
  · exact tuple_mass_one_le _ cube cubes hp.le (Finset.mem_filter.mpr ⟨hy,hg⟩) (hcubes y hy)
  · exact (tuple_mass_le_card _ cube cubes hp hp1).trans
      (by exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun y => grain (cube y)=g) Y))

/-- Whole-grain selection preserves the actual chosen-record image inside
retained grains. This prevents an untracked retrimming from breaking balance. -/
theorem retained_grain_records {T C G P : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq G] [DecidableEq P]
    (Y : Finset T) (cube : T → C) (grain : C → G) (piece : T → P)
    (R : Finset G) {g : G} (hg : g ∈ R) :
    (((Y.filter fun y => grain (cube y) ∈ R).filter fun y => grain (cube y)=g).image piece) =
      ((Y.filter fun y => grain (cube y)=g).image piece) := by
  congr 1
  ext y
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · intro h
    exact ⟨⟨h.1,by simpa only [h.2] using hg⟩,h.2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tuple_mass_le_card
#print axioms KakeyaTwoScale.tuple_mass_one_le
#print axioms KakeyaTwoScale.represented_grain_mass_bounds
#print axioms KakeyaTwoScale.retained_grain_records
