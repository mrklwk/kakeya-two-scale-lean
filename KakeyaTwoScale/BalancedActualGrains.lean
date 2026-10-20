module
public import KakeyaTwoScale.ActualGrainStatistics

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def grainRecordCount {T C G P : Type*} [DecidableEq T] [DecidableEq G] [DecidableEq P]
    (Y : Finset T) (cube : T → C) (grain : C → G) (piece : T → P) (g : G) : ℕ :=
  ((Y.filter fun y => grain (cube y)=g).image piece).card

theorem represented_record_count_bounds {T C G P : Type*}
    [DecidableEq T] [DecidableEq G] [DecidableEq P]
    (Y : Finset T) (cube : T → C) (grain : C → G) (piece : T → P)
    {g : G} (hg : g ∈ Y.image (grain ∘ cube)) :
    1 ≤ grainRecordCount Y cube grain piece g ∧ grainRecordCount Y cube grain piece g ≤ Y.card := by
  obtain ⟨y,hy,hg⟩ := Finset.mem_image.mp hg
  constructor
  · exact Finset.card_pos.mpr ⟨piece y,Finset.mem_image_of_mem piece (Finset.mem_filter.mpr ⟨hy,hg⟩)⟩
  · exact Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))

/-- The actual mass and the k actual chosen-record counts; no numerical
statistics are supplied by the caller. -/
def actualGrainQuantity {T C G P : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq G] [DecidableEq P] {k : ℕ}
    (Y : Finset T) (cube : T → C) (cubes : Finset C) (grain : C → G)
    (piece : T → Fin k → P) (p : ℝ) (g : G) : Fin (k+1) → ℝ :=
  Fin.cases (tupleCubeMass (Y.filter fun y => grain (cube y)=g) cube cubes p)
    (fun j => (grainRecordCount Y cube grain (fun y => piece y j) g:ℝ))

/-- Construct simultaneous balance on represented grains for the actual mass
and every actual family count. Whole-grain selection preserves chosen records;
the fixed bin range can be chosen from the initial tuple cardinality. -/
theorem balanced_actual_grains {T C G P : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq G] [DecidableEq P] {k B : ℕ}
    (Y : Finset T) (cube : T → C) (cubes : Finset C) (grain : C → G)
    (piece : T → Fin k → P) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hcubes : ∀ y ∈ Y, cube y ∈ cubes) (hbound : (Y.card:ℝ) ≤ (2:ℝ)^B) :
    ∃ (band : Fin (k+1) → Fin (B+1)) (R : Finset G), R ⊆ Y.image (grain ∘ cube) ∧
      tupleCubeMass Y cube cubes p / (((B+1)^(k+1):ℕ):ℝ) ≤
        tupleCubeMass (Y.filter fun y => grain (cube y) ∈ R) cube cubes p ∧
      (∀ g ∈ R, ∀ j, (2:ℝ)^(band j).val ≤ actualGrainQuantity Y cube cubes grain piece p g j ∧
        actualGrainQuantity Y cube cubes grain piece p g j < (2:ℝ)^((band j).val+1)) ∧
      (∀ g ∈ R, ∀ j,
        grainRecordCount (Y.filter fun y => grain (cube y) ∈ R) cube grain (fun y => piece y j) g =
          grainRecordCount Y cube grain (fun y => piece y j) g) := by
  classical
  let S := Y.image (grain ∘ cube)
  have hquantity : ∀ g ∈ S, ∀ j,
      1 ≤ actualGrainQuantity Y cube cubes grain piece p g j ∧
        actualGrainQuantity Y cube cubes grain piece p g j ≤ (2:ℝ)^B := by
    intro g hg j
    refine Fin.cases ?_ (fun j => ?_) j
    · have hh := represented_grain_mass_bounds Y cube cubes grain hcubes hp hp1 hg
      exact ⟨hh.1,hh.2.trans hbound⟩
    · simp only [actualGrainQuantity,Fin.cases_succ]
      have hh := represented_record_count_bounds Y cube grain (fun y => piece y j) hg
      exact ⟨by exact_mod_cast hh.1,(show (grainRecordCount Y cube grain (fun y => piece y j) g:ℝ) ≤ Y.card by exact_mod_cast hh.2).trans hbound⟩
  obtain ⟨band,R,hRS,hmass,hbands⟩ := joint_weighted_grain_bands S
    (actualGrainQuantity Y cube cubes grain piece p)
    (fun g => tupleCubeMass (Y.filter fun y => grain (cube y)=g) cube cubes p) hquantity
  have hfull : Y.filter (fun y => grain (cube y) ∈ S)=Y := by
    apply Finset.filter_eq_self.mpr
    intro y hy
    exact Finset.mem_image_of_mem (grain ∘ cube) hy
  rw [← grain_subset_mass Y cube cubes grain S hp,hfull,← grain_subset_mass Y cube cubes grain R hp] at hmass
  refine ⟨band,R,hRS,hmass,hbands,?_⟩
  intro g hg j
  unfold grainRecordCount
  rw [retained_grain_records Y cube grain (fun y => piece y j) R hg]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.represented_record_count_bounds
#print axioms KakeyaTwoScale.balanced_actual_grains
