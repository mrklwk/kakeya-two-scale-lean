module
public import KakeyaTwoScale.ActualBufferedStageSeed

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
attribute [local instance] Classical.propDecidable

variable {n k : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

def grainTuples (W : FrozenGeometryState n k T C O) (cube : T → C) (g : W.Grain) : Finset T := by
  classical
  exact W.tuples.filter fun y => W.grain (cube y)=g

def grainCubes (W : FrozenGeometryState n k T C O) (cube : T → C) (g : W.Grain) : Finset C :=
  (W.grainTuples cube g).image cube

omit [DecidableEq T] [DecidableEq C] in
theorem grainTuples_subset (W : FrozenGeometryState n k T C O) (cube : T → C) (g : W.Grain) :
    W.grainTuples cube g ⊆ W.tuples := Finset.filter_subset _ _

omit [DecidableEq T] [DecidableEq C] in
theorem grainTuples_nonempty (W : FrozenGeometryState n k T C O) (cube : T → C)
    {g : W.Grain} (hg : g ∈ W.grains cube) : (W.grainTuples cube g).Nonempty := by
  classical
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hg
  exact ⟨y,Finset.mem_filter.mpr ⟨hy,he⟩⟩

omit [DecidableEq T] in
theorem grainCubes_owner (W : FrozenGeometryState n k T C O) (cube : T → C)
    {g : W.Grain} {q : C} (hq : q ∈ W.grainCubes cube g) : W.grain q=g := by
  classical
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  exact (Finset.mem_filter.mp hy).2

omit [DecidableEq T] in
theorem grainCubes_active (W : FrozenGeometryState n k T C O) (cube : T → C)
    {g : W.Grain} {q : C} (hq : q ∈ W.grainCubes cube g) :
    1 ≤ ParentLevel.capacity (W.grainTuples cube g) cube q := by
  classical
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hq
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,he⟩⟩)

/-- The original frozen records, with a family tag and a constant local root.
No physical cutting or successor data are supplied. -/
abbrev localPhysical (W : FrozenGeometryState n k T C O) (cube : T → C)
    (g : W.Grain) (δ : ℝ) : CellularPhysicalFamily n k T O (Finset C) where
  Piece := Fin k × W.Piece
  parent y j := (j,W.parent y j)
  node _ := W.grainCubes cube g
  original t := W.original t.1 t.2
  base t := W.base t.1 t.2
  axis t := W.axis t.1 t.2
  length t := W.length δ t.1

omit [DecidableEq T] in
theorem localPhysical_valid (W : FrozenGeometryState n k T C O)
    (Y₀ : Finset T) (cube : T → C) (tube : T → Fin k → O)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (g : W.Grain) {δ : ℝ} {Lh : ℕ}
    (hδ : 0 < δ) (hv : W.Valid Y₀ cube tube Q δ) (hh : ∀ j, W.height j ≤ Lh) :
    (W.localPhysical cube g δ).Valid (W.grainTuples cube g) cube tube Q
      (fun _ => W.grainCubes cube g) δ (δ*2^Lh) := by
  classical
  let : DecidableEq (Fin k × W.Piece) := Classical.decEq _
  refine ⟨fun t => hv.2.1 t.1 t.2,?_,?_,fun _ _ _ => rfl,?_,?_⟩
  · intro t
    change δ ≤ δ*2^(W.height t.1) ∧ δ*2^(W.height t.1) ≤ δ*2^Lh
    constructor
    · exact le_mul_of_one_le_right hδ.le (one_le_pow₀ (by norm_num))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (hh t.1)) hδ.le
  · intro y hy j
    exact hv.2.2.1 y ((W.grainTuples_subset cube g) hy) j
  · intro y hy j
    exact hv.2.2.2.2.1 y ((W.grainTuples_subset cube g) hy) j
  · intro j o t ht v hv' htv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht.1
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv'.1
    apply hv.2.2.2.2.2.1 j o
      ⟨Finset.mem_image_of_mem _ ((W.grainTuples_subset cube g) hy),ht.2⟩
      ⟨Finset.mem_image_of_mem _ ((W.grainTuples_subset cube g) hz),hv'.2⟩
    intro he
    exact htv (congrArg (fun p => (j,p)) he)

theorem localPhysical_count (W : FrozenGeometryState n k T C O)
    (cube : T → C) (g : W.Grain) (δ : ℝ) (j : Fin k) :
    ((W.localPhysical cube g δ).records (W.grainTuples cube g) j).card =
      grainRecordCount W.tuples cube W.grain (fun y => W.parent y j) g := by
  classical
  let : DecidableEq (Fin k × W.Piece) := Classical.decEq _
  simp only [CellularPhysicalFamily.records,localPhysical]
  rw [show (W.grainTuples cube g).image (fun y => (j,W.parent y j)) =
      ((W.grainTuples cube g).image (fun y => W.parent y j)).image (fun t => (j,t)) by
        rw [Finset.image_image]; rfl]
  rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
  rfl

omit [DecidableEq T] in
theorem grainTuples_mass_on_support (W : FrozenGeometryState n k T C O)
    (cube : T → C) (cubes : Finset C) (g : W.Grain) {p : ℝ} (hp : 0 < p)
    (hc : ∀ y ∈ W.tuples, cube y ∈ cubes) :
    tupleCubeMass (W.grainTuples cube g) cube (W.grainCubes cube g) p =
      tupleCubeMass (W.grainTuples cube g) cube cubes p := by
  apply tupleCubeMass_eq_of_support _ _ _ _ _ (fun y hy => Finset.mem_image_of_mem _ hy) hp
  intro q hq
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  exact hc y ((W.grainTuples_subset cube g) hy)

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.localPhysical_valid
#print axioms KakeyaTwoScale.FrozenGeometryState.localPhysical_count
#print axioms KakeyaTwoScale.FrozenGeometryState.grainTuples_mass_on_support
