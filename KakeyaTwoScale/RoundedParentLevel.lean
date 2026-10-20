module
public import KakeyaTwoScale.ParentLevel
public import KakeyaTwoScale.LatticePacking

@[expose] public section

/-! Actual grid-pair parents, followed by the proved capacity-level selection.
Coordinates here use the existing sup-norm horizontal grid convention. -/
noncomputable section
namespace KakeyaTwoScale
namespace RoundedParentLevel
open Classical

abbrev Parent (n : ℕ) := (Fin n → ℤ) × (Fin n → ℤ)

def assign {Child : Type*} {n : ℕ} (ρ : ℝ)
    (b v : Child → Fin n → ℝ) (x : Child) : Parent n :=
  (gridIndex ρ (b x),gridIndex ρ (v x))

def parentBase {n : ℕ} (ρ : ℝ) (p : Parent n) : Fin n → ℝ := latticePoint ρ p.1

def parentSlope {n : ℕ} (ρ : ℝ) (p : Parent n) : Fin n → ℝ := latticePoint ρ p.2

theorem parentBase_assign {Child : Type*} {n : ℕ} (ρ : ℝ)
    (b v : Child → Fin n → ℝ) (x : Child) :
    parentBase ρ (assign ρ b v x) = gridRound ρ (b x) := rfl

theorem parentSlope_assign {Child : Type*} {n : ℕ} (ρ : ℝ)
    (b v : Child → Fin n → ℝ) (x : Child) :
    parentSlope ρ (assign ρ b v x) = gridRound ρ (v x) := rfl

/-- Both coordinates determine a unique parent, with no choice of nearby data. -/
theorem assign_eq_iff {Child : Type*} {n : ℕ} (ρ : ℝ)
    (b v : Child → Fin n → ℝ) (x y : Child) :
    assign ρ b v x=assign ρ b v y ↔
      gridIndex ρ (b x)=gridIndex ρ (b y) ∧ gridIndex ρ (v x)=gridIndex ρ (v y) :=
  by simp only [assign,Prod.mk.injEq]

/-- The geometrically constructed parent contains the entire horizontal coarse
cell of the child at every allowed height. -/
theorem parent_contains_coarse_cell {Child : Type*} {n : ℕ} {ρ : ℝ} (hρ : 0<ρ)
    (b v : Child → Fin n → ℝ) (x : Child) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    gridCell ρ (gridIndex ρ (segmentPoint (b x) (v x) t)) ⊆
      (fun y => (t,y)) ⁻¹' horizontalTube
        (parentBase ρ (assign ρ b v x)) (parentSlope ρ (assign ρ b v x)) (3*ρ) :=
  gridCell_inside_rounded_parent hρ (b x) (v x) t ht

variable {Child : Type*} [DecidableEq Child] {n : ℕ}

def fixed (S : Finset Child) (b v : Child → Fin n → ℝ) (j : ℕ)
    (fine ρ : ℝ) (hf : 0<fine) (hρ : 0<ρ) : FixedParents Child (Parent n) :=
  ParentLevel.fixed S (assign ρ b v) j fine (ρ^n) hf (pow_pos hρ n)

theorem fixed_rounding (S : Finset Child) (b v : Child → Fin n → ℝ) (j : ℕ)
    (fine ρ : ℝ) (hf : 0<fine) (hρ : 0<ρ) (x : Child) :
    parentBase ρ ((fixed S b v j fine ρ hf hρ).assign x)=gridRound ρ (b x) ∧
    parentSlope ρ ((fixed S b v j fine ρ hf hρ).assign x)=gridRound ρ (v x) := ⟨rfl,rfl⟩

/-- The supplied finite family determines a retained level and all parent data.
No rounding, capacity, weight-comparability or retention premises are supplied. -/
theorem exists_rounded_fixed_level (S : Finset Child) (b v : Child → Fin n → ℝ)
    (fine ρ : ℝ) (hf : 0<fine) (hρ : 0<ρ) :
    ∃ j ≤ S.card.log2, ∃ F : FixedParents Child (Parent n),
      F=fixed S b v j fine ρ hf hρ ∧
      fine*(S.card:ℝ)/((S.card.log2+1:ℕ):ℝ) ≤ fine*(F.children.card:ℝ) ∧
      (∀ x, parentBase ρ (F.assign x)=gridRound ρ (b x) ∧
        parentSlope ρ (F.assign x)=gridRound ρ (v x)) ∧
      (∀ p∈F.parents, F.capacity p=ParentLevel.capacity S (assign ρ b v) p) ∧
      (∀ p∈F.parents, F.weight ≤ fine*(F.capacity p:ℝ)/(ρ^n) ∧
        fine*(F.capacity p:ℝ)/(ρ^n) < 2*F.weight) := by
  obtain ⟨j,hj,hm⟩ := ParentLevel.exists_fixed_level S (assign ρ b v)
    fine (ρ^n) hf (pow_pos hρ n)
  refine ⟨j,hj,fixed S b v j fine ρ hf hρ,rfl,hm,?_,?_,?_⟩
  · exact fixed_rounding S b v j fine ρ hf hρ
  · intro p hp
    exact ParentLevel.fixed_capacity_original S (assign ρ b v) j fine (ρ^n) hf (pow_pos hρ n) hp
  · intro p hp
    have he := ParentLevel.fixed_capacity_original S (assign ρ b v) j fine (ρ^n) hf (pow_pos hρ n) hp
    change ParentLevel.commonWeight fine (ρ^n) j ≤ _ ∧ _ < 2*ParentLevel.commonWeight fine (ρ^n) j
    change (ParentLevel.fixed S (assign ρ b v) j fine (ρ^n) hf (pow_pos hρ n)).capacity p = _ at he
    rw [show (fixed S b v j fine ρ hf hρ).capacity p = _ from he]
    exact ParentLevel.normalized_capacity_band S (assign ρ b v) j hf (pow_pos hρ n) hp

end RoundedParentLevel
end KakeyaTwoScale
#print axioms KakeyaTwoScale.RoundedParentLevel.parentBase_assign
#print axioms KakeyaTwoScale.RoundedParentLevel.parentSlope_assign
#print axioms KakeyaTwoScale.RoundedParentLevel.assign_eq_iff
#print axioms KakeyaTwoScale.RoundedParentLevel.parent_contains_coarse_cell
#print axioms KakeyaTwoScale.RoundedParentLevel.fixed_rounding
#print axioms KakeyaTwoScale.RoundedParentLevel.exists_rounded_fixed_level
