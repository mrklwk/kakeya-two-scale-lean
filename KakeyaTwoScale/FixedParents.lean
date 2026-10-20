module
public import KakeyaTwoScale.Selection

@[expose] public section

/-! A finite fixed-parent model. Selections change only the child subset;
capacities, parent assignment, scales and common weight remain unchanged. -/
open scoped BigOperators
namespace KakeyaTwoScale

structure FixedParents (Child Parent : Type*) [DecidableEq Child] [DecidableEq Parent] where
  children : Finset Child
  parents : Finset Parent
  assign : Child → Parent
  assigned : ∀ x ∈ children, assign x ∈ parents
  fineCellVolume : ℝ
  coarseCellVolume : ℝ
  weight : ℝ
  fine_nonneg : 0 ≤ fineCellVolume
  coarse_pos : 0 < coarseCellVolume
  weight_pos : 0 < weight
  capacity_bound : ∀ p ∈ parents,
    fineCellVolume * ((children.filter fun x => assign x = p).card : ℝ) ≤
      2*weight*coarseCellVolume

namespace FixedParents
variable {Child Parent : Type*} [DecidableEq Child] [DecidableEq Parent]
variable (F : FixedParents Child Parent)

def capacity (p : Parent) : ℕ := (F.children.filter fun x => F.assign x = p).card

def count (selected : Finset Child) (p : Parent) : ℕ :=
  (selected.filter fun x => F.assign x = p).card

 theorem count_mono {s t : Finset Child} (hst : s ⊆ t) (p : Parent) :
    F.count s p ≤ F.count t p := by
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ hst

 theorem count_le_capacity {selected : Finset Child} (hs : selected ⊆ F.children)
    (p : Parent) : F.count selected p ≤ F.capacity p :=
  F.count_mono hs p

 /-- Parents covering a cell must include the assigned parent of every
 selected child at that cell. No axis-only assertion is substituted for
 whole-cell containment; its geometric proof must provide this hypothesis. -/
 theorem covered_cell_mass {selected : Finset Child} (hs : selected ⊆ F.children)
    (covering : Finset Parent) (hp : covering ⊆ F.parents)
    (hcover : ∀ x ∈ selected, F.assign x ∈ covering) :
    F.fineCellVolume * (selected.card : ℝ) ≤
      2*F.coarseCellVolume*(F.weight*covering.card) := by
  have hcard : (selected.card : ℝ) = ∑ p ∈ covering, (F.count selected p : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise hcover)
  rw [hcard]
  apply cell_mass_bound covering (fun p => (F.count selected p : ℝ))
    (fun p => (F.capacity p : ℝ)) F.fineCellVolume F.coarseCellVolume F.weight
    F.fine_nonneg
  · intro p _
    exact_mod_cast F.count_le_capacity hs p
  · intro p hpc
    exact F.capacity_bound p (hp hpc)

 /-- Every later deletion preserves an already established per-parent cap. -/
 theorem cap_preserved {s t : Finset Child} (hst : s ⊆ t) (bound : ℝ)
    (hb : ∀ p ∈ F.parents, (F.count t p : ℝ) ≤ bound) :
    ∀ p ∈ F.parents, (F.count s p : ℝ) ≤ bound := by
  intro p hp
  have hm : (F.count s p : ℝ) ≤ F.count t p := by
    exact_mod_cast F.count_mono hst p
  exact hm.trans (hb p hp)

 /-- Many selected children require many represented parents. -/
 theorem represented_weight {selected : Finset Child}
    (bound : ℝ) (hbpos : 0 < bound)
    (hb : ∀ p ∈ selected.image F.assign, (F.count selected p : ℝ) ≤ bound) :
    F.weight * selected.card / bound ≤ F.weight * (selected.image F.assign).card := by
  have hcard : (selected.card : ℝ) =
      ∑ p ∈ selected.image F.assign, (F.count selected p : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image F.assign selected
  have hsum : (selected.card : ℝ) ≤ (selected.image F.assign).card * bound := by
    rw [hcard]
    calc
      _ ≤ ∑ _p ∈ selected.image F.assign, bound := Finset.sum_le_sum hb
      _ = _ := by simp [mul_comm]
  apply (div_le_iff₀ hbpos).2
  nlinarith [mul_le_mul_of_nonneg_left hsum F.weight_pos.le]
 /-- Sum the low-cell deletion cost at one height, with the same capacities
 and weight in every cell. A later measure-theoretic module must integrate it. -/
 theorem low_cells_loss {Cell : Type*} (cells : Finset Cell)
    (selected : Cell → Finset Child) (covering : Cell → Finset Parent) (M : ℝ)
    (hs : ∀ c ∈ cells, selected c ⊆ F.children)
    (hp : ∀ c ∈ cells, covering c ⊆ F.parents)
    (hcover : ∀ c ∈ cells, ∀ x ∈ selected c, F.assign x ∈ covering c)
    (hlow : ∀ c ∈ cells, F.weight*(covering c).card ≤ M) :
    ∑ c ∈ cells, F.fineCellVolume*(selected c).card ≤
      2*M*(F.coarseCellVolume*cells.card) := by
  have h := low_cell_loss cells
    (fun c => F.fineCellVolume*(selected c).card)
    (fun _ => F.coarseCellVolume)
    (fun c => F.weight*(covering c).card) M
    (fun _ _ => F.coarse_pos.le) hlow
    (fun c hc => F.covered_cell_mass (hs c hc) (covering c) (hp c hc) (hcover c hc))
  simpa [mul_comm] using h

end FixedParents
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FixedParents.covered_cell_mass
#print axioms KakeyaTwoScale.FixedParents.cap_preserved
#print axioms KakeyaTwoScale.FixedParents.represented_weight

#print axioms KakeyaTwoScale.FixedParents.low_cells_loss
