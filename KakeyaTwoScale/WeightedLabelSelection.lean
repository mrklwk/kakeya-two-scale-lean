module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Finite ownership conserves original nonnegative weights; one actual
fiber carries at least the reciprocal-cardinality share. -/
theorem exists_heaviest_weighted_label {C I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (B : Finset C) (owner : C → I) (w : C → ℝ) :
    ∃ i : I, (∑ q ∈ B, w q) ≤ (Fintype.card I : ℝ) *
      ∑ q ∈ B.filter (fun q => owner q=i), w q := by
  classical
  let f : I → ℝ := fun i => ∑ q ∈ B.filter (fun q => owner q=i), w q
  have heq : (∑ i, f i) = ∑ q ∈ B, w q := by
    simp only [f,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    simp
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp
    (Finset.max'_mem (Finset.univ.image f) (Finset.univ_nonempty.image f))
  refine ⟨i,?_⟩
  rw [← heq]
  calc
    (∑ j, f j) ≤ ∑ _j : I, f i := by
      apply Finset.sum_le_sum
      intro j _
      rw [hi]
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    _ = _ := by simp [f]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_heaviest_weighted_label
