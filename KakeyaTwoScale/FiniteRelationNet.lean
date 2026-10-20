module
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- A finite relation net is constructed from a uniform cardinality bound on
separated finite subsets. The ambient set itself need not be finite. -/
theorem finite_relation_net {α : Type*} (S : Set α) (R : α → α → Prop)
    (hrefl : ∀ x ∈ S, R x x) (hsymm : ∀ x y, R x y → R y x)
    (M : ℕ) (hbound : ∀ F : Finset α, (↑F : Set α) ⊆ S →
      (↑F : Set α).Pairwise (fun x y => ¬R x y) → F.card ≤ M) :
    ∃ F : Finset α, (↑F : Set α) ⊆ S ∧
      (↑F : Set α).Pairwise (fun x y => ¬R x y) ∧
      ∀ x ∈ S, ∃ y ∈ F, R x y := by
  classical
  let P := fun n : ℕ => ∃ F : Finset α, (↑F : Set α) ⊆ S ∧
    (↑F : Set α).Pairwise (fun x y => ¬R x y) ∧ F.card=n
  have hp0 : P 0 := ⟨∅,by simp,by simp,by simp⟩
  obtain ⟨F,hFS,hsep,hcard⟩ := Nat.findGreatest_spec (Nat.zero_le M) hp0
  refine ⟨F,hFS,hsep,?_⟩
  intro x hx
  by_contra! hn
  have hxf : x ∉ F := fun hf => hn x hf (hrefl x hx)
  have hins : (↑(insert x F) : Set α) ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · exact hFS hy
  have hsepins : (↑(insert x F) : Set α).Pairwise (fun x y => ¬R x y) := by
    intro y hy z hz hyz
    rcases Finset.mem_insert.mp hy with hey | hFy
    · subst y
      rcases Finset.mem_insert.mp hz with hez | hFz
      · exact (hyz hez.symm).elim
      · exact hn z hFz
    · rcases Finset.mem_insert.mp hz with hez | hFz
      · subst z
        exact fun h => hn y hFy (hsymm _ _ h)
      · exact hsep hFy hFz hyz
  have hi : (insert x F).card ≤ Nat.findGreatest P M :=
    Nat.le_findGreatest (hbound _ hins hsepins) ⟨insert x F,hins,hsepins,rfl⟩
  rw [Finset.card_insert_of_notMem hxf,hcard] at hi
  omega

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_relation_net
