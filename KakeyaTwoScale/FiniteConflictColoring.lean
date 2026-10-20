module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Image

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- The greedy finite coloring construction with a degree bound chosen before
the family. Colors are natural numbers at most M, hence M+1 colors suffice. -/
theorem finite_conflict_coloring {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (hirr : ∀ x, ¬R x x)
    (M : ℕ) (S : Finset α)
    (hdegree : ∀ x ∈ S, (S.filter (R x)).card ≤ M) :
    ∃ c : α → ℕ, (∀ x ∈ S, c x ≤ M) ∧
      ∀ x ∈ S, ∀ y ∈ S, R x y → c x ≠ c y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0,by simp,by simp⟩
  | @insert a S ha ih =>
    have hsmall : ∀ x ∈ S, (S.filter (R x)).card ≤ M := by
      intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert a S))).trans
        (hdegree x (Finset.mem_insert_of_mem hx))
    obtain ⟨c,hc,hproper⟩ := ih hsmall
    let T := (S.filter (R a)).image c
    have hT : T.card ≤ M := (Finset.card_image_le).trans <|
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert a S))).trans
        (hdegree a (Finset.mem_insert_self a S))
    obtain ⟨k,hk,hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show T.card < (Finset.range (M+1)).card by simpa using Nat.lt_succ_of_le hT)
    have hav (y) (hy : y ∈ S) (hrel : R a y) : k ≠ c y := by
      intro he
      apply hkn
      exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hrel⟩,he.symm⟩
    refine ⟨Function.update c a k,?_,?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      · by_cases hxa : x=a
        · subst x; simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
        · simpa [Function.update_of_ne hxa] using hc x hx
    · intro x hx y hy hxy
      by_cases hxa : x=a
      · subst x
        have hya : y≠a := by intro he; subst y; exact hirr a hxy
        have hyS := Finset.mem_of_mem_insert_of_ne hy hya
        simpa [Function.update_of_ne hya] using hav y hyS hxy
      · by_cases hya : y=a
        · subst y
          have hxS := Finset.mem_of_mem_insert_of_ne hx hxa
          simpa [Function.update_of_ne hxa] using (hav x hxS (hsymm x a hxy)).symm
        · simpa [Function.update_of_ne hxa,Function.update_of_ne hya] using
            hproper x (Finset.mem_of_mem_insert_of_ne hx hxa)
              y (Finset.mem_of_mem_insert_of_ne hy hya) hxy

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_conflict_coloring
