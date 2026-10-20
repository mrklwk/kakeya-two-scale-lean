module
public import KakeyaTwoScale.ProbabilityApproximation

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def countedWord {A B : Type*} (c : A → ℕ) (f : A → B) : (Σ a : A, Fin (c a)) → B :=
  fun i => f i.1

theorem countedWord_fiber_card {A B : Type*} [Fintype A] [DecidableEq B]
    (c : A → ℕ) (f : A → B) (y : B) :
    Fintype.card {i : Σ a : A, Fin (c a) // countedWord c f i = y} =
      ∑ a ∈ Finset.univ.filter (fun a => f a = y), c a := by
  let e : {i : Σ a : A, Fin (c a) // countedWord c f i = y} ≃
      (Σ a : {a : A // f a = y}, Fin (c a.val)) :=
    { toFun := fun i => ⟨⟨i.val.1,i.property⟩,i.val.2⟩
      invFun := fun i => ⟨⟨i.1.val,i.2⟩,i.1.property⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype _ (by intro a; simp) c).symm

theorem countedWord_empirical_push {A B : Type*} [Fintype A] [DecidableEq B]
    (c : A → ℕ) (f : A → B) (y : B) :
    empiricalLaw (countedWord c f) y = finitePushLaw Finset.univ (normalizedCounts c) f y := by
  unfold empiricalLaw finitePushLaw normalizedCounts
  rw [countedWord_fiber_card,Fintype.card_sigma]
  simp only [Fintype.card_fin,Nat.cast_sum,← Finset.sum_div]

/-- The empirical law of an actual counted word represents the normalized
integer-count law exactly, including all zero counts. -/
theorem countedWord_entropy {A B : Type*} [Fintype A] [DecidableEq B]
    (c : A → ℕ) (f : A → B) :
    empiricalEntropy (countedWord c f) =
      finiteEntropy (Finset.univ.image f) (finitePushLaw Finset.univ (normalizedCounts c) f) := by
  let T := Finset.univ.image (countedWord c f)
  have hsub : T ⊆ Finset.univ.image f := by
    intro y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨i.1,Finset.mem_univ _,rfl⟩
  unfold empiricalEntropy finiteEntropy
  congr 1
  simp only [countedWord_empirical_push]
  apply Finset.sum_subset hsub
  intro y _ hy
  have hz : Fintype.card {i : Σ a : A, Fin (c a) // countedWord c f i = y} = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun i => hy (Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,i.property⟩)⟩
  have hp : finitePushLaw Finset.univ (normalizedCounts c) f y = 0 := by
    rw [← countedWord_empirical_push]
    simp [empiricalLaw,hz]
  simp [hp]

/-- Counting-to-entropy for every normalized finite integer-count law. -/
theorem FiniteSDBound.counted_entropy {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 0 < β) (hR : R.Nonempty)
    {A : Type*} [Fintype A] (c : A → ℕ) (hc : 0 < ∑ a, c a) (f : A → ArithmeticPoint) :
    finiteEntropy (Finset.univ.image (arithmeticProjection (-1) ∘ f))
      (finitePushLaw Finset.univ (normalizedCounts c) (arithmeticProjection (-1) ∘ f)) ≤
      β*R.sup' hR (fun r => finiteEntropy (Finset.univ.image (arithmeticProjection r ∘ f))
        (finitePushLaw Finset.univ (normalizedCounts c) (arithmeticProjection r ∘ f))) := by
  have hn : 0 < Fintype.card (Σ a : A, Fin (c a)) := by simpa using hc
  have : Nonempty (Σ a : A, Fin (c a)) := Fintype.card_pos_iff.mp hn
  have hh := hSD.empirical_entropy hβ hR (countedWord c f)
  have he (r : ℚ) : arithmeticProjection r ∘ countedWord c f = countedWord c (arithmeticProjection r ∘ f) := rfl
  simpa only [he,countedWord_entropy] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.countedWord_fiber_card
#print axioms KakeyaTwoScale.countedWord_empirical_push
#print axioms KakeyaTwoScale.countedWord_entropy
#print axioms KakeyaTwoScale.FiniteSDBound.counted_entropy
