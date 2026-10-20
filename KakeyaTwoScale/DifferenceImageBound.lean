module
public import KakeyaTwoScale.FiniteVectorEncoding

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Choose one actual representative per image value. -/
theorem exists_image_transversal {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) :
    ∃ T ⊆ S, Set.InjOn f (↑T : Set A) ∧ T.image f = S.image f := by
  let I := S.image f
  have hex : ∀ y : {y // y ∈ I}, ∃ x ∈ S, f x = y.val := by
    intro y
    exact Finset.mem_image.mp y.property
  choose rep hrep heq using hex
  let T := I.attach.image rep
  have hT : T ⊆ S := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact hrep y
  refine ⟨T,hT,?_,?_⟩
  · intro x hx y hy hxy
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hy
    have huv : u = v := Subtype.ext ((heq u).symm.trans (hxy.trans (heq v)))
    rw [huv]
  · apply Finset.Subset.antisymm (Finset.image_subset_image hT)
    intro y hy
    exact Finset.mem_image.mpr ⟨rep ⟨y,hy⟩,Finset.mem_image.mpr ⟨⟨y,hy⟩,Finset.mem_attach _ _,rfl⟩,heq ⟨y,hy⟩⟩

/-- Remove difference injectivity by taking a transversal. The conclusion
bounds the difference image, which is the counting object needed by entropy. -/
theorem FiniteSDBound.difference_image_bound {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (G : Finset ArithmeticPoint) (N : ℝ) (hN : 0 ≤ N)
    (hp : ∀ r ∈ R, ((G.image (arithmeticProjection r)).card:ℝ) ≤ N) :
    ((G.image (arithmeticProjection (-1))).card:ℝ) ≤ C*N^β := by
  obtain ⟨T,hT,hi,he⟩ := exists_image_transversal G (arithmeticProjection (-1))
  have hb := hSD T hi N hN (fun r hr =>
    le_trans (by exact_mod_cast Finset.card_le_card (Finset.image_subset_image hT)) (hp r hr))
  have hc : T.card = (G.image (arithmeticProjection (-1))).card := by
    rw [← he,Finset.card_image_iff.mpr hi]
  rwa [hc] at hb

/-- Lift ordinary SD to finite rational vectors without changing the slope
family, exponent or multiplicative constant. The encoder is constructed
simultaneously for every relevant projection. -/
theorem FiniteSDBound.vector_difference_image_bound {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) {n : ℕ}
    (G : Finset ((Fin n → ℚ) × (Fin n → ℚ))) (N : ℝ) (hN : 0 ≤ N)
    (hp : ∀ r ∈ R, ((G.image (vectorProjection r)).card:ℝ) ≤ N) :
    ((G.image (vectorProjection (-1))).card:ℝ) ≤ C*N^β := by
  obtain ⟨f,hf⟩ := exists_projection_encoder G (insert (-1) R)
  have h := hSD.difference_image_bound (G.image (encodeVectorPair f)) N hN (by
    intro r hr
    rw [(hf r (Finset.mem_insert_of_mem hr)).2]
    exact hp r hr)
  rwa [(hf (-1) (Finset.mem_insert_self _ _)).2] at h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_image_transversal
#print axioms KakeyaTwoScale.FiniteSDBound.difference_image_bound
#print axioms KakeyaTwoScale.FiniteSDBound.vector_difference_image_bound
