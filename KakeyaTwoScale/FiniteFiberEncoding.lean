module
public import KakeyaTwoScale.IntegerEncoding

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Two functions with the same fibers on a finite domain have images of
the same cardinality, without requiring either function to be injective. -/
theorem image_card_of_same_fibers {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (S : Finset A) (f : A → B) (g : A → C)
    (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y ↔ g x = g y) :
    (S.image f).card = (S.image g).card := by
  have hr : ∀ b : {b // b ∈ S.image f}, ∃ x, x ∈ S ∧ f x = b.val := by
    intro b
    exact Finset.mem_image.mp b.property
  choose rep hrep using hr
  apply Finset.card_bij (fun b hb => g (rep ⟨b,hb⟩))
  · intro b hb
    exact Finset.mem_image.mpr ⟨_,(hrep ⟨b,hb⟩).1,rfl⟩
  · intro b hb c hc he
    have hh := (h _ (hrep ⟨b,hb⟩).1 _ (hrep ⟨c,hc⟩).1).mpr he
    simpa only [(hrep ⟨b,hb⟩).2,(hrep ⟨c,hc⟩).2] using hh
  · intro c hc
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    have hb : f x ∈ S.image f := Finset.mem_image.mpr ⟨x,hx,rfl⟩
    refine ⟨f x,hb,?_⟩
    exact (h _ (hrep ⟨f x,hb⟩).1 x hx).mp (hrep ⟨f x,hb⟩).2

/-- An injective finite encoding preserving the fibers transports each
individual fiber cardinality exactly. -/
theorem encoded_fiber_card {A B C D : Type*} [DecidableEq B]
    (S : Finset A) (e : A → B) (f : A → C) (g : B → D)
    (he : Set.InjOn e (↑S : Set A))
    (h : ∀ x ∈ S, ∀ y ∈ S, g (e x) = g (e y) ↔ f x = f y)
    (v : A) (hv : v ∈ S) :
    ((S.image e).filter (fun y => g y = g (e v))).card =
      (S.filter (fun x => f x = f v)).card := by
  symm
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    have hh := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hh.1,rfl⟩,
      (h x hh.1 v hv).mpr hh.2⟩
  · intro x hx y hy hxy
    exact he (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
  · intro y hy
    obtain ⟨hy,hgy⟩ := Finset.mem_filter.mp hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,(h x hx v hv).mp hgy⟩,rfl⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.image_card_of_same_fibers
#print axioms KakeyaTwoScale.encoded_fiber_card
