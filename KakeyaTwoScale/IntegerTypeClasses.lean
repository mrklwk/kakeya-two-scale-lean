module
public import KakeyaTwoScale.FiniteFiberEncoding
public import KakeyaTwoScale.TypeClassDiscretization

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Encoding of any finite family of rational pair-valued words into integer
pairs, preserving the complete equality relations of the chosen projections. -/
theorem exists_integer_word_encoder {I : Type*} [Fintype I]
    (S : Finset (I → ArithmeticPoint)) (R : Finset ℚ) :
    ∃ e : (I → ArithmeticPoint) → ℤ × ℤ,
      Set.InjOn e (↑S : Set _) ∧
      (∀ v ∈ S, ∀ w ∈ S, (e v).2 = (e w).2 ↔ Prod.snd ∘ v = Prod.snd ∘ w) ∧
      (∀ r ∈ R, ∀ v ∈ S, ∀ w ∈ S,
        integerProjection r (e v) = integerProjection r (e w) ↔
          arithmeticProjection r ∘ v = arithmeticProjection r ∘ w) := by
  let b := (Fintype.equivFin I).symm
  let g := fun v : I → ArithmeticPoint => (fun j => (v (b j)).1,fun j => (v (b j)).2)
  have hg : Function.Injective g := by
    intro v w h
    funext i
    have h1 := congrFun (congrArg Prod.fst h) ((Fintype.equivFin I) i)
    have h2 := congrFun (congrArg Prod.snd h) ((Fintype.equivFin I) i)
    exact Prod.ext (by simpa [g,b] using h1) (by simpa [g,b] using h2)
  obtain ⟨e,hei,hev,hep⟩ := exists_integer_vector_encoder (S.image g) R
  have hm (v) (hv : v ∈ S) : g v ∈ S.image g := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have hre (u v : I → ℚ) : u ∘ b = v ∘ b ↔ u = v := by
    constructor
    · intro h
      funext i
      simpa [b,Function.comp_def] using congrFun h ((Fintype.equivFin I) i)
    · intro h
      rw [h]
  refine ⟨e ∘ g,?_,?_,?_⟩
  · intro v hv w hw h
    exact hg (hei (hm v hv) (hm w hw) h)
  · intro v hv w hw
    rw [Function.comp_apply,Function.comp_apply,hev _ (hm v hv) _ (hm w hw)]
    exact hre (Prod.snd ∘ v) (Prod.snd ∘ w)
  · intro r hr v hv w hw
    rw [Function.comp_apply,Function.comp_apply,hep r hr _ (hm v hv) _ (hm w hw)]
    exact hre (arithmeticProjection r ∘ v) (arithmeticProjection r ∘ w)

/-- An actual integer set realizing the joint type class, its selected
projection classes, its vertical class and every vertical fiber exactly. -/
theorem integer_type_class_realization {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ArithmeticPoint) (R : Finset ℚ) :
    ∃ G : Finset (ℤ × ℤ),
      G.card = (wordTypeClass w).card ∧
      (G.image Prod.snd).card = (wordTypeClass (Prod.snd ∘ w)).card ∧
      (∀ r ∈ R, (G.image (integerProjection r)).card =
        (wordTypeClass (arithmeticProjection r ∘ w)).card) ∧
      (∀ y ∈ G.image Prod.snd,
        (G.filter (fun v => v.2 = y)).card = (baseTypeFiber w Prod.snd).card) := by
  let S := wordTypeClass w
  obtain ⟨e,hei,hev,hep⟩ := exists_integer_word_encoder S R
  refine ⟨S.image e,Finset.card_image_iff.mpr hei,?_,?_,?_⟩
  · rw [Finset.image_image,← wordTypeClass_image w Prod.snd]
    exact image_card_of_same_fibers S (Prod.snd ∘ e) (fun v => Prod.snd ∘ v) hev
  · intro r hr
    rw [Finset.image_image,← wordTypeClass_image w (arithmeticProjection r)]
    exact image_card_of_same_fibers S (integerProjection r ∘ e)
      (fun v => arithmeticProjection r ∘ v) (hep r hr)
  · intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have hm : Prod.snd ∘ v ∈ wordTypeClass (Prod.snd ∘ w) := by
      rw [← wordTypeClass_image w Prod.snd]
      exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
    calc
      _ = (S.filter (fun u => Prod.snd ∘ u = Prod.snd ∘ v)).card := by
        convert encoded_fiber_card S e (fun v => Prod.snd ∘ v) Prod.snd hei hev v hv using 1 <;> congr 1 <;> ext <;> simp
      _ = _ := by
        simpa only [S,baseTypeFiber] using (wordTypeClass_fiber_card w Prod.snd hm).symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_integer_word_encoder
#print axioms KakeyaTwoScale.integer_type_class_realization
