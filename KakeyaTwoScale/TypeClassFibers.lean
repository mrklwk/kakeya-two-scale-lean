module
public import KakeyaTwoScale.RepeatedTypeClasses

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem wordTypeClass_precomp {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]
    (w u : I → A) (g : Equiv.Perm I) : u ∘ g ∈ wordTypeClass w ↔ u ∈ wordTypeClass w := by
  constructor
  · intro hu
    obtain ⟨h,hh⟩ := (mem_wordTypeClass _ _).mp hu
    apply (mem_wordTypeClass _ _).mpr
    refine ⟨g.symm.trans h,?_⟩
    funext i
    have he := congrFun hh (g.symm i)
    simpa [Function.comp_def] using he
  · intro hu
    obtain ⟨h,rfl⟩ := (mem_wordTypeClass _ _).mp hu
    exact (mem_wordTypeClass _ _).mpr ⟨g.trans h,rfl⟩

/-- All fibers of a projected type class have exactly the same size.
The bijection uses the same coordinate permutation on every coordinate. -/
theorem wordTypeClass_fiber_card {I A B : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] [DecidableEq B] (w : I → A) (f : A → B)
    {v : I → B} (hv : v ∈ wordTypeClass (f ∘ w)) :
    ((wordTypeClass w).filter (fun u => f ∘ u = f ∘ w)).card =
      ((wordTypeClass w).filter (fun u => f ∘ u = v)).card := by
  obtain ⟨g,rfl⟩ := (mem_wordTypeClass _ _).mp hv
  apply Finset.card_bij (fun u _ => u ∘ g)
  · intro u hu
    obtain ⟨hu,he⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨(wordTypeClass_precomp w u g).mpr hu,?_⟩
    exact congrArg (fun v => v ∘ g) he
  · intro u _ v _ he
    funext i
    have h := congrFun he (g.symm i)
    simpa [Function.comp_def] using h
  · intro u hu
    obtain ⟨hu,he⟩ := Finset.mem_filter.mp hu
    refine ⟨u ∘ g.symm,Finset.mem_filter.mpr ⟨(wordTypeClass_precomp w u g.symm).mpr hu,?_⟩,?_⟩
    · funext i
      have h := congrFun he (g.symm i)
      simpa [Function.comp_def] using h
    · funext i
      simp [Function.comp_def]

/-- Exact uniform-fiber mass identity for the constructed type class. -/
theorem wordTypeClass_fiber_product {I A B : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] [DecidableEq B] (w : I → A) (f : A → B) :
    (wordTypeClass (f ∘ w)).card *
      ((wordTypeClass w).filter (fun u => f ∘ u = f ∘ w)).card = (wordTypeClass w).card := by
  have hs := Finset.card_eq_sum_card_fiberwise
    (s := wordTypeClass w) (t := wordTypeClass (f ∘ w)) (f := fun u => f ∘ u)
    (by intro u hu; rw [← wordTypeClass_image]; exact Finset.mem_image.mpr ⟨u,hu,rfl⟩)
  rw [Finset.sum_congr rfl (fun v hv => (wordTypeClass_fiber_card w f hv).symm)] at hs
  simpa using hs.symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.wordTypeClass_precomp
#print axioms KakeyaTwoScale.wordTypeClass_fiber_card
#print axioms KakeyaTwoScale.wordTypeClass_fiber_product
