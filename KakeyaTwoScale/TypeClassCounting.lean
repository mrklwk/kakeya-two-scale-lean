module
public import KakeyaTwoScale.TensorSD
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Actual words obtained by permuting coordinates of a given word. -/
def wordTypeClass {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]
    (w : I → A) : Finset (I → A) :=
  Finset.univ.image (fun g : Equiv.Perm I => w ∘ g)

theorem mem_wordTypeClass {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]
    (w v : I → A) : v ∈ wordTypeClass w ↔ ∃ g : Equiv.Perm I, w ∘ g = v := by
  simp [wordTypeClass]

theorem wordTypeClass_nonempty {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]
    (w : I → A) : (wordTypeClass w).Nonempty :=
  ⟨w,(mem_wordTypeClass w w).mpr ⟨Equiv.refl I,rfl⟩⟩

/-- Projection of a type class is the entire projected type class, not
merely a subset with an uncontrolled lower bound. -/
theorem wordTypeClass_image {I A B : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] [DecidableEq B] (w : I → A) (f : A → B) :
    (wordTypeClass w).image (fun v => f ∘ v) = wordTypeClass (f ∘ w) := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨g,rfl⟩ := (mem_wordTypeClass w u).mp hu
    exact (mem_wordTypeClass _ _).mpr ⟨g,rfl⟩
  · intro hv
    obtain ⟨g,rfl⟩ := (mem_wordTypeClass _ _).mp hv
    exact Finset.mem_image.mpr ⟨w ∘ g,(mem_wordTypeClass _ _).mpr ⟨g,rfl⟩,rfl⟩

/-- Exact factorial counting from orbit-stabilizer, with every factorial
in the denominator coming from the actual symbol fiber. -/
theorem wordTypeClass_card_mul_fiber_factorials {I A : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq A] (w : I → A) :
    (wordTypeClass w).card *
      (∏ a ∈ Finset.univ.image w, (Fintype.card {i : I // w i = a}).factorial) =
      (Fintype.card I).factorial := by
  let K := (Equiv.Perm I)ᵈᵐᵃ
  let : Fintype K := Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  have hs : (↑(wordTypeClass w) : Set (I → A)) = MulAction.orbit K w := by
    ext v
    rw [Finset.mem_coe,mem_wordTypeClass,MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨DomMulAct.mk g,rfl⟩
    · rintro ⟨g,rfl⟩
      exact ⟨DomMulAct.mk.symm g,rfl⟩
  let : Fintype (MulAction.orbit K w) := Fintype.ofEquiv
    {v // v ∈ wordTypeClass w} (Set.equivOfEq hs)
  let : Fintype (MulAction.stabilizer K w) := Fintype.ofFinite _
  have hc : Fintype.card (MulAction.orbit K w) = (wordTypeClass w).card := by
    rw [← Fintype.card_congr (Set.equivOfEq hs)]
    exact Fintype.card_coe _
  have he : MulAction.stabilizer K w ≃ {g : Equiv.Perm I // w ∘ g = w} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm (fun _ => DomMulAct.mem_stabilizer_iff)
  have ht := Fintype.card_congr he
  rw [DomMulAct.stabilizer_card'] at ht
  have hh := MulAction.card_orbit_mul_card_stabilizer_eq_card_group K w
  rw [hc,ht,Fintype.card_congr (DomMulAct.mk.symm : K ≃ Equiv.Perm I),Fintype.card_perm] at hh
  exact hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mem_wordTypeClass
#print axioms KakeyaTwoScale.wordTypeClass_nonempty
#print axioms KakeyaTwoScale.wordTypeClass_image
#print axioms KakeyaTwoScale.wordTypeClass_card_mul_fiber_factorials
