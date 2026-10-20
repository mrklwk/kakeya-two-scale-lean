module
public import KakeyaTwoScale.HomogeneousEntropy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem subtype_image_eq {A B : Type*} [DecidableEq B] (S : Finset A) (f : A → B) :
    (Finset.univ.image (fun x : S => f x.val)) = S.image f := by
  ext y
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,x.property,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩

theorem finitePushLaw_subtype {A B : Type*} [DecidableEq B]
    (S : Finset A) (q : A → ℝ) (f : A → B) (y : B) :
    finitePushLaw Finset.univ (fun x : S => q x.val) (fun x : S => f x.val) y = finitePushLaw S q f y := by
  simp only [finitePushLaw,Finset.sum_filter]
  exact (Finset.sum_subtype S (by intro x; rfl) (fun x => if f x=y then q x else 0)).symm

theorem pushEntropy_subtype {A B : Type*} [DecidableEq B]
    (S : Finset A) (q : A → ℝ) (f : A → B) :
    pushEntropy (fun x : S => q x.val) (fun x : S => f x.val) =
      finiteEntropy (S.image f) (finitePushLaw S q f) := by
  unfold pushEntropy
  rw [subtype_image_eq]
  congr 1
  funext y
  exact finitePushLaw_subtype S q f y

theorem finiteEntropy_subtype {A : Type*} (S : Finset A) (q : A → ℝ) :
    finiteEntropy (Finset.univ : Finset S) (fun x => q x.val) = finiteEntropy S q := by
  unfold finiteEntropy
  congr 1
  exact (Finset.sum_subtype S (by intro x; rfl) (fun x => q x*Real.log (q x))).symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.subtype_image_eq
#print axioms KakeyaTwoScale.finitePushLaw_subtype
#print axioms KakeyaTwoScale.pushEntropy_subtype
#print axioms KakeyaTwoScale.finiteEntropy_subtype
