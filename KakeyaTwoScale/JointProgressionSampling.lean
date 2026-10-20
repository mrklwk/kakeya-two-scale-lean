module
public import KakeyaTwoScale.PZRestrictedIndex

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

def nonzeroTranslationSamples (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  (Finset.univ.erase 0).product Finset.univ

def progressionHeightHits (p : ℕ) [NeZero p] (A I J : Finset (ZMod p)) (y : ZMod p) :
    Finset (ZMod p × ZMod p) :=
  (nonzeroTranslationSamples p).filter (fun z =>
    y ∈ J.image (fun j => z.1*j) ∧ z.2 ∈ A-I.image (fun i => z.1*i))

/-- Exact joint sampling count. The index interval is undilated in A−(y/j)I,
and every nonzero difference and every translation is counted once. -/
theorem progression_height_hit_count (p : ℕ) [Fact p.Prime]
    (A I J : Finset (ZMod p)) (hJ : ∀ j ∈ J, j ≠ 0) (y : ZMod p) (hy : y ≠ 0) :
    (progressionHeightHits p A I J y).card =
      ∑ j ∈ J, (A-I.image (fun i => (y*j⁻¹)*i)).card := by
  let T := J.sigma (fun j => A-I.image (fun i => (y*j⁻¹)*i))
  let e : (Σ _j : ZMod p, ZMod p) → ZMod p × ZMod p := fun z => (y*z.1⁻¹,z.2)
  have hinj : Function.Injective e := by
    intro a b he
    have h1 : a.1 = b.1 := inv_injective (mul_left_cancel₀ hy (congrArg Prod.fst he))
    cases a with
    | mk a t =>
      cases b with
      | mk b s =>
        dsimp only at h1
        subst b
        have h2 : t = s := congrArg Prod.snd he
        subst s
        rfl
  have heq : progressionHeightHits p A I J y = T.image e := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz,hheight,htrans⟩ := Finset.mem_filter.mp hz
      have hd : z.1 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hz).1).1
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hheight
      have hj0 := hJ j hj
      have hdiff : y*j⁻¹ = z.1 := by rw [← he]; field_simp
      apply Finset.mem_image.mpr
      refine ⟨⟨j,z.2⟩,Finset.mem_sigma.mpr ⟨hj,?_⟩,?_⟩
      · simpa only [hdiff] using htrans
      · exact Prod.ext hdiff rfl
    · intro hz
      obtain ⟨⟨j,t⟩,hjt,he⟩ := Finset.mem_image.mp hz
      obtain ⟨hj,ht⟩ := Finset.mem_sigma.mp hjt
      have hj0 := hJ j hj
      subst z
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,Finset.mem_univ _⟩,?_,?_⟩
      · exact mul_ne_zero hy (inv_ne_zero hj0)
      · exact Finset.mem_image.mpr ⟨j,hj,by dsimp [e]; field_simp⟩
      · exact ht
  rw [heq,Finset.card_image_of_injective _ hinj]
  exact Finset.card_sigma _ _

theorem nonzeroTranslationSamples_card (p : ℕ) [Fact p.Prime] :
    (nonzeroTranslationSamples p).card = (p-1)*p := by
  simp [nonzeroTranslationSamples,Finset.card_product]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.progression_height_hit_count
#print axioms KakeyaTwoScale.nonzeroTranslationSamples_card
