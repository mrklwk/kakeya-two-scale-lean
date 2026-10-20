module
public import KakeyaTwoScale.SampledHeightSets
public import KakeyaTwoScale.CoefficientIntervals

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

/-- A genuine coefficient interval replaces the false symmetric-interval
inclusion in the informal source. Coefficients may have either sign. -/
theorem sampled_projection_subset (p m : ℕ) [Fact p.Prime]
    (H : Finset (ZMod p × ZMod p)) (a b : ℤ) (d t : ZMod p) :
    (sampledGraph H (positiveFieldInterval p m) (halfFieldInterval p m) d t).image
      (modularLinearForm p a b) ⊆
    (H.image (modularLinearForm p a b)) ∩ fieldProgression (coefficientInterval p m a b) d ((a:ZMod p)*t) := by
  intro z hz
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hv,hx,hy⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,?_⟩
  obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,hjy⟩ := Finset.mem_image.mp hy
  obtain ⟨i0,hi0,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨j0,hj0,rfl⟩ := Finset.mem_image.mp hj
  refine Finset.mem_image.mpr ⟨(a:ZMod p)*(i0:ZMod p)+(b:ZMod p)*(j0:ZMod p),
    linear_form_in_coefficientInterval p m a b i0 j0 (Finset.mem_Icc.mp hi0).2 (Finset.mem_Icc.mp hj0).2,?_⟩
  dsimp [modularLinearForm]
  rw [← hix,← hjy]
  ring

theorem sampled_projection_translation_sum (p m : ℕ) [Fact p.Prime] (hm : 0 < m)
    (H : Finset (ZMod p × ZMod p)) (a b : ℤ) (ha : (a:ZMod p) ≠ 0)
    (d : ZMod p) (hd : d ≠ 0) :
    ∑ t : ZMod p, ((sampledGraph H (positiveFieldInterval p m) (halfFieldInterval p m) d t).image
      (modularLinearForm p a b)).card ≤
      (2*coefficientWidth a b+1)*m*(H.image (modularLinearForm p a b)).card := by
  let A := H.image (modularLinearForm p a b)
  let I := coefficientInterval p m a b
  have he : (∑ t : ZMod p, (A ∩ fieldProgression I d ((a:ZMod p)*t)).card) =
      ∑ t : ZMod p, (A ∩ fieldProgression I d t).card := by
    apply Fintype.sum_equiv (Equiv.mulLeft₀ (a:ZMod p) ha)
    intro x
    rfl
  calc
    _ ≤ ∑ t : ZMod p, (A ∩ fieldProgression I d ((a:ZMod p)*t)).card :=
      Finset.sum_le_sum (fun t _ => Finset.card_le_card (sampled_projection_subset p m H a b d t))
    _ = A.card*I.card := by rw [he,progression_translation_first_moment A I d hd]
    _ ≤ A.card*((2*coefficientWidth a b+1)*m) := Nat.mul_le_mul_left _ (coefficientInterval_card p m hm a b)
    _ = _ := by ring

theorem sampled_projection_total_sum (p m : ℕ) [Fact p.Prime] (hm : 0 < m)
    (H : Finset (ZMod p × ZMod p)) (a b : ℤ) (ha : (a:ZMod p) ≠ 0) :
    ∑ z ∈ nonzeroTranslationSamples p,
      ((sampledGraph H (positiveFieldInterval p m) (halfFieldInterval p m) z.1 z.2).image
        (modularLinearForm p a b)).card ≤
      (p-1)*((2*coefficientWidth a b+1)*m*(H.image (modularLinearForm p a b)).card) := by
  unfold nonzeroTranslationSamples
  change (∑ z ∈ (Finset.univ.erase 0) ×ˢ (Finset.univ : Finset (ZMod p)), _) ≤ _
  rw [Finset.sum_product]
  calc
    _ ≤ ∑ d ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        (2*coefficientWidth a b+1)*m*(H.image (modularLinearForm p a b)).card :=
      Finset.sum_le_sum (fun d hd => sampled_projection_translation_sum p m hm H a b ha d (Finset.mem_erase.mp hd).1)
    _ = _ := by simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sampled_projection_subset
#print axioms KakeyaTwoScale.sampled_projection_translation_sum
#print axioms KakeyaTwoScale.sampled_projection_total_sum
