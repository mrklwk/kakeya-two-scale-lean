module
public import KakeyaTwoScale.RefinedFiberProjection
public import KakeyaTwoScale.SlopeTree

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def commonRefinement {A I : Type*} [DecidableEq A]
    (S : Finset A) (F : Finset I) (R : I → Finset A) : Finset A :=
  S.filter (fun x => ∀ i ∈ F, x ∈ R i)

theorem commonRefinement_loss {A I : Type*} [DecidableEq A]
    (S : Finset A) (F : Finset I) (R : I → Finset A)
    (hR : ∀ i ∈ F, R i ⊆ S) :
    S.card-(commonRefinement S F R).card ≤ ∑ i ∈ F, (S.card-(R i).card) := by
  have h := simultaneous_filter_loss S F (fun i x => x ∈ R i)
  change S.card-(commonRefinement S F R).card ≤ _ at h
  apply h.trans
  apply Finset.sum_le_sum
  intro i hi
  have he : S.filter (fun x => x ∉ R i) = S \ R i := by ext x; simp
  rw [he,Finset.card_sdiff_of_subset (hR i hi)]

/-- Construct the entire intersection/popularity/stability refinement from
actual incoming subsets. The total deletion is derived from their losses,
and all final-fiber projection bounds follow from the construction. -/
theorem exists_intersected_projection_refinement {A B D I J : Type*}
    [DecidableEq A] [DecidableEq D] [DecidableEq I] [DecidableEq J]
    (S : Finset A) (F : Finset I) (R : I → Finset A) (f : I → A → B)
    (d : ℕ) (Jset : Finset J) (g : J → A → D)
    (hR : ∀ i ∈ F, R i ⊆ S) :
    ∃ Q ⊆ commonRefinement S F R,
      d*(S.card-Q.card) ≤ 2*d*(∑ i ∈ F, (S.card-(R i).card))+2*F.card*S.card ∧
      ∀ j ∈ Jset, ∀ i ∈ F,
        (∀ x ∈ S, ∀ y ∈ S, f i x = f i y → g j x = g j y) →
        ∀ z : D, Q.card*((Q.filter (fun x => g j x = z)).image (f i)).card ≤
          (d*((R i).image (f i)).card)*(2*Jset.card)*(Q.filter (fun x => g j x = z)).card := by
  let R₀ := commonRefinement S F R
  let T := fun i => (R i).image (f i)
  have hR₀ : R₀ ⊆ S := Finset.filter_subset _ _
  have hm : ∀ i ∈ F.toList, ∀ x ∈ R₀, f i x ∈ T i := by
    intro i hi x hx
    have hi' : i ∈ F := by simpa using hi
    exact Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).2 i hi',rfl⟩
  obtain ⟨Q,hQR,hloss,hproj⟩ := exists_refinement_projection_bounds S R₀ T f F.toList d Jset g hR₀ hm
  have hQ₀ := hQR.trans (popularRounds_subset T f d F.toList R₀)
  refine ⟨Q,hQ₀,?_,?_⟩
  · have h0 := commonRefinement_loss S F R hR
    have hc := Finset.card_le_card hR₀
    have hd := Nat.mul_le_mul_left (2*d) h0
    have hf := Nat.mul_le_mul_left (2*F.card) hc
    simp only [Finset.length_toList] at hloss
    change S.card-R₀.card ≤ _ at h0
    nlinarith
  · intro j hj i hi hdet z
    exact hproj j hj i (by simpa using hi) hdet z

/-- A concrete final popularity/stability refinement retaining at least
half the corners, with explicit constant 2(4|F|+1) on every selected fiber.
No half-mass retention premise is assumed. -/
theorem exists_half_fiber_refinement {A B D I : Type*}
    [DecidableEq A] [DecidableEq D] [DecidableEq I]
    (S : Finset A) (F : Finset I) (f : I → A → B) (g : A → D) :
    ∃ Q ⊆ S, S.card ≤ 2*Q.card ∧
      ∀ i ∈ F, (∀ x ∈ S, ∀ y ∈ S, f i x = f i y → g x = g y) →
      ∀ z : D, Q.card*((Q.filter (fun x => g x = z)).image (f i)).card ≤
        (2*(4*F.card+1)*(S.image (f i)).card)*(Q.filter (fun x => g x = z)).card := by
  let T := fun i => S.image (f i)
  let d := 4*F.card+1
  obtain ⟨Q,hQ,hloss,hproj⟩ := exists_refinement_projection_bounds S S T f F.toList d
    ({()} : Finset Unit) (fun _ => g) (Finset.Subset.refl _)
    (fun i _ x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  have hQS := hQ.trans (popularRounds_subset T f d F.toList S)
  have hc := Finset.card_le_card hQS
  have hl : (4*F.card+1)*(S.card-Q.card) ≤ 2*F.card*S.card := by
    simpa only [d, Nat.sub_self,Nat.mul_zero,zero_add,Finset.length_toList] using hloss
  have he : 2*F.card*(S.card-Q.card)+2*F.card*Q.card = 2*F.card*S.card := by
    rw [← Nat.mul_add,Nat.sub_add_cancel hc]
  have hhalf : S.card ≤ 2*Q.card := by
    have hd : S.card-Q.card ≤ Q.card := by
      by_contra hh
      have hm := Nat.mul_le_mul_left (2*F.card) (Nat.le_of_lt (Nat.lt_of_not_ge hh))
      nlinarith
    omega
  refine ⟨Q,hQS,hhalf,?_⟩
  intro i hi hdet z
  have h := hproj () (by simp) i (by simpa using hi) hdet z
  simpa [T,d,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.commonRefinement_loss
#print axioms KakeyaTwoScale.exists_intersected_projection_refinement

#print axioms KakeyaTwoScale.exists_half_fiber_refinement
