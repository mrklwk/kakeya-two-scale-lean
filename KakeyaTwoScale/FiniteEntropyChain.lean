module
public import KakeyaTwoScale.ProjectionLaw

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem finitePushLaw_pos {A B : Type*} [DecidableEq B]
    (S : Finset A) (q : A → ℝ) (f : A → B)
    (hq : ∀ x ∈ S, 0 < q x) {y : B} (hy : y ∈ S.image f) :
    0 < finitePushLaw S q f y := by
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
  exact Finset.sum_pos (fun x hx => hq x (Finset.mem_filter.mp hx).1)
    ⟨x,Finset.mem_filter.mpr ⟨hx,hxy⟩⟩

theorem finiteConditionalLaw_sum {A B : Type*} [DecidableEq B]
    (S : Finset A) (q : A → ℝ) (f : A → B)
    (hq : ∀ x ∈ S, 0 < q x) {y : B} (hy : y ∈ S.image f) :
    ∑ x ∈ S.filter (fun x => f x = y), q x/finitePushLaw S q f y = 1 := by
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (finitePushLaw_pos S q f hq hy))

theorem fiber_entropy_decomposition {A B : Type*} [DecidableEq B]
    (S : Finset A) (q : A → ℝ) (f : A → B)
    (hq : ∀ x ∈ S, 0 < q x) {y : B} (hy : y ∈ S.image f) :
    finitePushLaw S q f y * finiteEntropy (S.filter (fun x => f x = y))
      (fun x => q x/finitePushLaw S q f y) =
      -(∑ x ∈ S.filter (fun x => f x = y), q x*Real.log (q x))+
        finitePushLaw S q f y*Real.log (finitePushLaw S q f y) := by
  let T := S.filter (fun x => f x = y)
  let p := finitePushLaw S q f y
  have hp : 0 < p := finitePushLaw_pos S q f hq hy
  have hterm : ∀ x ∈ T, p*(q x/p*Real.log (q x/p)) =
      q x*Real.log (q x)-q x*Real.log p := by
    intro x hx
    have hx' := hq x (Finset.mem_filter.mp hx).1
    rw [Real.log_div (ne_of_gt hx') (ne_of_gt hp)]
    field_simp
  change p*(-∑ x ∈ T, q x/p*Real.log (q x/p)) = _
  rw [mul_neg,Finset.mul_sum,Finset.sum_congr rfl hterm,Finset.sum_sub_distrib,← Finset.sum_mul]
  change -( (∑ x ∈ T, q x*Real.log (q x))-p*Real.log p) = _
  ring

/-- Shannon's chain rule on an actual finite law, with its conditional
probabilities explicitly normalized. Strict positivity is only required on
the listed support, which may always exclude zero-mass points. -/
theorem finiteEntropy_chain_rule {A B : Type*} [DecidableEq B]
    (S : Finset A) (q : A → ℝ) (f : A → B)
    (hq : ∀ x ∈ S, 0 < q x) :
    finiteEntropy S q = finiteEntropy (S.image f) (finitePushLaw S q f)+
      ∑ y ∈ S.image f, finitePushLaw S q f y *
        finiteEntropy (S.filter (fun x => f x = y)) (fun x => q x/finitePushLaw S q f y) := by
  rw [Finset.sum_congr rfl (fun y hy => fiber_entropy_decomposition S q f hq hy),Finset.sum_add_distrib]
  have hsum : (∑ y ∈ S.image f, ∑ x ∈ S.filter (fun x => f x = y), q x*Real.log (q x)) =
      ∑ x ∈ S, q x*Real.log (q x) :=
    Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
  rw [Finset.sum_neg_distrib,hsum]
  unfold finiteEntropy
  ring

/-- Finite entropy is continuous even when a coordinate tends to zero.
This supplies the continuity side of a future rational approximation step. -/
theorem continuous_finiteEntropy {A : Type*} (S : Finset A) :
    Continuous (fun q : A → ℝ => finiteEntropy S q) := by
  apply Continuous.neg
  exact continuous_finsetSum S (fun x _ => Real.continuous_mul_log.comp (continuous_apply x))

/-- Pushforward entropy is continuous on the fixed finite support; no
strict-positivity hypothesis is needed for this statement. -/
theorem continuous_projection_entropy {A B : Type*} [DecidableEq B]
    (S : Finset A) (f : A → B) :
    Continuous (fun q : A → ℝ => finiteEntropy (S.image f) (finitePushLaw S q f)) := by
  apply (continuous_finiteEntropy (S.image f)).comp
  apply continuous_pi
  intro y
  exact continuous_finsetSum _ (fun x _ => continuous_apply x)

/-- Values of an injective pushforward are exactly the original masses. -/
theorem finitePushLaw_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (q : A → ℝ) (f : A → B) (hi : Set.InjOn f (↑S : Set A))
    {x : A} (hx : x ∈ S) : finitePushLaw S q f (f x) = q x := by
  have he : S.filter (fun y => f y = f x) = {x} := by
    ext y
    constructor
    · intro hy
      obtain ⟨hy,he⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_singleton.mpr (hi hy hx he)
    · intro hy
      have he := Finset.mem_singleton.mp hy
      subst y
      exact Finset.mem_filter.mpr ⟨hx,rfl⟩
  simp [finitePushLaw,he]

/-- Rational rescalings and finite encoders preserve entropy whenever they
are injective on the actual support. -/
theorem finiteEntropy_push_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (q : A → ℝ) (f : A → B) (hi : Set.InjOn f (↑S : Set A)) :
    finiteEntropy (S.image f) (finitePushLaw S q f) = finiteEntropy S q := by
  unfold finiteEntropy
  rw [Finset.sum_image hi]
  congr 1
  exact Finset.sum_congr rfl (fun x hx => by rw [finitePushLaw_injective S q f hi hx])

/-- Removing zero masses changes neither entropy nor the represented law
on the positive support. -/
theorem finiteEntropy_filter_pos {A : Type*} (S : Finset A) (q : A → ℝ)
    (hq : ∀ x ∈ S, 0 ≤ q x) :
    finiteEntropy (S.filter (fun x => 0 < q x)) q = finiteEntropy S q := by
  unfold finiteEntropy
  congr 1
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hx hn
  have hn' : ¬0 < q x := by intro hh; exact hn (Finset.mem_filter.mpr ⟨hx,hh⟩)
  have hz : q x = 0 := le_antisymm (le_of_not_gt hn') (hq x hx)
  simp [hz]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finitePushLaw_pos
#print axioms KakeyaTwoScale.finiteConditionalLaw_sum
#print axioms KakeyaTwoScale.fiber_entropy_decomposition
#print axioms KakeyaTwoScale.finiteEntropy_chain_rule
#print axioms KakeyaTwoScale.continuous_finiteEntropy
#print axioms KakeyaTwoScale.continuous_projection_entropy

#print axioms KakeyaTwoScale.finitePushLaw_injective
#print axioms KakeyaTwoScale.finiteEntropy_push_injective
#print axioms KakeyaTwoScale.finiteEntropy_filter_pos
