module
public import KakeyaTwoScale.FiniteLawDiscretization
public import KakeyaTwoScale.FiniteSDEntropy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Entropy is unchanged by an injective relabeling of a finite pushforward.
The law may contain zero masses. -/
theorem pushEntropy_injective_post {A B C : Type*} [Fintype A]
    [DecidableEq B] [DecidableEq C] (q : A → ℝ) (f : A → B) (g : B → C)
    (hg : Function.Injective g) : pushEntropy q (g ∘ f) = pushEntropy q f := by
  have hp (y : B) : finitePushLaw Finset.univ q (g ∘ f) (g y) = finitePushLaw Finset.univ q f y := by
    unfold finitePushLaw
    congr 1
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply,hg.eq_iff]
  unfold pushEntropy finiteEntropy
  rw [← Finset.image_image,Finset.sum_image (fun x _ y _ h => hg h)]
  congr 1
  exact Finset.sum_congr rfl (fun y _ => by rw [hp])

def verticalSlope (s : ℚ) : ℚ := -s/(1+s)
def differenceToVertical (v : ArithmeticPoint) : ArithmeticPoint := (v.1,v.1-v.2)

theorem vertical_projection_identity (s : ℚ) (hs : s ≠ -1) (v : ArithmeticPoint) :
    arithmeticProjection s (differenceToVertical v) = (1+s)*arithmeticProjection (verticalSlope s) v := by
  have hden : 1+s ≠ 0 := by intro h; apply hs; linarith
  dsimp [arithmeticProjection,differenceToVertical,verticalSlope]
  field_simp
  ring

/-- Converts the proved difference-coordinate entropy inequality to the
vertical-coordinate convention used in PZ. The slope set changes once, before
the probability law is chosen, and the exponent is unchanged. -/
theorem FiniteSDBound.vertical_entropy {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 0 < β) (hR : R.Nonempty)
    (hproper : ∀ s ∈ R, s ≠ -1)
    {A : Type*} [Fintype A] (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (hsum : ∑ a, q a = 1)
    (f : A → ArithmeticPoint) :
    pushEntropy q (Prod.snd ∘ f) ≤
      β*(R.image verticalSlope).sup' (hR.image _) (fun r => pushEntropy q (arithmeticProjection r ∘ f)) := by
  let g := differenceToVertical ∘ f
  have h := hSD.finite_probability_entropy hβ hR q hq hsum g
  change pushEntropy q (arithmeticProjection (-1) ∘ g) ≤
    β*R.sup' hR (fun s => pushEntropy q (arithmeticProjection s ∘ g)) at h
  have he0 : arithmeticProjection (-1) ∘ g = Prod.snd ∘ f := by
    funext a
    simp [g,differenceToVertical,arithmeticProjection]
  rw [he0] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hβ.le
  apply Finset.sup'_le hR
  intro s hs
  have hn : 1+s ≠ 0 := by intro hh; have := hproper s hs; apply this; linarith
  have he : arithmeticProjection s ∘ g =
      (fun z : ℚ => (1+s)*z) ∘ (arithmeticProjection (verticalSlope s) ∘ f) := by
    funext a
    exact vertical_projection_identity s (hproper s hs) (f a)
  rw [he,pushEntropy_injective_post q (arithmeticProjection (verticalSlope s) ∘ f)
    (fun z : ℚ => (1+s)*z) (fun _ _ h => mul_left_cancel₀ hn h)]
  exact Finset.le_sup' (fun r => pushEntropy q (arithmeticProjection r ∘ f))
    (show verticalSlope s ∈ R.image verticalSlope from Finset.mem_image.mpr ⟨s,hs,rfl⟩)

theorem finite_vertical_entropy_625_373 :
    ∃ R : Finset ℚ, ∃ hR : R.Nonempty,
      ∀ (A : Type) [Fintype A] (q : A → ℝ), (∀ a, 0 ≤ q a) → (∑ a, q a = 1) →
      ∀ f : A → ArithmeticPoint,
        pushEntropy q (Prod.snd ∘ f) ≤ (625/373:ℝ)*R.sup' hR
          (fun r => pushEntropy q (arithmeticProjection r ∘ f)) := by
  obtain ⟨R,hproper,hSD⟩ := finiteSD_625_373_constant_one
  have hR := hSD.slopes_nonempty (by norm_num)
  exact ⟨R.image verticalSlope,hR.image _,fun A _ q hq hsum f =>
    hSD.vertical_entropy (by norm_num) hR hproper q hq hsum f⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.pushEntropy_injective_post
#print axioms KakeyaTwoScale.vertical_projection_identity
#print axioms KakeyaTwoScale.FiniteSDBound.vertical_entropy
#print axioms KakeyaTwoScale.finite_vertical_entropy_625_373
