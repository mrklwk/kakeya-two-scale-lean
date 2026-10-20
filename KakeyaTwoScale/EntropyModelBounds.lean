module
public import KakeyaTwoScale.FiniteLawDiscretization

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem integer_fiber_projection_card_le (G : Finset (ℤ × ℤ)) (y : ℤ) (r : ℚ) :
    (G.filter (fun v => v.2=y)).card ≤ (G.image (integerProjection r)).card := by
  let S := G.filter (fun v => v.2=y)
  have hinj : Set.InjOn (integerProjection r) (S:Set (ℤ × ℤ)) := by
    intro v hv w hw he
    have hvy := (Finset.mem_filter.mp hv).2
    have hwy := (Finset.mem_filter.mp hw).2
    apply Prod.ext
    · have h : (v.1:ℚ) = (w.1:ℚ) := by
        dsimp [integerProjection] at he
        rw [hvy,hwy] at he
        linarith
      exact_mod_cast h
    · exact hvy.trans hwy.symm
  calc
    _ = (S.image (integerProjection r)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/-- Conditional entropy is nonnegative and bounded by every nonvertical
projection entropy, including for laws with zero masses. This follows from
actual integer models and fiberwise injectivity. -/
theorem finite_conditional_entropy_bounds {A : Type*} [Fintype A]
    (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (hsum : ∑ a, q a = 1)
    (f : A → ArithmeticPoint) (r : ℚ) :
    0 ≤ pushEntropy q f-pushEntropy q (Prod.snd ∘ f) ∧
    pushEntropy q f-pushEntropy q (Prod.snd ∘ f) ≤
      pushEntropy q (arithmeticProjection r ∘ f) := by
  let F := pushEntropy q f-pushEntropy q (Prod.snd ∘ f)
  let P := pushEntropy q (arithmeticProjection r ∘ f)
  have approx (ε : ℝ) (hε : 0 < ε) : -ε < F ∧ F < P+2*ε := by
    obtain ⟨n,_,hn,G,hG⟩ := finite_probability_integer_discretization q hq hsum f {r} ε hε 1
    obtain ⟨v,hv⟩ := hG.1
    have hy : v.2 ∈ G.image Prod.snd := Finset.mem_image.mpr ⟨v,hv,rfl⟩
    have hfpos : 0 < (G.filter (fun w => w.2=v.2)).card :=
      Finset.card_pos.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
    have hlog : 0 ≤ Real.log ((G.filter (fun w => w.2=v.2)).card:ℝ) :=
      Real.log_nonneg (by exact_mod_cast hfpos)
    have hdiv : 0 ≤ Real.log ((G.filter (fun w => w.2=v.2)).card:ℝ)/(n:ℝ) :=
      div_nonneg hlog (Nat.cast_nonneg _)
    have hle := Real.log_le_log (show (0:ℝ) < (G.filter (fun w => w.2=v.2)).card by exact_mod_cast hfpos)
      (show ((G.filter (fun w => w.2=v.2)).card:ℝ) ≤ (G.image (integerProjection r)).card by
        exact_mod_cast integer_fiber_projection_card_le G v.2 r)
    have hdivle := div_le_div_of_nonneg_right hle (Nat.cast_nonneg n)
    have hf := abs_lt.mp (hG.2.2.2.2.1 v.2 hy)
    have hp := abs_lt.mp (hG.2.2.2.1 r (Finset.mem_singleton_self r))
    dsimp [F,P]
    constructor <;> linarith
  constructor
  · by_contra h
    have hF : F < 0 := lt_of_not_ge h
    have h := (approx (-F/2) (by linarith)).1
    linarith
  · by_contra h
    have hPF : P < F := lt_of_not_ge h
    have h := (approx ((F-P)/4) (by linarith)).2
    linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.integer_fiber_projection_card_le
#print axioms KakeyaTwoScale.finite_conditional_entropy_bounds
