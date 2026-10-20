module
public import KakeyaTwoScale.IntegerTypeClasses
public import KakeyaTwoScale.CountedLaws

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology BigOperators

/-- Additive logarithmic-error formulation; natural logarithms and actual
positive word length are used. Every vertical fiber has the same size. -/
def IntegerEntropyModel (R : Finset ℚ) (H Hv : ℝ) (Hp : ℚ → ℝ)
    (n : ℕ) (ε : ℝ) (G : Finset (ℤ × ℤ)) : Prop :=
  G.Nonempty ∧
  |Real.log (G.card:ℝ)/(n:ℝ)-H| < ε ∧
  |Real.log ((G.image Prod.snd).card:ℝ)/(n:ℝ)-Hv| < ε ∧
  (∀ r ∈ R, |Real.log ((G.image (integerProjection r)).card:ℝ)/(n:ℝ)-Hp r| < ε) ∧
  (∀ y ∈ G.image Prod.snd,
    |Real.log ((G.filter (fun v => v.2 = y)).card:ℝ)/(n:ℝ)-(H-Hv)| < ε) ∧
  (∀ y ∈ G.image Prod.snd, ∀ z ∈ G.image Prod.snd,
    (G.filter (fun v => v.2 = y)).card = (G.filter (fun v => v.2 = z)).card)

theorem empirical_integer_discretization {I : Type*}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (w : I → ArithmeticPoint) (R : Finset ℚ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∃ G : Finset (ℤ × ℤ),
      IntegerEntropyModel R (empiricalEntropy w) (empiricalEntropy (Prod.snd ∘ w))
        (fun r => empiricalEntropy (arithmeticProjection r ∘ w)) (Fintype.card I*k) ε G := by
  have h := empirical_type_discretization w R arithmeticProjection Prod.snd ε hε
  have hv := (repeated_type_entropy_tendsto (Prod.snd ∘ w)).eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [h,hv] with k hk hkv
  obtain ⟨G,hG,hV,hP,hF⟩ := integer_type_class_realization (repeatedWord w k) R
  have he (f : ArithmeticPoint → ℚ) : f ∘ repeatedWord w k = repeatedWord (f ∘ w) k := rfl
  refine ⟨G,?_,?_,?_,?_,?_,?_⟩
  · apply Finset.card_pos.mp
    rw [hG]
    exact Finset.card_pos.mpr (wordTypeClass_nonempty _)
  · simpa only [hG,Nat.cast_mul] using hk.1
  · simpa only [hV,he,Nat.cast_mul,Metric.mem_ball,Real.dist_eq,empiricalEntropy] using hkv
  · intro r hr
    simpa only [hP r hr,he,Nat.cast_mul] using hk.2.1 r hr
  · intro y hy
    simpa only [hF y hy,Nat.cast_mul] using hk.2.2.1
  · intro y hy z hz
    rw [hF y hy,hF z hz]

/-- Empirical entropies of normalized rounded-count laws converge to the
entropy of the actual finite pushforward law, including zero masses. -/
theorem countedWord_entropy_tendsto {A B : Type*} [Fintype A] [DecidableEq B]
    (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (hsum : ∑ a, q a = 1) (f : A → B) :
    Tendsto (fun k : ℕ => empiricalEntropy (countedWord (fun a => roundedCount (q a) k) f))
      atTop (𝓝 (finiteEntropy (Finset.univ.image f) (finitePushLaw Finset.univ q f))) := by
  have h := ((continuous_projection_entropy Finset.univ f).tendsto q).comp
    (normalized_roundedCounts_tendsto q hq hsum)
  simpa only [countedWord_entropy,Function.comp_def] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.empirical_integer_discretization
#print axioms KakeyaTwoScale.countedWord_entropy_tendsto
