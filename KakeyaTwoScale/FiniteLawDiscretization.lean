module
public import KakeyaTwoScale.IntegerDiscretization

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology BigOperators

def pushEntropy {A B : Type*} [Fintype A] [DecidableEq B] (q : A → ℝ) (f : A → B) : ℝ :=
  finiteEntropy (Finset.univ.image f) (finitePushLaw Finset.univ q f)

theorem IntegerEntropyModel.error_transfer {R : Finset ℚ} {H Hv H' Hv' ε : ℝ}
    {Hp Hp' : ℚ → ℝ} {n : ℕ} {G : Finset (ℤ × ℤ)}
    (h : IntegerEntropyModel R H Hv Hp n (ε/3) G)
    (hH : |H-H'| < ε/3) (hV : |Hv-Hv'| < ε/3)
    (hP : ∀ r ∈ R, |Hp r-Hp' r| < ε/3) :
    IntegerEntropyModel R H' Hv' Hp' n ε G := by
  have hε : 0 < ε := by have := abs_nonneg (H-H'); linarith
  have hstep (x A B : ℝ) (h1 : |x-A| < ε/3) (h2 : |A-B| < ε/3) : |x-B| < ε := by
    have ht := abs_sub_le x A B
    linarith
  refine ⟨h.1,hstep _ _ _ h.2.1 hH,hstep _ _ _ h.2.2.1 hV,?_,?_,h.2.2.2.2.2⟩
  · intro r hr
    exact hstep _ _ _ (h.2.2.2.1 r hr) (hP r hr)
  · intro y hy
    have hf := h.2.2.2.2.1 y hy
    have ht := abs_sub_le (Real.log ((G.filter (fun v => v.2 = y)).card:ℝ)/(n:ℝ)) (H-Hv) (H'-Hv')
    have hc := abs_sub (H-H') (Hv-Hv')
    have he : (H-H')-(Hv-Hv') = (H-Hv)-(H'-Hv') := by ring
    rw [he] at hc
    linarith

/-- Finite-support entropy discretization into actual integer pairs at
arbitrarily large positive lengths. All real normalized laws, including zero
masses, are handled by proved approximation. Errors are additive in normalized
natural logarithms. Uniform vertical fibers are exact. -/
theorem finite_probability_integer_discretization {A : Type*} [Fintype A]
    (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (hsum : ∑ a, q a = 1)
    (f : A → ArithmeticPoint) (R : Finset ℚ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ G : Finset (ℤ × ℤ),
      IntegerEntropyModel R (pushEntropy q f) (pushEntropy q (Prod.snd ∘ f))
        (fun r => pushEntropy q (arithmeticProjection r ∘ f)) n ε G := by
  let c := fun k a => roundedCount (q a) k
  have hε3 : 0 < ε/3 := by positivity
  have hJ := (countedWord_entropy_tendsto q hq hsum f).eventually (Metric.ball_mem_nhds _ hε3)
  have hV := (countedWord_entropy_tendsto q hq hsum (Prod.snd ∘ f)).eventually (Metric.ball_mem_nhds _ hε3)
  have hP : ∀ r ∈ R, ∀ᶠ k : ℕ in atTop,
      |empiricalEntropy (countedWord (c k) (arithmeticProjection r ∘ f))-
        pushEntropy q (arithmeticProjection r ∘ f)| < ε/3 := by
    intro r _
    have h := (countedWord_entropy_tendsto q hq hsum (arithmeticProjection r ∘ f)).eventually
      (Metric.ball_mem_nhds _ hε3)
    simpa only [Metric.mem_ball,Real.dist_eq,pushEntropy,c] using h
  have hevent : ∀ᶠ k : ℕ in atTop,
      0 < ∑ a, c k a ∧
      |empiricalEntropy (countedWord (c k) f)-pushEntropy q f| < ε/3 ∧
      |empiricalEntropy (countedWord (c k) (Prod.snd ∘ f))-pushEntropy q (Prod.snd ∘ f)| < ε/3 ∧
      ∀ r ∈ R, |empiricalEntropy (countedWord (c k) (arithmeticProjection r ∘ f))-
        pushEntropy q (arithmeticProjection r ∘ f)| < ε/3 := by
    filter_upwards [roundedCount_total_eventually_pos q hq hsum,hJ,hV,(eventually_all_finset R).mpr hP]
      with k hk hj hv hp
    exact ⟨hk,by simpa only [Metric.mem_ball,Real.dist_eq,pushEntropy,c] using hj,
      by simpa only [Metric.mem_ball,Real.dist_eq,pushEntropy,c] using hv,hp⟩
  obtain ⟨k,hk,hj,hv,hp⟩ := hevent.exists
  let I := Σ a : A, Fin (c k a)
  have hI : 0 < Fintype.card I := by simpa [I] using hk
  have : Nonempty I := Fintype.card_pos_iff.mp hI
  let w : I → ArithmeticPoint := countedWord (c k) f
  have he (g : ArithmeticPoint → ℚ) : g ∘ w = countedWord (c k) (g ∘ f) := rfl
  obtain ⟨j,⟨G,hG⟩,hjN⟩ := ((empirical_integer_discretization w R (ε/3) hε3).and
    (eventually_ge_atTop (max N 1))).exists
  refine ⟨Fintype.card I*j,?_,Nat.mul_pos hI (by omega),G,?_⟩
  · exact (le_trans (le_max_left N 1) hjN).trans (Nat.le_mul_of_pos_left j hI)
  · apply hG.error_transfer
    · exact hj
    · simpa only [he] using hv
    · intro r hr
      simpa only [he] using hp r hr

end KakeyaTwoScale
#print axioms KakeyaTwoScale.IntegerEntropyModel.error_transfer
#print axioms KakeyaTwoScale.finite_probability_integer_discretization
