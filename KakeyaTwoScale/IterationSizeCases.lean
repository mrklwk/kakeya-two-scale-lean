module
public import KakeyaTwoScale.VerticalDataset
public import KakeyaTwoScale.IterationThresholds

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def realArithmeticStep (β : ℝ) : ℝ := (3*β^2+2*β-2)/(β^2+3*β-2)

theorem arithmeticStep_above_three_halves (β : ℝ) (hβ : 1 < β) :
    (3:ℝ)/2 < realArithmeticStep β := by
  have hd : 0 < β^2+3*β-2 := by nlinarith
  unfold realArithmeticStep
  apply (lt_div_iff₀ hd).mpr
  have hprod := mul_pos (by linarith : 0 < β-1) (by linarith : 0 < 3*β-2)
  nlinarith

theorem small_set_update_bound (g N A β : ℝ) (hN : 1 ≤ N) (hA : 0 ≤ A)
    (hβ : 1 < β) (hg : g ≤ A*N^((3:ℝ)/2)) :
    g ≤ A*N^(realArithmeticStep β) :=
  hg.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hN (arithmeticStep_above_three_halves β hβ).le) hA)

/-- The square-size condition derives the center-size requirement and
W≥N² for every balanced family. No rounding-size premise is assumed. -/
theorem balanced_large_size {A B I : Type*} (S : Finset A) (T : I → Finset B)
    (f : I → A → B) (sl : List I) (N : ℕ) (hN : 0 < N)
    (hf : ∀ i ∈ sl, ∀ x ∈ S, f i x ∈ T i)
    (hsize : 4*(2^sl.length)^2*N^3 ≤ S.card^2) :
    2*N ≤ (popularRounds T f 2 sl S).card ∧
      ∀ i ∈ sl, (T i).card ≤ N → N^2 ≤ (balancedVertical S T f sl N i).card := by
  let p := 2^sl.length
  let R := popularRounds T f 2 sl S
  have hp : 0 < p := by dsimp [p]; positivity
  have hret := popularRounds_half T f sl S hf
  change S.card ≤ p*R.card at hret
  have hsq : S.card^2 ≤ p^2*R.card^2 := by nlinarith [Nat.mul_le_mul hret hret]
  have hN1 : 1 ≤ N := hN
  have hn := Nat.mul_le_mul_left (4*p^2*N^2) hN1
  have hprod : p^2*(4*N^2) ≤ p^2*R.card^2 := by
    change 4*p^2*N^3 ≤ S.card^2 at hsize
    nlinarith
  have hcentersq := Nat.le_of_mul_le_mul_left hprod (Nat.pow_pos hp)
  have hcenter : 2*N ≤ R.card := by nlinarith
  refine ⟨hcenter,?_⟩
  intro i hi hTi
  have hmass := (balancedVertical_mass S T f sl N hi hf hTi hN hcenter).1
  have he : (4*p^2*N)*N^2 ≤ (4*p^2*N)*(balancedVertical S T f sl N i).card := by
    change 4*p^2*N^3 ≤ S.card^2 at hsize
    change S.card^2 ≤ 4*p^2*N*(balancedVertical S T f sl N i).card at hmass
    nlinarith
  exact Nat.le_of_mul_le_mul_left he (by positivity)

/-- Exhaustive small/large split for the actual rational dataset. In the
large branch every relevant pair family has at least N² points; the small
branch already has the N^(3/2) bound, with a fixed list-dependent constant. -/
theorem rational_balanced_size_cases (G : Finset ArithmeticPoint) (sl : List ℚ)
    (N : ℕ) (hN : 0 < N)
    (hproj : ∀ r ∈ sl, (G.image (arithmeticProjection r)).card ≤ N) :
    (G.card:ℝ) ≤ 2*(2:ℝ)^sl.length*(N:ℝ)^((3:ℝ)/2) ∨
      (2*N ≤ (popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G).card ∧
        ∀ r ∈ sl, N^2 ≤ (rationalBalancedPairs G sl N r).card) := by
  by_cases hs : 4*(2^sl.length)^2*N^3 ≤ G.card^2
  · right
    have h := balanced_large_size G (fun r => G.image (arithmeticProjection r)) arithmeticProjection sl N hN
      (fun r _ x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) hs
    refine ⟨h.1,?_⟩
    intro r hr
    rw [rationalBalancedPairs,verticalPairSet_card]
    exact h.2 r hr (hproj r hr)
  · left
    have hs' : (G.card:ℝ)^2 ≤ 4*((2:ℝ)^sl.length)^2*(N:ℝ)^3 := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hs))
    have hn0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
    have hp : 0 ≤ (N:ℝ)^((3:ℝ)/2) := Real.rpow_nonneg hn0 _
    have he : ((N:ℝ)^((3:ℝ)/2))^2 = (N:ℝ)^3 := by
      rw [← Real.rpow_two,← Real.rpow_mul hn0]
      norm_num
    have hright : 0 ≤ 2*(2:ℝ)^sl.length*(N:ℝ)^((3:ℝ)/2) := by positivity
    nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.arithmeticStep_above_three_halves
#print axioms KakeyaTwoScale.small_set_update_bound
#print axioms KakeyaTwoScale.balanced_large_size
#print axioms KakeyaTwoScale.rational_balanced_size_cases
