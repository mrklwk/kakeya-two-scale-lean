module
public import KakeyaTwoScale.NodeExponentUpdate

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped BigOperators Topology

section Iteration
variable {R₀ : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R₀ β C)
  (hproper : ∀ r ∈ R₀, r ≠ -1)

theorem eventually_updated_bound (M : ℕ) (hM : 2 ≤ M)
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop, ∀ G : Finset ArithmeticPoint,
      Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint) →
      (∀ r ∈ nestedGlobalSlopes hSD hproper M, (G.image (arithmeticProjection r)).card ≤ N) →
      (G.card:ℝ) ≤ A*(N:ℝ)^(realArithmeticStep β+102/(M:ℝ)) := by
  let nodes := (Finset.range M).biUnion (nestedSlopeLevels hSD hproper)
  let c := fun t => iterationBoundConstant β C (2^(nestedGlobalSlopes hSD hproper M).card)
    (outerSlopeFamily hSD hproper t).card
  let A := 2*(2:ℝ)^(nestedGlobalSlopes hSD hproper M).card+∑ t ∈ nodes, c t
  have hc : ∀ t, 0 < c t := fun t => Real.exp_pos _
  have hsum : 0 ≤ ∑ t ∈ nodes, c t := Finset.sum_nonneg (fun t _ => (hc t).le)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_dataset_comparison hSD hproper M hM hβ hC,
    eventually_ge_atTop (2:ℕ)] with N hN hN2
  intro G hd hp
  have hn : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : 0 ≤ (N:ℝ)^(realArithmeticStep β+102/(M:ℝ)) := Real.rpow_nonneg (by positivity) _
  rcases hN G hd hp with hs | hl
  · have hexp : (3:ℝ)/2 ≤ realArithmeticStep β+102/(M:ℝ) := by
      have h := arithmeticStep_above_three_halves β hβ
      have hh : (0:ℝ) ≤ 102/(M:ℝ) := by positivity
      linarith
    have h1 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hexp)
      (show 0 ≤ 2*(2:ℝ)^(nestedGlobalSlopes hSD hproper M).card by positivity)
    have h2 := mul_le_mul_of_nonneg_right
      (show 2*(2:ℝ)^(nestedGlobalSlopes hSD hproper M).card ≤ A by dsimp [A]; linarith) hpow
    exact hs.trans (h1.trans h2)
  · obtain ⟨k,hk,t,ht,hcenters,hlarge,hcomparison⟩ := hl
    have hx := node_exponent_update hSD hproper G N M k t ht hk hN2 hM hβ hβ2 hC hp hcenters hlarge hcomparison
    have htn : t ∈ nodes := Finset.mem_biUnion.mpr ⟨k,Finset.mem_range.mpr hk,ht⟩
    have hct : c t ≤ ∑ u ∈ nodes, c u := Finset.single_le_sum (fun u _ => (hc u).le) htn
    have hctA : c t ≤ A := by
      dsimp [A]
      have hz : (0:ℝ) ≤ 2*2^(nestedGlobalSlopes hSD hproper M).card := by positivity
      linarith
    exact hx.trans (mul_le_mul_of_nonneg_right hctA hpow)

/-- The fixed global set contains two distinct base projections, including
at small scales. This closes the bounded-scale tail without any SD input. -/
theorem global_base_slopes (M : ℕ) :
    (0:ℚ) ∈ nestedGlobalSlopes hSD hproper M ∧ (1:ℚ) ∈ nestedGlobalSlopes hSD hproper M := by
  have ht : rootSlopeTriple ∈ nestedSlopeLevels hSD hproper 0 := by simp [nestedSlopeLevels,slopeTreeLevels]
  have h := node_base_slopes_mem hSD hproper M 0 (Nat.zero_le _) rootSlopeTriple ht
  exact ⟨h.1,h.2.1⟩

/-- Upgrade an eventual bound to the full real-scale SD predicate. The
constant absorbs all bounded natural scales; flooring handles real scales. -/
theorem FiniteSDBound.of_eventual_nat {R : Finset ℚ} {e A : ℝ}
    (hzero : (0:ℚ) ∈ R) (hone : (1:ℚ) ∈ R) (he : 0 < e) (hA : 0 < A)
    (hev : ∀ᶠ N : ℕ in atTop, ∀ G : Finset ArithmeticPoint,
      Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint) →
      (∀ r ∈ R, (G.image (arithmeticProjection r)).card ≤ N) → (G.card:ℝ) ≤ A*(N:ℝ)^e) :
    ∃ B : ℝ, 0 < B ∧ FiniteSDBound R e B := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hev
  let B := A+(N₀:ℝ)^2
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : A ≤ B := by dsimp [B]; nlinarith [sq_nonneg (N₀:ℝ)]
  have hnat : ∀ N : ℕ, ∀ G : Finset ArithmeticPoint,
      Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint) →
      (∀ r ∈ R, (G.image (arithmeticProjection r)).card ≤ N) → (G.card:ℝ) ≤ B*(N:ℝ)^e := by
    intro N G hd hp
    by_cases hn : N₀ ≤ N
    · exact (hN₀ N hn G hd hp).trans (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (by positivity) _))
    · have hrough : (G.card:ℝ) ≤ (N:ℝ)^2 := by
        have h := finiteSD_two_slopes (0:ℚ) 1 (by norm_num) G hd N (by positivity)
          (by intro r hr; simp only [Finset.mem_insert,Finset.mem_singleton] at hr
              rcases hr with rfl | rfl
              · exact_mod_cast hp 0 hzero
              · exact_mod_cast hp 1 hone)
        simpa using h
      by_cases hNz : N = 0
      · subst N
        simpa [Real.zero_rpow (ne_of_gt he)] using hrough
      · have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        have hNN : (N:ℝ) ≤ N₀ := by exact_mod_cast (show N ≤ N₀ by omega)
        have hsq : (N:ℝ)^2 ≤ (N₀:ℝ)^2 := by nlinarith
        have hc : (N₀:ℝ)^2 ≤ B := by dsimp [B]; linarith
        have hpw := Real.one_le_rpow hN1 he.le
        exact hrough.trans (hsq.trans (hc.trans (by nlinarith)))
  refine ⟨B,hB,?_⟩
  intro G hd N hN hp
  have hfloor : ∀ r ∈ R, (G.image (arithmeticProjection r)).card ≤ Nat.floor N := by
    intro r hr
    exact (Nat.le_floor_iff hN).mpr (hp r hr)
  have hx := hnat (Nat.floor N) G hd hfloor
  have hpw := Real.rpow_le_rpow (Nat.cast_nonneg (Nat.floor N)) (Nat.floor_le hN) he.le
  exact hx.trans (mul_le_mul_of_nonneg_left hpw hB.le)

/-- A proved sums-differences update, with depth-dependent loss. No
iteration, nu-cap, mass-retention or corner-comparison hypothesis is used. -/
theorem FiniteSDBound.improve_with_depth (M : ℕ) (hM : 2 ≤ M)
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C) :
    ∃ B : ℝ, 0 < B ∧
      FiniteSDBound (nestedGlobalSlopes hSD hproper M) (realArithmeticStep β+102/(M:ℝ)) B := by
  obtain ⟨A,hA,he⟩ := eventually_updated_bound hSD hproper M hM hβ hβ2 hC
  have hexp : 0 < realArithmeticStep β+102/(M:ℝ) := by
    have h := arithmeticStep_above_three_halves β hβ
    have h' : (0:ℝ) ≤ 102/(M:ℝ) := by positivity
    linarith
  exact FiniteSDBound.of_eventual_nat (global_base_slopes hSD hproper M).1
    (global_base_slopes hSD hproper M).2 hexp hA he

end Iteration
end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_updated_bound
#print axioms KakeyaTwoScale.global_base_slopes
#print axioms KakeyaTwoScale.FiniteSDBound.of_eventual_nat
#print axioms KakeyaTwoScale.FiniteSDBound.improve_with_depth
