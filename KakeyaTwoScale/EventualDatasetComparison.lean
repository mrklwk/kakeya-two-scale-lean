module
public import KakeyaTwoScale.NodeFinalComparison

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

section Iteration
variable {R₀ : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R₀ β C)
  (hproper : ∀ r ∈ R₀, r ≠ -1)

def nodeComparisonBound (G : Finset ArithmeticPoint) (N M k d : ℕ)
    (t : ProperSlopeTriple) : Prop :=
    let sl := (nestedGlobalSlopes hSD hproper M).toList
    let W := (rationalBalancedPairs G sl N t.r2).card
    let J := outerSlopeFamily hSD hproper t
    let E := iterationMassThreshold N W M k
    let L := iterationFiberThreshold N W M k
    let Lnext := iterationFiberThreshold N W M (k+1)
    let l := (popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G).card/(2*N)
    let B := (W:ℝ)/(C*((8*d*J.card:ℝ)/Lnext)^β)^(-1/(β-1))
    ∃ H : ℕ, 0 < H ∧ l*E ≤ 2*H ∧
      (C*(4*(4*(J.card:ℝ)+1)*N*B/H)^β)^(-1/(β-1)) ≤ N*L

/-- Fully instantiated finite iteration comparison for all sufficiently
large scales. Every dataset, refinement and corner is constructed; the
numerical budget is now proved uniformly before G is supplied. -/
theorem eventually_dataset_comparison (M : ℕ) (hM : 2 ≤ M) (hβ : 1 < β) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ∀ G : Finset ArithmeticPoint,
      Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint) →
      (∀ r ∈ nestedGlobalSlopes hSD hproper M, (G.image (arithmeticProjection r)).card ≤ N) →
      (G.card:ℝ) ≤ 2*(2:ℝ)^(nestedGlobalSlopes hSD hproper M).card*(N:ℝ)^((3:ℝ)/2) ∨
      ∃ k < M, ∃ t ∈ nestedSlopeLevels hSD hproper k,
        2*N ≤ (popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2
          (nestedGlobalSlopes hSD hproper M).toList G).card ∧
        N^2 ≤ (rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2).card ∧
        nodeComparisonBound hSD hproper G N M k (iterationPopularity N M) t := by
  let nodes := (Finset.range M).biUnion (nestedSlopeLevels hSD hproper)
  have hb : ∀ t ∈ nodes, ∀ᶠ N : ℕ in atTop, ∀ k < M, ∀ W : ℕ, N^2 ≤ W →
      4*(iterationPopularity N M)*((outerSlopeFamily hSD hproper t).sigma (innerSlopeFamily hSD hproper t)).card*
        (iterationMassThreshold N W M (k+1)) +
      4*((outerSlopeFamily hSD hproper t).sigma (innerSlopeFamily hSD hproper t)).card*W ≤
        (iterationPopularity N M)*(iterationMassThreshold N W M k) := by
    intro t _
    exact eventually_rounded_refinement_budget M _ hM
  have hb' := (eventually_all_finset nodes).mpr hb
  filter_upwards [hb',eventually_ge_atTop (2:ℕ)] with N hb hN
  intro G hdiff hproj
  let sl := (nestedGlobalSlopes hSD hproper M).toList
  have hp : ∀ r ∈ sl, (G.image (arithmeticProjection r)).card ≤ N := by
    intro r hr
    exact hproj r (by simpa [sl] using hr)
  rcases rational_balanced_size_cases G sl N (by omega) hp with hsmall | hlarge
  · left
    simpa [sl,Finset.length_toList] using hsmall
  rcases selected_dataset_or_small hSD hproper G N M hN hM hproj with hsmall | hselect
  · exact Or.inl hsmall
  obtain ⟨k,hk,t,ht,hu,hc⟩ := hselect
  have hs := (node_base_slopes_mem hSD hproper M k (by omega) t ht).2.1
  have hmass := hlarge.2 t.r2 (by simpa [sl] using hs)
  right
  refine ⟨k,hk,t,ht,hlarge.1,hmass,?_⟩
  apply node_final_comparison hSD hproper G N M k (iterationPopularity N M) t ht hk hN hM
    (iterationPopularity_inverse N M (by exact_mod_cast (show 1 ≤ N by omega))).1
    hβ hC hdiff hproj hmass hu hc
  exact hb t (Finset.mem_biUnion.mpr ⟨k,Finset.mem_range.mpr hk,ht⟩) k hk _ hmass

end Iteration
end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_dataset_comparison
