module
public import KakeyaTwoScale.EventualDatasetComparison
public import KakeyaTwoScale.QuantitativeIteration

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

section Node
variable {R₀ : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R₀ β C)
  (hproper : ∀ r ∈ R₀, r ≠ -1)

/-- The actual finite comparison yields the updated exponent with an
explicit 102/M loss. Every mass and rounding input is discharged here. -/
theorem node_exponent_update (G : Finset ArithmeticPoint) (N M k : ℕ)
    (t : ProperSlopeTriple) (ht : t ∈ nestedSlopeLevels hSD hproper k)
    (hk : k < M) (hN : 2 ≤ N) (hM : 2 ≤ M) (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C)
    (hproj : ∀ r ∈ nestedGlobalSlopes hSD hproper M, (G.image (arithmeticProjection r)).card ≤ N)
    (hcenters : 2*N ≤ (popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2
      (nestedGlobalSlopes hSD hproper M).toList G).card)
    (hlarge : N^2 ≤ (rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2).card)
    (hcomparison : nodeComparisonBound hSD hproper G N M k (iterationPopularity N M) t) :
    (G.card:ℝ) ≤ iterationBoundConstant β C (2^(nestedGlobalSlopes hSD hproper M).card)
      (outerSlopeFamily hSD hproper t).card * (N:ℝ)^(realArithmeticStep β+102/(M:ℝ)) := by
  let sl := (nestedGlobalSlopes hSD hproper M).toList
  let S := rationalBalancedPairs G sl N t.r2
  let centers := popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G
  let l := centers.card/(2*N)
  let E := iterationMassThreshold N S.card M k
  let L0 := iterationFiberThreshold N S.card M k
  let L1 := iterationFiberThreshold N S.card M (k+1)
  let d := iterationPopularity N M
  let J := outerSlopeFamily hSD hproper t
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0:ℝ) < N := by linarith
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlargeR : (N:ℝ)^2 ≤ S.card := by exact_mod_cast hlarge
  have hSr : (0:ℝ) < S.card := lt_of_lt_of_le (sq_pos_of_pos hNp) hlargeR
  have hround := large_family_rounding_inputs N S.card M k hNreal hlargeR hM (by omega)
  have hround1 := large_family_rounding_inputs N S.card M (k+1) hNreal hlargeR hM (by omega)
  have he0 := iterationMassThreshold_bounds N S.card M k hround.1
  have hL0 := iterationFiberThreshold_bounds N S.card M k hround.2
  have hL1 := iterationFiberThreshold_bounds N S.card M (k+1) hround1.2
  have hepos : (0:ℝ) < E := by change 0 < (iterationMassThreshold N S.card M k:ℝ); linarith [he0.1,hround.1]
  have hL0pos : (0:ℝ) < L0 := by change 0 < (iterationFiberThreshold N S.card M k:ℝ); linarith [hL0.1,hround.2]
  have hL1pos : (0:ℝ) < L1 := by change 0 < (iterationFiberThreshold N S.card M (k+1):ℝ); linarith [hL1.1,hround1.2]
  have hlpos : 0 < l := Nat.div_pos hcenters (by omega)
  have hlr : (0:ℝ) < l := by exact_mod_cast hlpos
  have hsub := Finset.card_le_card (popularRounds_subset (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G)
  have hgpos : 0 < G.card := by change centers.card ≤ G.card at hsub; change 2*N ≤ centers.card at hcenters; omega
  have hgr : (0:ℝ) < G.card := by exact_mod_cast hgpos
  have hp : ∀ r ∈ sl, ∀ x ∈ G, arithmeticProjection r x ∈ G.image (arithmeticProjection r) :=
    fun r _ x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hs : t.r2 ∈ sl := by
    simpa [sl] using (node_base_slopes_mem hSD hproper M k (by omega) t ht).2.1
  have hNs := hproj t.r2 (by simpa [sl] using hs)
  have hmass := (balancedVertical_mass G (fun r => G.image (arithmeticProjection r)) arithmeticProjection sl N hs hp hNs (by omega) hcenters).1
  have hmassR : (G.card:ℝ)^2 ≤ 4*((2:ℝ)^sl.length)^2*N*S.card := by
    have hmass' : G.card^2 ≤ 4*(2^sl.length)^2*N*S.card := by
      simpa only [S,rationalBalancedPairs,verticalPairSet_card] using hmass
    exact_mod_cast hmass'
  have hret := popularRounds_half (fun r => G.image (arithmeticProjection r)) arithmeticProjection sl G hp
  have hfloor := Nat.lt_mul_div_succ centers.card (by omega : 0 < 2*N)
  have hwingNat : G.card ≤ 4*2^sl.length*N*l := by
    change G.card ≤ 2^sl.length*centers.card at hret
    change centers.card < 2*N*(l+1) at hfloor
    have hh : centers.card ≤ 4*N*l := by nlinarith
    have hh' := Nat.mul_le_mul_left (2^sl.length) hh
    nlinarith
  have hwing : (G.card:ℝ) ≤ 4*(2:ℝ)^sl.length*N*l := by exact_mod_cast hwingNat
  have heps : (N:ℝ)^(-2/(M:ℝ))*S.card ≤ E := by
    have hh := Real.rpow_le_rpow_of_exponent_le hNreal (iterationLossExponent_bounds M k (by omega) (by omega)).1
    exact (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg _)).trans he0.1
  have hrho : iterationRho M (k+1) = iterationRho M k-100/(M:ℝ) := by
    simp only [iterationRho,Nat.cast_add,Nat.cast_one]
    ring
  have hnext : (S.card:ℝ)*(N:ℝ)^(iterationRho M k-100/(M:ℝ)-2) ≤ L1 := by
    simpa only [hrho] using hL1.1
  have hcurrent : (L0:ℝ) ≤ 2*(S.card:ℝ)*(N:ℝ)^(iterationRho M k-2) := by
    nlinarith only [hL0.2]
  have hpop := iterationPopularity_bounds N M hNreal
  have hdpos : (0:ℝ) < d := by exact_mod_cast (iterationPopularity_inverse N M hNreal).1
  have hJpos : (0:ℝ) < J.card := by
    exact_mod_cast Finset.card_pos.mpr ((outerSlopeFamily_spec hSD hproper t).1.slopes_nonempty (by linarith))
  obtain ⟨H,hH,hm,hcomp⟩ := hcomparison
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hmR : (l:ℝ)*E ≤ 2*H := by exact_mod_cast hm
  have hx := quantitative_iteration_bound β C ((2:ℝ)^sl.length) J.card M (iterationRho M k)
    G.card N S.card l E H L0 L1 d hβ hβ2 hMr (iterationRho_nonneg M k (by omega) (by omega))
    hC (by positivity) hJpos hgr hNreal hSr hlr hepos hHr hL0pos hL1pos hdpos
    hcomp hmR heps hnext hcurrent hpop.2 hwing hmassR
  simpa only [sl,Finset.length_toList] using hx

end Node
end KakeyaTwoScale
#print axioms KakeyaTwoScale.node_exponent_update
