module
public import KakeyaTwoScale.DatasetCorners
public import KakeyaTwoScale.RoundedRefinementBudget
public import KakeyaTwoScale.RealCornerComparison

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

section Node
variable {R₀ : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R₀ β C)
  (hproper : ∀ r ∈ R₀, r ≠ -1)

/-- Entire finite dataset assembly: the selected first wing, every child
refinement, common second wing, and actual good corners are constructed.
Only the explicit numerical scale budget remains a hypothesis. -/
theorem node_final_comparison (G : Finset ArithmeticPoint) (N M k d : ℕ)
    (t : ProperSlopeTriple) (ht : t ∈ nestedSlopeLevels hSD hproper k)
    (hk : k < M) (hN : 2 ≤ N) (hM : 2 ≤ M) (hd : 0 < d)
    (hβ : 1 < β) (hC : 0 < C)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hproj : ∀ r ∈ nestedGlobalSlopes hSD hproper M, (G.image (arithmeticProjection r)).card ≤ N)
    (hlarge : N^2 ≤ (rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2).card)
    (huniform : let V := nodeBalancedDataset hSD hproper G N M t
      iterationMassThreshold N V.card M k ≤ (V.filter (fun v =>
        (V.filter (fun w => nodeDoubleProjection t w = nodeDoubleProjection t v)).card <
          iterationFiberThreshold N V.card M k)).card)
    (hchunky : ∀ u ∈ nestedSlopeLevels hSD hproper (k+1),
      ∃ Q ⊆ nodeBalancedDataset hSD hproper G N M u,
        (nodeBalancedDataset hSD hproper G N M u).card-Q.card <
          iterationMassThreshold N (nodeBalancedDataset hSD hproper G N M u).card M (k+1) ∧
        iterationFiberThreshold N (nodeBalancedDataset hSD hproper G N M u).card M (k+1)*
          (Q.image (nodeDoubleProjection u)).card ≤ 2*(nodeBalancedDataset hSD hproper G N M u).card)
    (hbudget : let S := rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2
      let F := (outerSlopeFamily hSD hproper t).sigma (innerSlopeFamily hSD hproper t)
      4*d*F.card*(iterationMassThreshold N S.card M (k+1))+4*F.card*S.card ≤
        d*(iterationMassThreshold N S.card M k)) :
    let sl := (nestedGlobalSlopes hSD hproper M).toList
    let W := (rationalBalancedPairs G sl N t.r2).card
    let J := outerSlopeFamily hSD hproper t
    let E := iterationMassThreshold N W M k
    let L := iterationFiberThreshold N W M k
    let Lnext := iterationFiberThreshold N W M (k+1)
    let l := (popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G).card/(2*N)
    let B := (W:ℝ)/(C*((8*d*J.card:ℝ)/Lnext)^β)^(-1/(β-1))
    ∃ H : ℕ, 0 < H ∧ l*E ≤ 2*H ∧
      (C*(4*(4*(J.card:ℝ)+1)*N*B/H)^β)^(-1/(β-1)) ≤ N*L := by
  dsimp only
  let sl := (nestedGlobalSlopes hSD hproper M).toList
  let S := rationalBalancedPairs G sl N t.r2
  let V := nodeBalancedDataset hSD hproper G N M t
  let J := outerSlopeFamily hSD hproper t
  let F := J.sigma (innerSlopeFamily hSD hproper t)
  let E := iterationMassThreshold N S.card M k
  let E1 := iterationMassThreshold N S.card M (k+1)
  let L := iterationFiberThreshold N S.card M k
  let L1 := iterationFiberThreshold N S.card M (k+1)
  let l := (popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G).card/(2*N)
  have hm := node_base_slopes_mem hSD hproper M k (by omega) t ht
  have hp : t.r1 ∈ sl := by simpa [sl] using hm.1
  have hs : t.r2 ∈ sl := by simpa [sl] using hm.2.1
  have heq : V.card = S.card := rationalBalancedPairs_equal_mass G sl N hp hs
    (hproj _ hm.1) (hproj _ hm.2.1)
  let U := V.filter (fun v => (V.filter (fun w => nodeDoubleProjection t w = nodeDoubleProjection t v)).card < L)
  have hUV : U ⊆ V := Finset.filter_subset _ _
  have hEU : E ≤ U.card := by simpa only [V,heq] using huniform
  have hES : E ≤ S.card := (hEU.trans (Finset.card_le_card hUV)).trans_eq heq
  have hSpos : 0 < S.card := by change N^2 ≤ S.card at hlarge; nlinarith
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlargeR : (N:ℝ)^2 ≤ S.card := by exact_mod_cast hlarge
  have hround := large_family_rounding_inputs N S.card M k hNreal hlargeR hM (by omega)
  have hround1 := large_family_rounding_inputs N S.card M (k+1) hNreal hlargeR hM (by omega)
  have hEpos : 0 < E := Nat.ceil_pos.mpr (by linarith [hround.1])
  have hLpos : 0 < L1 := Nat.ceil_pos.mpr (by linarith [hround1.2])
  have hb : 4*d*F.card*E1+4*F.card*S.card ≤ d*S.card :=
    hbudget.trans (Nat.mul_le_mul_left d hES)
  obtain ⟨Q,hQ,hloss,hhalf,hnu⟩ := node_common_nu_refinement hSD hproper G N M k d t ht
    hβ hC hd hdiff hchunky (Finset.card_pos.mp hSpos) hLpos hb
  have herror : 2*(S.card-Q.card) ≤ E := by
    have hh : d*(2*(S.card-Q.card)) ≤ d*E := by
      change d*(S.card-Q.card) ≤ 2*d*F.card*E1+2*F.card*S.card at hloss
      change 4*d*F.card*E1+4*F.card*S.card ≤ d*E at hbudget
      nlinarith
    exact Nat.le_of_mul_le_mul_left hh hd
  let K := selectedPairCorners G sl N t.r1 t.r2 U Q
  have hmass : l*E ≤ 2*K.card := selectedPairCorners_mass G sl N t.r1 t.r2 hp hs
    (hproj _ hm.1) (hproj _ hm.2.1) U Q hUV hQ E hEU herror
  have hlpos : 0 < l := by
    have hc := rationalBalancedPairs_card G sl N hs (hproj _ hm.2.1)
    change S.card = _*l at hc
    by_contra hn
    have hz : l = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz,mul_zero] at hc
    omega
  have hKpos : 0 < K.card := by nlinarith
  have hgood : goodCorners K V t.r2 t.r3 L = K := by
    apply selectedPairCorners_good
    intro v hv
    exact (Finset.mem_filter.mp hv).2.le
  let A : ℝ := (C*((8*d*J.card:ℝ)/L1)^β)^(-1/(β-1))
  have hJpos : 0 < (J.card:ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ((outerSlopeFamily_spec hSD hproper t).1.slopes_nonempty (by linarith))
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hLR : (0:ℝ) < L1 := by exact_mod_cast hLpos
  have hA : 0 < A := by dsimp [A]; positivity
  let B : ℝ := S.card/A
  have hBpos : 0 < B := div_pos (by exact_mod_cast hSpos) hA
  have hB : ∀ j ∈ J, ((Q.image (cornerNu t.r1 t.r3 j)).card:ℝ) ≤ B := by
    intro j hj
    apply (le_div_iff₀ hA).mpr
    have hn := hnu j hj
    have hc : (Q.card:ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hQ
    change A*(Q.image (cornerNu t.r1 t.r3 j)).card ≤ Q.card at hn
    nlinarith
  have hinc := selectedPairCorners_incidence G sl N t.r1 t.r2 U Q
  have hfinal := (outerSlopeFamily_spec hSD hproper t).1.final_corner_comparison_real hβ hC
    G K V Q t.r1 t.r2 t.r3 N L B (by omega) hBpos t.ne12 hdiff
    (fun j hj => (outerSlopeFamily_distinct hSD hproper t hj).1) hinc.1
    (fun c hc => hUV ((hinc.2 c hc).1)) (fun c hc => (hinc.2 c hc).2)
    (fun j hj => hproj j ((nodeFamilies_subset_global hSD hproper M k (by omega) t ht).1 hj))
    (hproj _ hm.2.2) hB (by rw [hgood]; exact Finset.card_pos.mp hKpos)
  rw [hgood] at hfinal
  exact ⟨K.card,hKpos,hmass,hfinal⟩

end Node
end KakeyaTwoScale
#print axioms KakeyaTwoScale.node_final_comparison
