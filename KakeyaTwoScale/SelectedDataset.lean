module
public import KakeyaTwoScale.ThresholdRegime
public import KakeyaTwoScale.NestedSlopeFamilies

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def nodeDoubleProjection (t : ProperSlopeTriple) (v : ArithmeticPoint × ArithmeticPoint) : ℚ × ℚ :=
  (arithmeticProjection t.r2 v.1,arithmeticProjection t.r3 v.2)

theorem pair_projection_image_bound (G : Finset ArithmeticPoint)
    (V : Finset (ArithmeticPoint × ArithmeticPoint)) (r s : ℚ) (N : ℕ)
    (hV : V ⊆ G.product G) (hr : (G.image (arithmeticProjection r)).card ≤ N)
    (hs : (G.image (arithmeticProjection s)).card ≤ N) :
    (V.image (fun v => (arithmeticProjection r v.1,arithmeticProjection s v.2))).card ≤ N^2 := by
  have hsub : V.image (fun v => (arithmeticProjection r v.1,arithmeticProjection s v.2)) ⊆
      (G.image (arithmeticProjection r)).product (G.image (arithmeticProjection s)) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hg := Finset.mem_product.mp (hV hw)
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨w.1,hg.1,rfl⟩,
      Finset.mem_image.mpr ⟨w.2,hg.2,rfl⟩⟩
  have hc := Finset.card_le_card hsub
  have he := Finset.card_product (G.image (arithmeticProjection r)) (G.image (arithmeticProjection s))
  exact hc.trans (he.le.trans (by simpa [pow_two] using Nat.mul_le_mul hr hs))

section Dataset
variable {R : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R β C)
  (hproper : ∀ r ∈ R, r ≠ -1)

def nodeBalancedDataset (G : Finset ArithmeticPoint) (N M : ℕ) (t : ProperSlopeTriple) :
    Finset (ArithmeticPoint × ArithmeticPoint) :=
  rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r1

theorem node_base_slopes_mem (M k : ℕ) (hk : k ≤ M) (t : ProperSlopeTriple)
    (ht : t ∈ nestedSlopeLevels hSD hproper k) :
    t.r1 ∈ nestedGlobalSlopes hSD hproper M ∧
      t.r2 ∈ nestedGlobalSlopes hSD hproper M ∧ t.r3 ∈ nestedGlobalSlopes hSD hproper M := by
  have h := nodeSlopeSet_subset_global hSD hproper M k hk t ht
  refine ⟨h ?_,h ?_,h ?_⟩ <;> simp [nodeSlopeSet,ProperSlopeTriple.forbidden]

/-- Instantiate the rounded level selection on the actual nested SD tree
and actual rational balanced pair sets. The small-set alternative is
explicit; no uniformity, chunkiness or rounding premise is supplied. -/
theorem selected_dataset_or_small (G : Finset ArithmeticPoint) (N M : ℕ)
    (hN : 2 ≤ N) (hM : 2 ≤ M)
    (hproj : ∀ r ∈ nestedGlobalSlopes hSD hproper M, (G.image (arithmeticProjection r)).card ≤ N) :
    (G.card:ℝ) ≤ 2*(2:ℝ)^(nestedGlobalSlopes hSD hproper M).card*(N:ℝ)^((3:ℝ)/2) ∨
      ∃ k < M, ∃ t ∈ nestedSlopeLevels hSD hproper k,
        iterationMassThreshold N (nodeBalancedDataset hSD hproper G N M t).card M k ≤
          ((nodeBalancedDataset hSD hproper G N M t).filter (fun v =>
            ((nodeBalancedDataset hSD hproper G N M t).filter (fun w => nodeDoubleProjection t w = nodeDoubleProjection t v)).card <
              iterationFiberThreshold N (nodeBalancedDataset hSD hproper G N M t).card M k)).card ∧
        ∀ u ∈ nestedSlopeLevels hSD hproper (k+1), ∃ Q ⊆ nodeBalancedDataset hSD hproper G N M u,
          (nodeBalancedDataset hSD hproper G N M u).card-Q.card <
            iterationMassThreshold N (nodeBalancedDataset hSD hproper G N M u).card M (k+1) ∧
          iterationFiberThreshold N (nodeBalancedDataset hSD hproper G N M u).card M (k+1) *
            (Q.image (nodeDoubleProjection u)).card ≤ 2*(nodeBalancedDataset hSD hproper G N M u).card := by
  let sl := (nestedGlobalSlopes hSD hproper M).toList
  have hp : ∀ r ∈ sl, (G.image (arithmeticProjection r)).card ≤ N := by
    intro r hr
    exact hproj r (by simpa [sl] using hr)
  rcases rational_balanced_size_cases G sl N (by omega) hp with hsmall | hlarge
  · left
    simpa [sl,Finset.length_toList] using hsmall
  · right
    apply select_rounded_projection_level (nestedSlopeLevels hSD hproper)
      (nodeBalancedDataset hSD hproper G N M) nodeDoubleProjection N M hN hM
    · exact ⟨rootSlopeTriple,by simp [nestedSlopeLevels,slopeTreeLevels]⟩
    · intro k hk t ht
      have hm := (node_base_slopes_mem hSD hproper M k hk t ht).1
      exact hlarge.2 t.r1 (by simpa [sl] using hm)
    · intro t ht
      have hm := node_base_slopes_mem hSD hproper M M (le_refl _) t ht
      apply pair_projection_image_bound G _ t.r2 t.r3 N
      · intro v hv
        have hv' := rationalBalancedPairs_incidence G sl N t.r1 hv
        exact Finset.mem_product.mpr ⟨hv'.1,hv'.2.1⟩
      · exact hproj t.r2 hm.2.1
      · exact hproj t.r3 hm.2.2

end Dataset
end KakeyaTwoScale
#print axioms KakeyaTwoScale.pair_projection_image_bound
#print axioms KakeyaTwoScale.node_base_slopes_mem
#print axioms KakeyaTwoScale.selected_dataset_or_small
