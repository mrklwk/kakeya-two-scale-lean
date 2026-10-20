module
public import KakeyaTwoScale.CommonNuRefinement

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

theorem FiniteSDBound.slopes_nonempty {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 0 < β) : R.Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have h := hSD {(0,0)} (by simp [Set.InjOn]) 0 (le_refl _) (by simp [he])
  norm_num [Real.zero_rpow (ne_of_gt hβ)] at h

section Node
variable {R₀ : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R₀ β C)
  (hproper : ∀ r ∈ R₀, r ≠ -1)

/-- All children use exactly the same second-wing dataset, not merely sets
of equal cardinality. Their maps differ but their underlying pairs do not. -/
theorem child_dataset_eq (G : Finset ArithmeticPoint) (N M : ℕ)
    (t : ProperSlopeTriple) (j : ℚ) (hj : j ∈ outerSlopeFamily hSD hproper t)
    (r : ℚ) (hr : r ∈ innerSlopeFamily hSD hproper t j) :
    nodeBalancedDataset hSD hproper G N M (childSlopeTriple hSD hproper t j hj r hr) =
      rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2 := rfl

/-- Apply the common refinement to the actual next-level chunky subsets.
The only additional quantitative premise is the displayed numerical loss
budget; no nu-image or simultaneous-fiber bound is assumed. -/
theorem node_common_nu_refinement (G : Finset ArithmeticPoint) (N M k d : ℕ)
    (t : ProperSlopeTriple) (ht : t ∈ nestedSlopeLevels hSD hproper k)
    (hβ : 1 < β) (hC : 0 < C) (hd : 0 < d)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hchunky : ∀ u ∈ nestedSlopeLevels hSD hproper (k+1),
      ∃ Q ⊆ nodeBalancedDataset hSD hproper G N M u,
        (nodeBalancedDataset hSD hproper G N M u).card-Q.card <
          iterationMassThreshold N (nodeBalancedDataset hSD hproper G N M u).card M (k+1) ∧
        iterationFiberThreshold N (nodeBalancedDataset hSD hproper G N M u).card M (k+1)*
          (Q.image (nodeDoubleProjection u)).card ≤ 2*(nodeBalancedDataset hSD hproper G N M u).card)
    (hne : (rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2).Nonempty)
    (hL : 0 < iterationFiberThreshold N
      (rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2).card M (k+1))
    (hbudget : let S := rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2
      let F := (outerSlopeFamily hSD hproper t).sigma (innerSlopeFamily hSD hproper t)
      4*d*F.card*(iterationMassThreshold N S.card M (k+1))+4*F.card*S.card ≤ d*S.card) :
    let S := rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2
    let J := outerSlopeFamily hSD hproper t
    let F := J.sigma (innerSlopeFamily hSD hproper t)
    ∃ Q ⊆ S,
      d*(S.card-Q.card) ≤ 2*d*F.card*(iterationMassThreshold N S.card M (k+1))+2*F.card*S.card ∧
      S.card ≤ 2*Q.card ∧ ∀ j ∈ J,
        (C*((8*d*J.card:ℝ)/(iterationFiberThreshold N S.card M (k+1)))^β)^(-1/(β-1))*
          (Q.image (cornerNu t.r1 t.r3 j)).card ≤ Q.card := by
  dsimp only
  let S := rationalBalancedPairs G (nestedGlobalSlopes hSD hproper M).toList N t.r2
  let J := outerSlopeFamily hSD hproper t
  let P := innerSlopeFamily hSD hproper t
  let F := J.sigma P
  let E := iterationMassThreshold N S.card M (k+1)
  let L := iterationFiberThreshold N S.card M (k+1)
  let a := fun j => 1-cornerCoefficient t.r1 t.r3 j
  have hex : ∀ i : Σ _ : ℚ, ℚ, ∃ Q : Finset (ArithmeticPoint × ArithmeticPoint),
      i ∈ F → Q ⊆ S ∧ S.card-Q.card ≤ E ∧
        L*(Q.image (fun v => (arithmeticProjection i.2 v.1,
          arithmeticProjection (dualSlope (a i.1) t.r1 t.r2 i.2) v.2))).card ≤ 2*S.card := by
    intro i
    by_cases hi : i ∈ F
    · obtain ⟨hj,hr⟩ := Finset.mem_sigma.mp hi
      let u := childSlopeTriple hSD hproper t i.1 hj i.2 hr
      have hu := constructed_child_mem hSD hproper k t ht i.1 hj i.2 hr
      obtain ⟨Q,hQ,hE,hI⟩ := hchunky u hu
      exact ⟨Q,fun _ => ⟨hQ,Nat.le_of_lt hE,hI⟩⟩
    · exact ⟨∅,fun hi' => (hi hi').elim⟩
  choose R hR using hex
  have hS : S ⊆ G.product G := by
    intro v hv
    have h := rationalBalancedPairs_incidence G _ N t.r2 hv
    exact Finset.mem_product.mpr ⟨h.1,h.2.1⟩
  have hv : ∀ v ∈ S, arithmeticProjection t.r2 v.1 = arithmeticProjection t.r2 v.2 := by
    intro v hv
    exact (rationalBalancedPairs_incidence G _ N t.r2 hv).2.2.symm
  exact exists_common_nu_refinement G S J P a t.r1 t.r2 β C hβ hC
    (fun j hj => (innerSlopeFamily_spec hSD hproper t j hj).1) hS hv hdiff
    (fun j hj r hr => by
      have h := (innerSlopeFamily_spec hSD hproper t j hj).2 r hr
      exact ⟨h.2.2.1,h.2.2.2.2.1⟩)
    R d L E hd hL ((outerSlopeFamily_spec hSD hproper t).1.slopes_nonempty (by linarith))
    (fun i hi => (hR i hi).1) (fun i hi => (hR i hi).2.1)
    (fun i hi => (hR i hi).2.2) hbudget hne

end Node
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FiniteSDBound.slopes_nonempty
#print axioms KakeyaTwoScale.child_dataset_eq
#print axioms KakeyaTwoScale.node_common_nu_refinement
