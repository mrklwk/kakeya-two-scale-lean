module
public import KakeyaTwoScale.FrozenFilteredTerminal

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
attribute [local instance] Classical.propDecidable

/-- Summing the all-short selected-fiber bound charges only the FULL archive's
upper budgets. Neither lower counts nor rebuilt ancestor marginals occur. -/
theorem exists_terminal_upper_budget_bound (n : ℕ) (Cstar : ℝ) :
    ∃ cap : ℕ, 0 < cap ∧ ∀ {T O : Type} [DecidableEq T] {k : ℕ},
      ∀ (S : FrozenGeometryState n k T (Fin n → ℤ) O) (Y₀ : Finset T)
        (cube : T → Fin n → ℤ) (tube : T → Fin k → O)
        (cubes : Finset (Fin n → ℤ)) (δ : ℝ), 0 < δ →
      S.Valid Y₀ cube tube (fun q => WithLp.ofLp ⁻¹' gridCell δ q) δ →
      (∀ y ∈ Y₀, ∀ z ∈ Y₀, cube y=cube z → (∀ j, tube y j=tube z j) → y=z) →
      (∀ j, S.length δ j ≤ Cstar*δ) → 0 < k →
      ∀ (p : ℝ), 1/(k:ℝ) ≤ p → ∀ (Z : Finset T), Z ⊆ S.tuples →
      ∀ (K : Fin k → ℝ), (∀ j, 0 ≤ K j) →
      (∀ g ∈ S.grains cube, ∀ j,
        (grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g:ℝ) ≤ K j) →
      tupleCubeMass Z cube cubes p ≤ ((S.grains cube).card:ℝ)*(∏ j, (cap:ℝ)*K j)^p := by
  classical
  obtain ⟨cap,hcap,hterminal⟩ := exists_filtered_terminal_bound n Cstar
  refine ⟨cap,hcap,?_⟩
  intro T O inst k S Y₀ cube tube cubes δ hδ hv hinj hshort hk p hp Z hZS K hK hupper
  have hp0 : 0 < p := (div_pos zero_lt_one (by exact_mod_cast hk : (0:ℝ)<k)).trans_le hp
  let G := Z.image (S.grain ∘ cube)
  have hG : G ⊆ S.grains cube := Finset.image_subset_image hZS
  have hlocal (g) (hg : g ∈ G) :
      tupleCubeMass (Z.filter fun y => S.grain (cube y)=g) cube cubes p ≤
        (∏ j, (cap:ℝ)*K j)^p := by
    have ht := hterminal S Y₀ cube tube cubes δ hδ hv hinj hshort hk p hp Z hZS g
    apply ht.trans (Real.rpow_le_rpow (Finset.prod_nonneg (fun j _ => by positivity)) ?_ hp0.le)
    apply Finset.prod_le_prod₀ (fun j _ => by positivity)
    intro j _
    exact mul_le_mul_of_nonneg_left (hupper g (hG hg) j) (Nat.cast_nonneg cap)
  have hm := selected_mass_le_ancestor_mass Z Z cube cubes S.grain (Finset.Subset.refl _) hp0
  have hs := hm.trans (Finset.sum_le_sum hlocal)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hc : (G.card:ℝ) ≤ (S.grains cube).card := by exact_mod_cast Finset.card_le_card hG
  exact hs.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg
    (Finset.prod_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg cap) (hK j))) p))

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_terminal_upper_budget_bound
