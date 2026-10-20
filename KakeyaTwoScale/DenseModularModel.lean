module
public import KakeyaTwoScale.CollisionPruning
public import KakeyaTwoScale.ModularProjectionBound

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

theorem integerFiberXs_card (G : Finset (ℤ × ℤ)) (y : ℤ) :
    (integerFiberXs G y).card = (G.filter (fun v => v.2 = y)).card := by
  apply Finset.card_image_iff.mpr
  intro v hv w hw he
  exact Prod.ext he ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)

theorem integer_fiber_le_projection (G : Finset (ℤ × ℤ)) (y : ℤ) (r : ℚ) :
    (integerFiberXs G y).card ≤ (G.image (integerProjection r)).card := by
  rw [integerFiberXs_card]
  have hi : Set.InjOn (integerProjection r) (↑(G.filter (fun v => v.2 = y)) : Set (ℤ × ℤ)) := by
    intro v hv w hw he
    have hs := (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
    apply Prod.ext ?_ hs
    simp only [integerProjection,hs,add_left_inj] at he
    exact_mod_cast he
  rw [← Finset.card_image_iff.mpr hi]
  exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/-- The retained set and the modular map are constructed by averaging the
proved collision probabilities. Projection loss is independent of p and G.
This is the dense-pair and projection part of PZ's cyclic modeling step. -/
theorem exists_dense_modular_model (p N : ℕ) [Fact p.Prime] (hpN : 20*N ≤ p)
    (G : Finset (ℤ × ℤ)) (hV : (G.image Prod.snd).card ≤ N)
    (hF : ∀ v ∈ G, (integerFiberXs G v.2).card ≤ N) :
    ∃ S : Finset (ℤ × ℤ), ∃ H : Finset (ZMod p × ZMod p),
      S ⊆ G ∧ H.card = S.card ∧ (H.image Prod.snd).card = (S.image Prod.snd).card ∧
      (4/5:ℝ)*G.card ≤ (H.card:ℝ) ∧
      ∀ a b : ℤ, (b:ZMod p) ≠ 0 →
        (H.image (modularRationalProjection p a b)).card ≤
          (G.image (integerProjection ((a:ℚ)/(b:ℚ)))).card * (2*(|b|+|a|+1)+1).toNat := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨θ,hθ⟩ := exists_dense_circle_pruning p N hp hpN G hV hF
  let S := G.filter (fun v => θ ∈ goodCircleParameters p G v)
  let t := (p:ℝ)*circleRepresentative θ
  have hf : (fun v : ℤ × ℤ => (circleBin p (v.1 • θ),circleBin p (v.2 • θ))) = modularPair p t := by
    funext v
    simp only [circleBin_zsmul_eq_modularRound,modularPair,t]
  have hi : Set.InjOn (modularPair p t) (↑S : Set (ℤ × ℤ)) := by
    rw [← hf]
    exact circle_pruning_injective p G θ
  refine ⟨S,S.image (modularPair p t),Finset.filter_subset _ _,Finset.card_image_iff.mpr hi,?_,?_,?_⟩
  · rw [Finset.image_image]
    apply image_card_of_same_fibers
    intro v hv w hw
    rw [← hf]
    exact circle_pruning_vertical_eq p G θ v w hv (Finset.mem_filter.mp hw).1
  · rw [Finset.card_image_iff.mpr hi]
    exact hθ
  · intro a b hb
    have h := modular_rational_projection_card_bound p t a b hb S
    apply h.trans
    apply Nat.mul_le_mul_right
    exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.integerFiberXs_card
#print axioms KakeyaTwoScale.integer_fiber_le_projection
#print axioms KakeyaTwoScale.exists_dense_modular_model
