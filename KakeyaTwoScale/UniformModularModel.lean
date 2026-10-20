module
public import KakeyaTwoScale.DenseModularModel

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem uniform_integer_fiber_product (G : Finset (ℤ × ℤ)) (M : ℕ)
    (hM : ∀ y ∈ G.image Prod.snd, (G.filter (fun v => v.2 = y)).card = M) :
    G.card = (G.image Prod.snd).card*M := by
  have h := Finset.card_eq_sum_card_fiberwise (s := G) (t := G.image Prod.snd) (f := Prod.snd)
    (by intro v hv; exact Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  rw [Finset.sum_congr rfl hM] at h
  simpa using h

theorem subset_card_le_uniform_fibers (S G : Finset (ℤ × ℤ)) (hSG : S ⊆ G) (M : ℕ)
    (hM : ∀ y ∈ G.image Prod.snd, (G.filter (fun v => v.2 = y)).card = M) :
    S.card ≤ (S.image Prod.snd).card*M := by
  have h := Finset.card_eq_sum_card_fiberwise (s := S) (t := S.image Prod.snd) (f := Prod.snd)
    (by intro v hv; exact Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  rw [h]
  calc
    _ ≤ ∑ _y ∈ S.image Prod.snd, M := by
      apply Finset.sum_le_sum
      intro y hy
      rw [← hM y (Finset.image_subset_image hSG hy)]
      exact Finset.card_le_card (Finset.filter_subset_filter _ hSG)
    _ = _ := by simp

/-- A complete uniform-fiber version of the cyclic modeling construction:
p ≥ 20 times the number of heights retains at least 4/5 of both points and
heights. The rational projection estimate has explicit denominator conditions
and coefficient-only loss. The empty-set case is excluded explicitly. -/
theorem exists_uniform_modular_model (p : ℕ) [Fact p.Prime]
    (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (R : Finset ℚ) (hR : R.Nonempty)
    (hp : 20*(G.image Prod.snd).card ≤ p)
    (hP : ∀ r ∈ R, (G.image (integerProjection r)).card ≤ (G.image Prod.snd).card)
    (M : ℕ) (hM : ∀ y ∈ G.image Prod.snd, (G.filter (fun v => v.2 = y)).card = M) :
    ∃ H : Finset (ZMod p × ZMod p),
      (4/5:ℝ)*G.card ≤ (H.card:ℝ) ∧
      (4/5:ℝ)*(G.image Prod.snd).card ≤ ((H.image Prod.snd).card:ℝ) ∧
      ∀ a b : ℤ, (b:ZMod p) ≠ 0 →
        (H.image (modularRationalProjection p a b)).card ≤
          (G.image (integerProjection ((a:ℚ)/(b:ℚ)))).card * (2*(|b|+|a|+1)+1).toNat := by
  obtain ⟨r,hr⟩ := hR
  have hF : ∀ v ∈ G, (integerFiberXs G v.2).card ≤ (G.image Prod.snd).card := by
    intro v _
    exact (integer_fiber_le_projection G v.2 r).trans (hP r hr)
  obtain ⟨S,H,hSG,hcard,hvert,hdense,hproj⟩ := exists_dense_modular_model p (G.image Prod.snd).card hp G le_rfl hF
  have hMpos : 0 < M := by
    obtain ⟨v,hv⟩ := hG
    rw [← hM v.2 (Finset.mem_image.mpr ⟨v,hv,rfl⟩)]
    exact Finset.card_pos.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  have hprod := uniform_integer_fiber_product G M hM
  have hsub := subset_card_le_uniform_fibers S G hSG M hM
  have hsubR : (S.card:ℝ) ≤ ((S.image Prod.snd).card:ℝ)*(M:ℝ) := by exact_mod_cast hsub
  have hprodR : (G.card:ℝ) = ((G.image Prod.snd).card:ℝ)*(M:ℝ) := by exact_mod_cast hprod
  have hMposR : (0:ℝ) < M := by exact_mod_cast hMpos
  refine ⟨H,hdense,?_,hproj⟩
  rw [hvert]
  rw [hcard,hprodR] at hdense
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_integer_fiber_product
#print axioms KakeyaTwoScale.subset_card_le_uniform_fibers
#print axioms KakeyaTwoScale.exists_uniform_modular_model
