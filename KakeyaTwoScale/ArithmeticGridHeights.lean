module
public import KakeyaTwoScale.ProgressionLattice

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- The arithmetic inequality applied to actual rounded segment data. One
progression length works in every dimension. For each positive step cutoff,
one packing constant works at every scale and every grid translation. -/
theorem arithmetic_grid_heights :
    ∃ ell : ℕ, 2 ≤ ell ∧ ∀ n : ℕ, ∀ c : ℝ, 0 < c →
      ∃ B : ℕ, 0 < B ∧ ∀ r s h : ℝ, 0 < r → c ≤ h → h ≤ 1 →
        ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), ∀ z w : Fin n → ℝ,
        ∃ i : ℕ, i < ell ∧ (fiberCardPartition G Prod.snd (theta/a))^a ≤
          (B:ℝ)*(G.image (fun p => gridIndex r
            (segmentPoint (latticePoint r p.1+z) (latticePoint r p.2+w) (s+(i:ℝ)*h)))).card := by
  obtain ⟨ell,hell,hcount⟩ := consecutive_integer_partition_625_373
  refine ⟨ell,hell,?_⟩
  intro n c hc
  obtain ⟨B,hB,hpack⟩ := rounded_progression_projection_bound n c hc
  refine ⟨B,hB,?_⟩
  intro r s h hr hch hh1 G z w
  have hh : 0 < h := hc.trans_le hch
  obtain ⟨i,hi,hineq⟩ := hcount n (G.image (progressionLatticeMap r s h))
  rw [progressionLatticeMap_partition hr hh hh1] at hineq
  have hcard := hpack r s h hr hch G z w i
  have hcap : (((G.image (progressionLatticeMap r s h)).image (integerVectorProjection i)).card:ℝ) ≤
      (B:ℝ)*(G.image (fun p => gridIndex r
        (segmentPoint (latticePoint r p.1+z) (latticePoint r p.2+w) (s+(i:ℝ)*h)))).card := by
    exact_mod_cast hcard
  have hzero : 0 ≤ fiberCardPartition G Prod.snd (252/373) :=
    Finset.sum_nonneg (fun v _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpow := Real.rpow_le_rpow hzero hineq (show 0 ≤ a by norm_num [a])
  rw [← Real.rpow_mul (Nat.cast_nonneg _)] at hpow
  norm_num [a] at hpow
  refine ⟨i,hi,?_⟩
  norm_num only [theta,a] at ⊢
  exact hpow.trans hcap

end KakeyaTwoScale
#print axioms KakeyaTwoScale.arithmetic_grid_heights
