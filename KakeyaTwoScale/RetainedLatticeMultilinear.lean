module
public import KakeyaTwoScale.WeightedCubeMultilinear

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Retained tuples need not saturate the Cartesian product. Literal incidence
and a wedge lower bound suffice to compare their count with the CV cube mass. -/
theorem retained_lattice_tuple_bound {n k : ℕ} (L : Fin k → ℕ)
    (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
    (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
    (z : Fin (n+1) → ℤ) (R : Finset ((j : Fin k) → Fin (L j))) (θ : ℝ)
    (hθ : ∀f∈R, θ≤tupleWedgeVolume (fun j => u j (f j)))
    (hinc : ∀f∈R, ∀j,
      (visibilityCube (fun i => (z i:ℝ)) ∩ infiniteLineTube (b j (f j))
        (WithLp.ofLp (u j (f j))) 1).Nonempty) :
    θ*R.card≤cubeMultilinearMass L b u (fun _ _ => 1) z := by
  calc
    θ*R.card = ∑_f∈R, θ := by simp [mul_comm]
    _ ≤ ∑f∈R, tupleWedgeVolume (fun j => u j (f j))*
        ∏j, cubeTubeWeight L b u (fun _ _ => 1) z j (f j) := by
      apply Finset.sum_le_sum
      intro f hf
      simpa only [cubeTubeWeight,ite_eq_left (hinc f hf _),Finset.prod_const_one,mul_one]
        using hθ f hf
    _ ≤ cubeMultilinearMass L b u (fun _ _ => 1) z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      intro f _ _
      exact mul_nonneg (tupleWedgeVolume_nonneg _)
        (Finset.prod_nonneg (fun j _ => cubeTubeWeight_nonneg L b u _ (by intros; norm_num) z j (f j)))

/-- The missing retained-relation form of the lattice CV input. Its constants
are independent of the finite cube bank, tuple relations and all family sizes.
No marginal retention, density, or Cartesian saturation premise is present. -/
theorem retained_lattice_multilinear (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (J : ℕ) (z : Fin J → Fin (n+1) → ℤ),
      Function.Injective z → ∀ (L : Fin k → ℕ)
      (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
      (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
      (R : Fin J → Finset ((j : Fin k) → Fin (L j))) (θ : ℝ),
      (∀j t, ‖u j t‖=1) → 0≤θ →
      (∀q, ∀f∈R q, θ≤tupleWedgeVolume (fun j => u j (f j))) →
      (∀q, ∀f∈R q, ∀j,
        (visibilityCube (fun i => (z q i:ℝ)) ∩ infiniteLineTube (b j (f j))
          (WithLp.ofLp (u j (f j))) 1).Nonempty) →
      θ^(1/((k-1:ℕ):ℝ))*(∑q, ((R q).card:ℝ)^(1/((k-1:ℕ):ℝ))) ≤
        C*(∏j, (L j:ℝ))^(1/((k-1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hmain⟩ := weighted_cube_multilinear n k hk hkn
  refine ⟨C,hC,?_⟩
  intro J z hz L b u R θ hu hθ hw hi
  have hh := hmain J z hz L b u (fun _ _ => 1) hu (by intros; norm_num)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
  apply le_trans _ hh
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  rw [←Real.mul_rpow hθ (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow (mul_nonneg hθ (Nat.cast_nonneg _))
    (retained_lattice_tuple_bound L b u (z q) (R q) θ (hw q) (hi q)) (by positivity)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.retained_lattice_tuple_bound
#print axioms KakeyaTwoScale.retained_lattice_multilinear
