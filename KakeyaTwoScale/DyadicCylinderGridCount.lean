module
public import KakeyaTwoScale.ShortCylinderGridCount

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Overlapping short cylinders cover the entire open cylinder, including
all integer subdivision times. No endpoint ownership convention is needed. -/
theorem flatCylinder_integer_length_cover {n : ℕ}
    (b u : EuclideanSpace ℝ (Fin n)) {δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ flatCylinder b u (N*δ) δ) :
    ∃ i ∈ Finset.range N,
      x ∈ flatCylinder (b + ((i:ℝ)*δ-δ) • u) u (3*δ) δ := by
  obtain ⟨t, ht, htN, hi, hr⟩ := hx
  let i : ℕ := ⌊t/δ⌋₊
  have htd : 0 ≤ t/δ := div_nonneg ht.le hδ.le
  have hiN : i < N := (Nat.floor_lt htd).mpr ((div_lt_iff₀ hδ).mpr htN)
  have hlow : (i:ℝ)*δ ≤ t := (le_div_iff₀ hδ).mp (Nat.floor_le htd)
  have hupp : t < ((i:ℝ)+1)*δ := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (t/δ))
  have he : b + ((i:ℝ)*δ-δ) • u + (t-(i:ℝ)*δ+δ) • u = b+t • u := by module
  refine ⟨i, Finset.mem_range.mpr hiN, t-(i:ℝ)*δ+δ, by linarith, by linarith, ?_, ?_⟩
  · simpa only [he] using hi
  · simpa only [he] using hr

/-- The linear cube-incidence bound for actual dyadic-length cylinders.
The dimension-only constant is constructed before all scale and finite data. -/
theorem exists_dyadicCylinder_grid_count (n : ℕ) :
    ∃ B : ℕ, 0 < B ∧ ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ),
      ∀ (b u : EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 →
      ∀ cubes : Finset (Fin n → ℤ),
      (∀ z ∈ cubes,
        ((WithLp.ofLp ⁻¹' gridCell δ z) ∩ flatCylinder b u (N*δ) δ).Nonempty) →
      cubes.card ≤ N*B := by
  classical
  obtain ⟨B, hB, hshort⟩ := exists_shortCylinder_grid_count n 3
  refine ⟨B, hB, ?_⟩
  intro δ hδ N b u hu cubes hmeet
  let parts : ℕ → Finset (Fin n → ℤ) := fun i => cubes.filter fun z =>
    ((WithLp.ofLp ⁻¹' gridCell δ z) ∩
      flatCylinder (b + ((i:ℝ)*δ-δ) • u) u (3*δ) δ).Nonempty
  have hcover : cubes ⊆ (Finset.range N).biUnion parts := by
    intro z hz
    obtain ⟨x, hxz, hxc⟩ := hmeet z hz
    obtain ⟨i, hi, hxi⟩ := flatCylinder_integer_length_cover b u hδ N hxc
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hz, x, hxz, hxi⟩⟩
  have hpart (i : ℕ) : (parts i).card ≤ B := by
    apply hshort δ (3*δ) hδ le_rfl _ u hu
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  calc
    cubes.card ≤ ((Finset.range N).biUnion parts).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ Finset.range N, (parts i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range N, B := Finset.sum_le_sum (fun i _ => hpart i)
    _ = N*B := by simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.flatCylinder_integer_length_cover
#print axioms KakeyaTwoScale.exists_dyadicCylinder_grid_count
