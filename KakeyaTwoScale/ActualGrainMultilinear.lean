module
public import KakeyaTwoScale.PhysicalTupleMultilinear
public import KakeyaTwoScale.GrainOriginalMultiplicity

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Terminal CV bound for a literal frozen geometric state, summed over its
actual owned grains. Original-ID injectivity is used only within a cube.
All geometry and record families are extracted from the state itself. -/
theorem actual_grain_multilinear (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (T O : Type) [DecidableEq T]
      (S : FrozenGeometryState (n+1) k T (Fin (n+1)→ℤ) O)
      (Y₀ : Finset T) (cube : T→Fin (n+1)→ℤ) (tube : T→Fin k→O)
      (cubes : Finset (Fin (n+1)→ℤ)) (δ θ : ℝ), 0<δ → 0≤θ →
      S.Valid Y₀ cube tube (fun q => WithLp.ofLp ⁻¹' gridCell δ q) δ →
      (∀y∈Y₀, ∀y'∈Y₀, cube y=cube y' → tube y=tube y' → y=y') →
      (∀y∈S.tuples, θ≤tupleWedgeVolume (fun j => S.axis j (S.parent y j))) →
      θ^(1/((k-1:ℕ):ℝ))*tupleCubeMass S.tuples cube cubes (1/((k-1:ℕ):ℝ)) ≤
        C*∑g∈S.grains cube,
          (∏j, ((S.grainRecords cube g j).card:ℝ))^(1/((k-1:ℕ):ℝ)) := by
  classical
  obtain ⟨C,hC,hmain⟩ := physical_tuple_multilinear n k hk hkn
  refine ⟨C,hC,?_⟩
  intro T O _ S Y₀ cube tube cubes δ θ hδ hθ hv hinj hw
  have hk1 : 0<k-1 := by omega
  have hp : 0<1/((k-1:ℕ):ℝ) := by positivity
  have hsplit := grain_subset_mass S.tuples cube cubes S.grain (S.grains cube) hp
  have hfilter : S.tuples.filter (fun y => S.grain (cube y)∈S.grains cube)=S.tuples := by
    apply Finset.filter_eq_self.mpr
    intro y hy
    exact Finset.mem_image.mpr ⟨y,hy,rfl⟩
  rw [hfilter] at hsplit
  rw [hsplit,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  apply hmain T S.Piece (S.tuples.filter (fun y => S.grain (cube y)=g)) cube cubes
    S.parent S.base S.axis (fun j _ => S.length δ j) δ θ hδ hθ hv.2.1
  · intro y hy y' hy' he hp
    apply hinj y (hv.1 (Finset.mem_filter.mp hy).1) y' (hv.1 (Finset.mem_filter.mp hy').1) he
    funext j
    rw [←hv.2.2.1 y (Finset.mem_filter.mp hy).1 j,
      ←hv.2.2.1 y' (Finset.mem_filter.mp hy').1 j,hp]
  · intro y hy
    exact hw y (Finset.mem_filter.mp hy).1
  · intro y hy j
    exact hv.2.2.2.2.1 y (Finset.mem_filter.mp hy).1 j

/-- Extracting a common grainwise upper budget from that actual-state bound.
The budgets remain explicit finite upper counts, not a new analytic premise. -/
theorem actual_grain_multilinear_of_upper (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (T O : Type) [DecidableEq T]
      (S : FrozenGeometryState (n+1) k T (Fin (n+1)→ℤ) O)
      (Y₀ : Finset T) (cube : T→Fin (n+1)→ℤ) (tube : T→Fin k→O)
      (cubes : Finset (Fin (n+1)→ℤ)) (δ θ : ℝ) (M : Fin k→ℝ),
      0<δ → 0≤θ → (∀j, 0≤M j) →
      S.Valid Y₀ cube tube (fun q => WithLp.ofLp ⁻¹' gridCell δ q) δ →
      (∀y∈Y₀, ∀y'∈Y₀, cube y=cube y' → tube y=tube y' → y=y') →
      (∀y∈S.tuples, θ≤tupleWedgeVolume (fun j => S.axis j (S.parent y j))) →
      (∀g∈S.grains cube, ∀j, ((S.grainRecords cube g j).card:ℝ)≤M j) →
      θ^(1/((k-1:ℕ):ℝ))*tupleCubeMass S.tuples cube cubes (1/((k-1:ℕ):ℝ)) ≤
        C*(S.grains cube).card*(∏j, M j)^(1/((k-1:ℕ):ℝ)) := by
  classical
  obtain ⟨C,hC,hmain⟩ := actual_grain_multilinear n k hk hkn
  refine ⟨C,hC,?_⟩
  intro T O _ S Y₀ cube tube cubes δ θ M hδ hθ hM hv hinj hw hup
  apply (hmain T O S Y₀ cube tube cubes δ θ hδ hθ hv hinj hw).trans
  have hh : (∑g∈S.grains cube, (∏j, ((S.grainRecords cube g j).card:ℝ))^(1/((k-1:ℕ):ℝ))) ≤
      (S.grains cube).card*(∏j, M j)^(1/((k-1:ℕ):ℝ)) := by
    calc
      _ ≤ ∑_g∈S.grains cube, (∏j, M j)^(1/((k-1:ℕ):ℝ)) := by
        apply Finset.sum_le_sum
        intro g hg
        exact Real.rpow_le_rpow (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
          (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hup g hg j)) (by positivity)
      _ = _ := by simp
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hC

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_grain_multilinear
#print axioms KakeyaTwoScale.actual_grain_multilinear_of_upper
