module
public import KakeyaTwoScale.ConcreteRootState

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Every coarse root contains full original fine-cube fibers. -/
theorem coarseRootTuples_full_fiber {n k : ℕ} {O : Type} [DecidableEq O]
    (Y : Finset (RootTuple n k O)) (δ : ℝ) (a z : Fin n → ℤ)
    (hz : rootCoarseOwner δ z=a) :
    (coarseRootTuples Y δ a).filter (fun y => y.1=z) = Y.filter (fun y => y.1=z) := by
  classical
  ext y
  simp only [coarseRootTuples, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hy,rfl⟩
    exact ⟨⟨hy,hz⟩,rfl⟩

/-- Root decomposition has exact nonlinear mass additivity at every positive
exponent, with no number-of-blocks loss. -/
theorem coarseRootTuples_mass_sum {n k : ℕ} {O : Type} [DecidableEq O]
    (Y : Finset (RootTuple n k O)) (δ : ℝ) (cubes : Finset (Fin n → ℤ))
    {p : ℝ} (hp : 0<p) :
    (∑ a ∈ cubes.image (rootCoarseOwner δ),
      tupleCubeMass (coarseRootTuples Y δ a) Prod.fst cubes p) =
      tupleCubeMass Y Prod.fst cubes p :=
  cube_label_mass_eq Y Prod.fst cubes (rootCoarseOwner δ) hp

/-- Count actual participating originals in each root. An original tube is
counted only in blocks that it really visits. -/
theorem coarseRootTuples_record_sum {n k N : ℕ}
    (Y : Finset (RootTuple n k (Fin N))) {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1)
    (b u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
    (hinc : ∀ y ∈ Y, ∀ j, (rootGridCube δ y.1 ∩
      flatCylinder (b (y.2 j)) (u (y.2 j)) 1 δ).Nonempty)
    (domains : Finset (Fin n → ℤ)) (j : Fin k) :
    (∑ a ∈ domains, ((coarseRootTuples Y δ a).image (fun y => y.2 j)).card) ≤
      13^n * (Y.image (fun y => y.2 j)).card := by
  classical
  let originals := Y.image (fun y => y.2 j)
  let visits (o : Fin N) := ((Y.filter (fun y => y.2 j=o)).image Prod.fst).image (rootCoarseOwner δ)
  have hv (o : Fin N) : (visits o).card ≤ 13^n := by
    apply rootCoarseOwner_visit_bound hδ hδ1 (b o) (u o) (hu o)
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    have hy' := Finset.mem_filter.mp hy
    simpa only [hy'.2] using hinc y hy'.1 j
  have he (a) : ((coarseRootTuples Y δ a).image (fun y => y.2 j)) =
      originals.filter (fun o => a ∈ visits o) := by
    ext o
    simp only [coarseRootTuples, originals, visits, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨y,⟨hy,ha⟩,ho⟩
      exact ⟨⟨y,hy,ho⟩,y.1,⟨y,⟨hy,ho⟩,rfl⟩,ha⟩
    · rintro ⟨_,z,⟨y,⟨hy,ho⟩,rfl⟩,ha⟩
      exact ⟨y,⟨hy,ha⟩,ho⟩
  simp_rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ o ∈ originals, ∑ a ∈ domains, if a ∈ visits o then 1 else 0) ≤
        ∑ o ∈ originals, (visits o).card := by
      apply Finset.sum_le_sum
      intro o ho
      have he' : (∑ a ∈ domains, if a ∈ visits o then 1 else 0) =
          (domains.filter (fun a => a ∈ visits o)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [he']
      exact Finset.card_le_card (fun a ha => (Finset.mem_filter.mp ha).2)
    _ ≤ ∑ _o ∈ originals, 13^n := Finset.sum_le_sum (fun o _ => hv o)
    _ = _ := by simp [originals, Nat.mul_comm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coarseRootTuples_full_fiber
#print axioms KakeyaTwoScale.coarseRootTuples_mass_sum
#print axioms KakeyaTwoScale.coarseRootTuples_record_sum
