module
public import KakeyaTwoScale.ActualBufferedRoutes
public import KakeyaTwoScale.BufferedTupleForest
public import KakeyaTwoScale.SelectedAncestorSurvival

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Actual ordinary-depth leaf masses inherit the genuine local cellular
contraction. Stopped-frontier persistence does not add fictitious contractions. -/
theorem actual_buffered_common_depth_mass_cap {b c J s depth : ℕ} {C : Type}
    [DecidableEq C]
    {P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ} {D : ℕ → ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))}
    {root : Finset C} {Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))}
    {w : C → ℝ} {η r : ℝ}
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (selection : ActualBufferedCommonDepth forest) :
    ∀ A ∈ selection.leaves, ownedCubeMass w A ≤
      ((2:ℝ)/2^s)^selection.d * ownedCubeMass w root := by
  have hc (A T) (hT : T ∈ ownedPartitionChildren root forest.node A) :
      ownedCubeMass w T ≤ ((2:ℝ)/2^s)*ownedCubeMass w A := by
    dsimp [ownedPartitionChildren] at hT
    split_ifs at hT with hA
    · rcases (forest.node A hA.1 hA.2).split with hl | hcell
      · rw [hl.1] at hT
        exact (Finset.notMem_empty _ hT).elim
      · exact (hcell.2.1 T hT).2.2
    · exact (Finset.notMem_empty _ hT).elim
  intro A hA
  exact owned_level_mass_le w root (ownedPartitionChildren root forest.node)
    (by positivity) hc selection.d A (selection.leaf_level A hA)

/-- Each represented final grain inherits the original full-cube mass cap
of its actual common-depth leaf. Tuple filtering and normalization cannot
increase it; no per-grain cap is supplied as an input. -/
theorem actual_buffered_seed_grain_mass_cap {b c J s depth : ℕ} {T C G : Type}
    [DecidableEq T] [DecidableEq C]
    {P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ} {D : ℕ → ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))}
    (Y Z : Finset T) (cube : T → C) (root : Finset C)
    {Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))} {alpha η r : ℝ}
    (hp : 0 < alpha) (hZY : Z ⊆ Y)
    (hactive : ∀ q ∈ root, 1 ≤ ParentLevel.capacity Y cube q)
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q
      (bufferedTupleWeight Y cube alpha) η r depth)
    (selection : ActualBufferedCommonDepth forest)
    (grain : C → G) (lift : G → Finset C)
    (hleaf : ∀ y ∈ Z, lift (grain (cube y)) ∈ selection.leaves)
    (hcube : ∀ y ∈ Z, cube y ∈ lift (grain (cube y))) :
    ∀ g ∈ Z.image (grain ∘ cube),
      tupleCubeMass (Z.filter fun y => grain (cube y)=g) cube root alpha ≤
        ((2:ℝ)/2^s)^selection.d * tupleCubeMass Y cube root alpha := by
  classical
  have heq q (hq : q ∈ root) : bufferedTupleWeight Y cube alpha q =
      (ParentLevel.capacity Y cube q:ℝ)^alpha :=
    max_eq_right (Real.one_le_rpow (by exact_mod_cast hactive q hq) hp.le)
  have htotal : ownedCubeMass (bufferedTupleWeight Y cube alpha) root=
      tupleCubeMass Y cube root alpha := Finset.sum_congr rfl (fun q hq => heq q hq)
  intro g hg
  obtain ⟨y,hy,hyg⟩ := Finset.mem_image.mp hg
  change grain (cube y)=g at hyg
  have hl : lift g ∈ selection.leaves := by
    simpa only [Function.comp_apply,hyg] using hleaf y hy
  have hsub : lift g ⊆ root := (forest.terminal _ (selection.leaves_subset hl)).2.1
  have hfilter : (Z.filter fun y => grain (cube y)=g) ⊆ Y.filter (fun y => cube y ∈ lift g) := by
    intro z hz
    obtain ⟨hz,hzg⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hZY hz,by simpa only [hzg] using hcube z hz⟩
  have hm : tupleCubeMass (Y.filter fun y => cube y ∈ lift g) cube root alpha =
      ownedCubeMass (bufferedTupleWeight Y cube alpha) (lift g) := by
    rw [whole_cube_selection_mass Y cube root (lift g) hsub hp]
    exact Finset.sum_congr rfl (fun q hq => (heq q (hsub hq)).symm)
  calc
    _ ≤ tupleCubeMass (Y.filter fun y => cube y ∈ lift g) cube root alpha :=
      tuple_mass_mono _ _ cube root hfilter hp.le
    _ = ownedCubeMass (bufferedTupleWeight Y cube alpha) (lift g) := hm
    _ ≤ ((2:ℝ)/2^s)^selection.d * ownedCubeMass (bufferedTupleWeight Y cube alpha) root :=
      actual_buffered_common_depth_mass_cap forest selection (lift g) hl
    _ = _ := by rw [htotal]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_buffered_common_depth_mass_cap
#print axioms KakeyaTwoScale.actual_buffered_seed_grain_mass_cap
