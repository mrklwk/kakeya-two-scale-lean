module
public import KakeyaTwoScale.FrozenGeometryState
public import KakeyaTwoScale.EqualWidthCylinderAncestry

@[expose] public section

open Set Classical
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
variable {n k : ℕ} {T C O : Type}

/-- Physical containment and original IDs determine a unique represented
parent, even when a record occurs in many different tuples. -/
theorem parent_consistent_of_containment
    (S U : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T→C)
    (tube : T→Fin k→O) (Q : C→Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (hS : S.Valid Y₀ cube tube Q δ) (hU : U.Valid Y₀ cube tube Q δ)
    (hsub : U.tuples ⊆ S.tuples)
    (hcontain : ∀ y∈U.tuples, ∀ j,
      U.geometry δ j (U.parent y j) ⊆ S.geometry δ j (S.parent y j))
    {x y : T} (hx : x∈U.tuples) (hy : y∈U.tuples) (j : Fin k)
    (he : U.parent x j=U.parent y j) : S.parent x j=S.parent y j := by
  by_contra hne
  have horig : S.original j (S.parent x j)=S.original j (S.parent y j) := by
    rw [hS.2.2.1 x (hsub hx) j,hS.2.2.1 y (hsub hy) j]
    have hh := hU.2.2.1 x hx j
    rw [he,hU.2.2.1 y hy j] at hh
    exact hh.symm
  have hdis := hS.2.2.2.2.2.1 j (S.original j (S.parent x j))
    (show S.parent x j ∈ {t | t∈S.records j ∧ S.original j t=S.original j (S.parent x j)} from
      ⟨Finset.mem_image_of_mem _ (hsub hx),rfl⟩)
    (show S.parent y j ∈ {t | t∈S.records j ∧ S.original j t=S.original j (S.parent x j)} from
      ⟨Finset.mem_image_of_mem _ (hsub hy),horig.symm⟩) hne
  obtain ⟨z,hz⟩ := hU.2.2.2.2.1 x hx j
  exact Set.disjoint_left.mp hdis (hcontain x hx j hz.2)
    (hcontain y hy j (he ▸ hz.2))

/-- An actual map on deduplicated records, agreeing with every surviving tuple. -/
theorem exists_represented_parent_map
    (S U : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T→C)
    (tube : T→Fin k→O) (Q : C→Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (hS : S.Valid Y₀ cube tube Q δ) (hU : U.Valid Y₀ cube tube Q δ)
    (hsub : U.tuples ⊆ S.tuples)
    (hcontain : ∀ y∈U.tuples, ∀ j,
      U.geometry δ j (U.parent y j) ⊆ S.geometry δ j (S.parent y j)) :
    ∃ parent : ∀ j, {t // t∈U.records j} → {t // t∈S.records j},
      ∀ y (hy : y∈U.tuples) j,
        (parent j ⟨U.parent y j,Finset.mem_image_of_mem _ hy⟩).val=S.parent y j := by
  classical
  have hw : ∀ j (t : {t // t∈U.records j}), ∃ y∈U.tuples, U.parent y j=t.val := by
    intro j t
    exact Finset.mem_image.mp t.property
  choose witness hmem heq using hw
  refine ⟨fun j t => ⟨S.parent (witness j t) j,Finset.mem_image_of_mem _ (hsub (hmem j t))⟩,?_⟩
  intro y hy j
  exact parent_consistent_of_containment S U Y₀ cube tube Q δ hS hU hsub hcontain
    (hmem j _) hy j (heq j _)

end FrozenGeometryState
end KakeyaTwoScale
set_option pp.fullNames true
#print axioms KakeyaTwoScale.FrozenGeometryState.parent_consistent_of_containment
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_represented_parent_map
