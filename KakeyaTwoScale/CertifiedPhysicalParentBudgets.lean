module
public import KakeyaTwoScale.BufferedSnapshotAncestry
public import KakeyaTwoScale.EqualWidthCylinderAncestry
public import KakeyaTwoScale.AxialRecordAggregation

@[expose] public section

open Set Classical
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace BufferedArchiveSnapshot
variable {n k : ℕ} {T C O : Type}

/-- The actual consistent parent map carries a separate deduplicated axial
budget on every represented parent fiber. -/
theorem certified_physical_parent_budgets
    (S U : FrozenGeometryState n k T C O) (tube : T→Fin k→O) (δ : ℝ)
    (hδ : 0<δ) (hS : Certified δ tube (ofState S)) (hU : Certified δ tube (ofState U)) (hsub : U.tuples ⊆ S.tuples)
    (hcontain : ∀ y∈U.tuples, ∀ j,
      U.geometry δ j (U.parent y j) ⊆ S.geometry δ j (S.parent y j))
    (haxis : ∀ y∈U.tuples, ∀ j, U.axis j (U.parent y j)=S.axis j (S.parent y j)) :
    ∃ p : Fin k→U.Piece→S.Piece,
      (∀ y∈U.tuples, ∀ j, p j (U.parent y j)=S.parent y j) ∧
      (∀ j, ∀ t∈U.records j, p j t∈S.records j) ∧
      (∀ j, ∀ s∈S.records j,
        (∑ _t∈(U.records j).filter (fun t=>p j t=s), U.length δ j) ≤ S.length δ j) := by
  classical
  simp only [Certified,ofState] at hS hU
  obtain ⟨y₀,hy₀⟩ := hU.1
  have hconsistent {x y : T} (hx : x∈U.tuples) (hy : y∈U.tuples) (j : Fin k)
      (he : U.parent x j=U.parent y j) : S.parent x j=S.parent y j := by
    by_contra hne
    have ho : S.original j (S.parent x j)=S.original j (S.parent y j) := by
      rw [hS.2.2.1 x (hsub hx) j,hS.2.2.1 y (hsub hy) j]
      have hh := hU.2.2.1 x hx j
      rw [he,hU.2.2.1 y hy j] at hh
      exact hh.symm
    have hd := hS.2.2.2.2 j (S.original j (S.parent x j))
      ⟨Finset.mem_image_of_mem _ (hsub hx),rfl⟩
      ⟨Finset.mem_image_of_mem _ (hsub hy),ho.symm⟩ hne
    obtain ⟨z,hz⟩ := hU.2.2.2.1 x hx j
    exact Set.disjoint_left.mp hd (hcontain x hx j hz) (hcontain y hy j (he ▸ hz))
  have hw : ∀ j (t : {t // t∈U.records j}), ∃ y∈U.tuples, U.parent y j=t.val := by
    intro j t
    exact Finset.mem_image.mp t.property
  choose witness hmem heq using hw
  let p : ∀ j, U.Piece→S.Piece := fun j t =>
    if h:t∈U.records j then S.parent (witness j ⟨t,h⟩) j else S.parent y₀ j
  have hp (y) (hy : y∈U.tuples) (j) : p j (U.parent y j)=S.parent y j := by
    simp only [p,dite_eq_left (show U.parent y j∈U.records j from Finset.mem_image_of_mem _ hy)]
    exact hconsistent (hmem j _) hy j (heq j _)
  have hpmem (j) (t) (ht : t∈U.records j) : p j t∈S.records j := by
    simp only [p,dite_eq_left ht]
    exact Finset.mem_image_of_mem _ (hsub (hmem j ⟨t,ht⟩))
  have hell (j) : 0<U.length δ j := by unfold FrozenGeometryState.length; positivity
  have hL (j) : 0<S.length δ j := by unfold FrozenGeometryState.length; positivity
  have hbudget (j) (s) (hs : s∈S.records j) :
      (∑ _t∈(U.records j).filter (fun t=>p j t=s), U.length δ j) ≤ S.length δ j := by
    let F := (U.records j).filter (fun t=>p j t=s)
    have hdata (t) (ht : t∈F) :
        U.axis j t=S.axis j s ∧ U.geometry δ j t⊆S.geometry δ j s ∧
        U.original j t=S.original j s := by
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
      rw [hp y hy j] at he
      subst s
      exact ⟨haxis y hy j,hcontain y hy j,(hU.2.2.1 y hy j).trans (hS.2.2.1 y (hsub hy) j).symm⟩
    apply disjoint_contained_cylinders_length_sum F (S.base j s) (S.axis j s)
      (U.base j) (fun _=>U.length δ j) (S.length δ j) δ (hS.2.1 j s) (hL j) hδ
      (fun _ _=>hell j)
    · intro t ht
      have hh := (hdata t ht).2.1
      unfold FrozenGeometryState.geometry at hh
      rwa [(hdata t ht).1] at hh
    · intro t ht z hz htz
      have hh := hU.2.2.2.2 j (S.original j s)
        ⟨(Finset.mem_filter.mp ht).1,(hdata t ht).2.2⟩
        ⟨(Finset.mem_filter.mp hz).1,(hdata z hz).2.2⟩ htz
      change Disjoint (U.geometry δ j t) (U.geometry δ j z) at hh
      unfold FrozenGeometryState.geometry at hh
      rwa [(hdata t ht).1,(hdata z hz).1] at hh
  exact ⟨p,hp,hpmem,hbudget⟩

/-- Every represented descendant record has a single actual parent and the
full fiber has at most the ancestor's axial length. -/
def ParentAxialBudget (δ : ℝ) (S U : BufferedArchiveSnapshot k T C O) : Prop :=
  ∃ h : U.dimension=S.dimension,
    let V : FrozenGeometryState S.dimension k T C O := h ▸ U.state
    ∃ p : Fin k→V.Piece→S.state.Piece,
      (∀ y∈V.tuples, ∀ j, p j (V.parent y j)=S.state.parent y j) ∧
      (∀ j, ∀ r∈V.records j, p j r∈S.state.records j) ∧
      (∀ j, ∀ r∈S.state.records j,
        (∑ _u∈(V.records j).filter (fun u=>p j u=r), V.length δ j) ≤ S.state.length δ j)

theorem PhysicalAncestor.parent_axial_budget {δ : ℝ}
    {S U : BufferedArchiveSnapshot k T C O} (hδ : 0<δ)
    (tube : T→Fin k→O) (hS : Certified δ tube S) (hU : Certified δ tube U)
    (h : PhysicalAncestor δ S U) : ParentAxialBudget δ S U := by
  rcases S with ⟨n,S⟩
  rcases U with ⟨m,U⟩
  rcases h with ⟨he,hsub,hcontain,haxis,_⟩
  dsimp only at he
  subst m
  exact ⟨rfl,certified_physical_parent_budgets S U tube δ hδ hS hU hsub hcontain haxis⟩

end BufferedArchiveSnapshot
end KakeyaTwoScale
set_option pp.fullNames true
#print axioms KakeyaTwoScale.BufferedArchiveSnapshot.certified_physical_parent_budgets

#print axioms KakeyaTwoScale.BufferedArchiveSnapshot.PhysicalAncestor.parent_axial_budget
