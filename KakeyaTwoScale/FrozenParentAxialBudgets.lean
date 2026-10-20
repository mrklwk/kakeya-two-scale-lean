module
public import KakeyaTwoScale.FrozenPhysicalAncestry
public import KakeyaTwoScale.AxialRecordAggregation

@[expose] public section

open Set Classical
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
variable {n k : ℕ} {T C O : Type}

/-- The actual consistent parent map carries a separate deduplicated axial
budget on every represented parent fiber. -/
theorem physical_transition_parent_budgets
    (S U : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T→C)
    (tube : T→Fin k→O) (Q : C→Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (hδ : 0<δ) (hS : S.Valid Y₀ cube tube Q δ) (hU : U.Valid Y₀ cube tube Q δ)
    (hne : U.tuples.Nonempty) (hsub : U.tuples ⊆ S.tuples)
    (hcontain : ∀ y∈U.tuples, ∀ j,
      U.geometry δ j (U.parent y j) ⊆ S.geometry δ j (S.parent y j))
    (haxis : ∀ y∈U.tuples, ∀ j, U.axis j (U.parent y j)=S.axis j (S.parent y j)) :
    ∃ p : Fin k→U.Piece→S.Piece,
      (∀ y∈U.tuples, ∀ j, p j (U.parent y j)=S.parent y j) ∧
      (∀ j, ∀ t∈U.records j, p j t∈S.records j) ∧
      (∀ j, ∀ s∈S.records j,
        (∑ _t∈(U.records j).filter (fun t=>p j t=s), U.length δ j) ≤ S.length δ j) := by
  classical
  obtain ⟨y₀,hy₀⟩ := hne
  obtain ⟨parent,hparent⟩ := exists_represented_parent_map S U Y₀ cube tube Q δ hS hU hsub hcontain
  let p : ∀ j, U.Piece→S.Piece := fun j t =>
    if h : t∈U.records j then (parent j ⟨t,h⟩).val else S.parent y₀ j
  have hp (y) (hy : y∈U.tuples) (j) : p j (U.parent y j)=S.parent y j := by
    simp only [p,dite_eq_left (show U.parent y j∈U.records j from Finset.mem_image_of_mem _ hy)]
    exact hparent y hy j
  have hpmem (j) (t) (ht : t∈U.records j) : p j t∈S.records j := by
    simp only [p,dite_eq_left ht]
    exact (parent j ⟨t,ht⟩).property
  have hell (j) : 0<U.length δ j := by unfold length; positivity
  have hL (j) : 0<S.length δ j := by unfold length; positivity
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
      unfold geometry at hh
      rwa [(hdata t ht).1] at hh
    · intro t ht z hz htz
      have hh := hU.2.2.2.2.2.1 j (S.original j s)
        ⟨(Finset.mem_filter.mp ht).1,(hdata t ht).2.2⟩
        ⟨(Finset.mem_filter.mp hz).1,(hdata z hz).2.2⟩ htz
      change Disjoint (U.geometry δ j t) (U.geometry δ j z) at hh
      unfold geometry at hh
      rwa [(hdata t ht).1,(hdata z hz).1] at hh
  exact ⟨p,hp,hpmem,hbudget⟩

end FrozenGeometryState
end KakeyaTwoScale
set_option pp.fullNames true
#print axioms KakeyaTwoScale.FrozenGeometryState.physical_transition_parent_budgets
