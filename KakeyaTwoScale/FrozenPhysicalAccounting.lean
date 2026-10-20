module
public import KakeyaTwoScale.FrozenPhysicalAncestry
public import KakeyaTwoScale.AxialRecordAggregation

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
variable {n k : ℕ} {T C O : Type}

/-- Constructed physical ancestry implies exact global axial conservation and
nonincreasing dyadic height. No axial or cardinal bound is an input. -/
theorem physical_transition_accounting
    (S U : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T→C)
    (tube : T→Fin k→O) (Q : C→Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (hδ : 0<δ) (hS : S.Valid Y₀ cube tube Q δ) (hU : U.Valid Y₀ cube tube Q δ)
    (hne : U.tuples.Nonempty) (hsub : U.tuples ⊆ S.tuples)
    (hcontain : ∀ y∈U.tuples, ∀ j,
      U.geometry δ j (U.parent y j) ⊆ S.geometry δ j (S.parent y j))
    (haxis : ∀ y∈U.tuples, ∀ j, U.axis j (U.parent y j)=S.axis j (S.parent y j)) :
    (∀ j, U.height j≤S.height j) ∧
    (∀ j, U.length δ j*(U.count j:ℝ) ≤ S.length δ j*(S.count j:ℝ)) := by
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
      (∑ t∈(U.records j).filter (fun t=>p j t=s), U.length δ j) ≤ S.length δ j := by
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
  have htotal (j) : U.length δ j*(U.count j:ℝ) ≤ S.length δ j*(S.count j:ℝ) := by
    have he := Finset.sum_fiberwise_of_maps_to (hpmem j) (fun _=>U.length δ j)
    have hb := Finset.sum_le_sum (hbudget j)
    rw [he] at hb
    simpa [count,nsmul_eq_mul,mul_comm] using hb
  refine ⟨?_,htotal⟩
  intro j
  have hc := hcontain y₀ hy₀ j
  unfold geometry at hc
  rw [haxis y₀ hy₀ j] at hc
  have hl := disjoint_contained_cylinders_length_sum ({0} : Finset ℕ)
    (S.base j (S.parent y₀ j)) (S.axis j (S.parent y₀ j))
    (fun _=>U.base j (U.parent y₀ j)) (fun _=>U.length δ j)
    (S.length δ j) δ (hS.2.1 j _) (hL j) hδ (fun _ _=>hell j)
    (fun _ _=>hc) (by simp)
  simp only [Finset.sum_singleton] at hl
  have hh : (2:ℝ)^(U.height j) ≤ 2^(S.height j) := by
    exact (mul_le_mul_iff_right₀ hδ).mp hl
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hh

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.physical_transition_accounting
