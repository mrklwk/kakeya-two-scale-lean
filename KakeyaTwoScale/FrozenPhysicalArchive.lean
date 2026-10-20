module
public import KakeyaTwoScale.FrozenPhysicalAccounting

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
variable {n k : ℕ} {T C O : Type}

/-- Actual successive containments preserve every earlier physical ancestor,
with the same surviving tuple selecting the ancestor at each level. -/
theorem physical_archive_ancestry
    (S : ℕ→FrozenGeometryState n k T C O) (N : ℕ) (δ : ℝ)
    (hsub : ∀ t<N, (S (t+1)).tuples ⊆ (S t).tuples)
    (hc : ∀ t<N, ∀ y∈(S (t+1)).tuples, ∀ j,
      (S (t+1)).geometry δ j ((S (t+1)).parent y j) ⊆
        (S t).geometry δ j ((S t).parent y j))
    (ha : ∀ t<N, ∀ y∈(S (t+1)).tuples, ∀ j,
      (S (t+1)).axis j ((S (t+1)).parent y j)=(S t).axis j ((S t).parent y j)) :
    ∀ s t, s≤t → t≤N →
      (S t).tuples ⊆ (S s).tuples ∧
      (∀ y∈(S t).tuples, ∀ j, (S t).geometry δ j ((S t).parent y j) ⊆
        (S s).geometry δ j ((S s).parent y j)) ∧
      (∀ y∈(S t).tuples, ∀ j, (S t).axis j ((S t).parent y j)=
        (S s).axis j ((S s).parent y j)) := by
  intro s t hst htN
  induction t, hst using Nat.le_induction with
  | base => exact ⟨fun _ h=>h,fun _ _ _=>Set.Subset.rfl,fun _ _ _=>rfl⟩
  | succ t hst ih =>
    have ht : t<N := by omega
    have hprev := ih (by omega)
    exact ⟨fun _ hy=>hprev.1 (hsub t ht hy),
      fun y hy j=>(hc t ht y hy j).trans (hprev.2.1 y (hsub t ht hy) j),
      fun y hy j=>(ha t ht y hy j).trans (hprev.2.2 y (hsub t ht hy) j)⟩

/-- Cumulative axial and height bounds are consequences of each level's actual
geometry. No stepwise or final axial inequality is assumed. -/
theorem physical_archive_accounting
    (S : ℕ→FrozenGeometryState n k T C O) (N : ℕ)
    (Y₀ : Finset T) (cube : T→C) (tube : T→Fin k→O)
    (Q : C→Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) (hδ : 0<δ)
    (hv : ∀ t≤N, (S t).Valid Y₀ cube tube Q δ)
    (hne : ∀ t≤N, (S t).tuples.Nonempty)
    (hsub : ∀ t<N, (S (t+1)).tuples ⊆ (S t).tuples)
    (hc : ∀ t<N, ∀ y∈(S (t+1)).tuples, ∀ j,
      (S (t+1)).geometry δ j ((S (t+1)).parent y j) ⊆
        (S t).geometry δ j ((S t).parent y j))
    (ha : ∀ t<N, ∀ y∈(S (t+1)).tuples, ∀ j,
      (S (t+1)).axis j ((S (t+1)).parent y j)=(S t).axis j ((S t).parent y j)) :
    ∀ s t, s≤t → t≤N →
      (∀ j, (S t).height j≤(S s).height j) ∧
      (∀ j, (S t).length δ j*((S t).count j:ℝ) ≤
        (S s).length δ j*((S s).count j:ℝ)) := by
  intro s t hst htN
  have hh := physical_archive_ancestry S N δ hsub hc ha s t hst htN
  exact physical_transition_accounting (S s) (S t) Y₀ cube tube Q δ hδ
    (hv s (hst.trans htN)) (hv t htN) (hne t htN) hh.1 hh.2.1 hh.2.2

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.physical_archive_ancestry
#print axioms KakeyaTwoScale.FrozenGeometryState.physical_archive_accounting
