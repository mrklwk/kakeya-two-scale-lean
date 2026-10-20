module
public import KakeyaTwoScale.BufferedArchiveSnapshot

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale
namespace BufferedArchiveSnapshot
variable {k : ℕ} {T C O : Type}

/-- Physical ancestry compares actual states after the uniquely determined
ambient-dimension equality. It retains whole cylinders and original IDs. -/
def PhysicalAncestor (δ : ℝ) (S U : BufferedArchiveSnapshot k T C O) : Prop :=
  ∃ h : U.dimension=S.dimension,
    let V : FrozenGeometryState S.dimension k T C O := h ▸ U.state
    V.tuples ⊆ S.state.tuples ∧
    (∀ y∈V.tuples, ∀ j, V.geometry δ j (V.parent y j) ⊆ S.state.geometry δ j (S.state.parent y j)) ∧
    (∀ y∈V.tuples, ∀ j, V.axis j (V.parent y j)=S.state.axis j (S.state.parent y j)) ∧
    (∀ y∈V.tuples, ∀ j, V.original j (V.parent y j)=S.state.original j (S.state.parent y j))

theorem PhysicalAncestor.refl (δ : ℝ) (S : BufferedArchiveSnapshot k T C O) :
    PhysicalAncestor δ S S := ⟨rfl,fun _ h=>h,fun _ _ _=>Subset.rfl,fun _ _ _=>rfl,fun _ _ _=>rfl⟩

theorem PhysicalAncestor.trans {δ : ℝ} {S U V : BufferedArchiveSnapshot k T C O}
    (hSU : PhysicalAncestor δ S U) (hUV : PhysicalAncestor δ U V) : PhysicalAncestor δ S V := by
  rcases S with ⟨n,S⟩
  rcases U with ⟨m,U⟩
  rcases V with ⟨l,V⟩
  rcases hSU with ⟨hSU,hs,hc,ha,ho⟩
  rcases hUV with ⟨hUV,hs',hc',ha',ho'⟩
  dsimp only at hSU hUV
  subst m
  subst l
  exact ⟨rfl,hs'.trans hs,fun y hy j=>(hc' y hy j).trans (hc y (hs' hy) j),
    fun y hy j=>(ha' y hy j).trans (ha y (hs' hy) j),
    fun y hy j=>(ho' y hy j).trans (ho y (hs' hy) j)⟩

theorem ofState_eq_of_HEq {n m : ℕ} (S : FrozenGeometryState n k T C O)
    (U : FrozenGeometryState m k T C O) (h : n=m) (he : HEq S U) : ofState S=ofState U := by
  subst m
  cases he
  rfl

/-- The intrinsic physical part of Valid, independent of a choice of cube
coordinate type, persists in every archived snapshot. -/
def Certified (δ : ℝ) (tube : T→Fin k→O) (S : BufferedArchiveSnapshot k T C O) : Prop :=
  S.state.tuples.Nonempty ∧
  (∀ j t, ‖S.state.axis j t‖=1) ∧
  (∀ y∈S.state.tuples, ∀ j, S.state.original j (S.state.parent y j)=tube y j) ∧
  (∀ y∈S.state.tuples, ∀ j, (S.state.geometry δ j (S.state.parent y j)).Nonempty) ∧
  (∀ j o, PairwiseDisjoint {r | r∈S.state.records j ∧ S.state.original j r=o} (S.state.geometry δ j))

theorem certified_of_valid {n : ℕ} (S : FrozenGeometryState n k T C O)
    (Y₀ : Finset T) (cube : T→C) (tube : T→Fin k→O)
    (Q : C→Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (hv : S.Valid Y₀ cube tube Q δ) (hn : S.tuples.Nonempty) : Certified δ tube (ofState S) :=
  ⟨hn,hv.2.1,hv.2.2.1,fun y hy j=>(hv.2.2.2.2.1 y hy j).mono inter_subset_right,hv.2.2.2.2.2.1⟩

end BufferedArchiveSnapshot
end KakeyaTwoScale
#print axioms KakeyaTwoScale.BufferedArchiveSnapshot.PhysicalAncestor.trans
#print axioms KakeyaTwoScale.BufferedArchiveSnapshot.certified_of_valid
