module
public import KakeyaTwoScale.CompactAlgebraicComponentBound

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

def closedFreeBox {X : Type*} {d : ℕ} (g : Fin d→X→ℝ)
    (J : Finset (Fin d)) (lo hi : Fin d→ℝ) : Set X :=
  {x | ∀ j, j∉J → lo j≤g j x ∧ g j x≤hi j}

def openFreeBox {X : Type*} {d : ℕ} (g : Fin d→X→ℝ)
    (J : Finset (Fin d)) (lo hi : Fin d→ℝ) : Set X :=
  {x | ∀ j, j∉J → lo j<g j x ∧ g j x<hi j}

theorem closedFreeBox_isClosed {X : Type*} [TopologicalSpace X] {d : ℕ}
    (g : Fin d→X→ℝ) (hg : ∀ j, Continuous (g j))
    (J : Finset (Fin d)) (lo hi : Fin d→ℝ) : IsClosed (closedFreeBox g J lo hi) := by
  have he : closedFreeBox g J lo hi =
      ⋂ j : {j : Fin d // j∉J}, {x | lo j≤g j x ∧ g j x≤hi j} := by
    ext x
    simp [closedFreeBox]
  rw [he]
  exact isClosed_iInter (fun j => (isClosed_le continuous_const (hg j)).inter
    (isClosed_le (hg j) continuous_const))

theorem openFreeBox_isOpen {X : Type*} [TopologicalSpace X] {d : ℕ}
    (g : Fin d→X→ℝ) (hg : ∀ j, Continuous (g j))
    (J : Finset (Fin d)) (lo hi : Fin d→ℝ) : IsOpen (openFreeBox g J lo hi) := by
  have he : openFreeBox g J lo hi =
      ⋂ j : {j : Fin d // j∉J}, {x | lo j<g j x ∧ g j x<hi j} := by
    ext x
    simp [openFreeBox]
  rw [he]
  exact isOpen_iInter_of_finite (fun j => (isOpen_lt continuous_const (hg j)).inter
    (isOpen_lt (hg j) continuous_const))

/-- A component cannot cross a missing coordinate-box boundary. K is the
actual clipped slice in applications. The argument uses preconnectedness,
without any path-connectivity or smooth-boundary assumption. -/
theorem component_trapped_in_openFreeBox {X : Type*} [TopologicalSpace X] {d : ℕ}
    (g : Fin d→X→ℝ) (hg : ∀ j, Continuous (g j))
    (J : Finset (Fin d)) (lo hi : Fin d→ℝ) (K : Set X)
    (hboundary : K ∩ closedFreeBox g J lo hi ⊆ openFreeBox g J lo hi)
    (x : X) (hx : x∈K) (hxb : x∈closedFreeBox g J lo hi) :
    connectedComponentIn K x ⊆ openFreeBox g J lo hi := by
  let U := openFreeBox g J lo hi
  let V := (closedFreeBox g J lo hi)ᶜ
  have hUV : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro y hy hyV
    apply hyV
    intro j hj
    exact ⟨(hy j hj).1.le,(hy j hj).2.le⟩
  have hcover : connectedComponentIn K x ⊆ U∪V := by
    intro y hy
    by_cases hb : y∈closedFreeBox g J lo hi
    · exact Or.inl (hboundary ⟨connectedComponentIn_subset K x hy,hb⟩)
    · exact Or.inr hb
  exact IsPreconnected.subset_left_of_subset_union
    (openFreeBox_isOpen g hg J lo hi) (closedFreeBox_isClosed g hg J lo hi).isOpen_compl
    hUV hcover ⟨x,mem_connectedComponentIn hx,hboundary ⟨hx,hxb⟩⟩
    isPreconnected_connectedComponentIn

/-- Distinct cells with disjoint free-coordinate interiors cannot trap the
same actual component. -/
theorem trapped_components_ne {X : Type*} [TopologicalSpace X]
    (K U V : Set X) (x y : X) (hx : x∈K)
    (hU : connectedComponentIn K x⊆U) (hV : connectedComponentIn K y⊆V)
    (hUV : Disjoint U V) : connectedComponentIn K x≠connectedComponentIn K y := by
  intro he
  have hxC := mem_connectedComponentIn hx
  exact Set.disjoint_left.mp hUV (hU hxC) (hV (he ▸ hxC))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.closedFreeBox_isClosed
#print axioms KakeyaTwoScale.openFreeBox_isOpen
#print axioms KakeyaTwoScale.component_trapped_in_openFreeBox
#print axioms KakeyaTwoScale.trapped_components_ne
