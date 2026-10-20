module
public import KakeyaTwoScale.OwnedCubeRecursion
public import Mathlib.Order.Fin.Basic

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

theorem owned_level_path {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C)) :
    ∀ d A, A ∈ slopeTreeLevels {root} children d →
      ∃ nodes : Fin (d+1) → Finset C,
        nodes 0 = root ∧ nodes (Fin.last d) = A ∧
        ∀ i : Fin d, nodes i.succ ∈ children (nodes i.castSucc) := by
  intro d
  induction d with
  | zero =>
    intro A hA
    have he : A=root := by simpa [slopeTreeLevels] using hA
    exact ⟨fun _ => root,rfl,he.symm,fun i => Fin.elim0 i⟩
  | succ d ih =>
    intro A hA
    obtain ⟨B,hB,hBA⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨nodes,hzero,hlast,hedge⟩ := ih B hB
    refine ⟨Fin.lastCases A nodes,?_,by simp,?_⟩
    · change Fin.lastCases A nodes (Fin.castSucc (0 : Fin (d+1))) = root
      simpa only [Fin.lastCases_castSucc] using hzero
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [hlast] using hBA
      · rw [← Fin.castSucc_succ]
        simpa only [Fin.lastCases_castSucc] using hedge j

theorem owned_frontier_path {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C)) (s : ℕ)
    {A : Finset C} (hA : A ∈ ownedTerminalFrontier root children s) :
    ∃ d ≤ s, ∃ nodes : Fin (d+1) → Finset C,
      nodes 0 = root ∧ nodes (Fin.last d) = A ∧
      (∀ i : Fin d, nodes i.succ ∈ children (nodes i.castSucc)) ∧
      (d=s ∨ children A=∅) := by
  obtain ⟨d,hd,hAd,hstop⟩ := owned_frontier_trace root children s A hA
  obtain ⟨nodes,hzero,hlast,hedge⟩ := owned_level_path root children d A hAd
  exact ⟨d,hd,nodes,hzero,hlast,hedge,hstop⟩

theorem owned_path_nested {C : Type*} [DecidableEq C]
    (children : Finset C → Finset (Finset C))
    (hsub : ∀ A B, B ∈ children A → B ⊆ A) {d : ℕ}
    (nodes : Fin (d+1) → Finset C)
    (hedge : ∀ i : Fin d, nodes i.succ ∈ children (nodes i.castSucc)) :
    Antitone nodes := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact hsub _ _ (hedge i)

theorem owned_path_root_leaf_subsets {C : Type*} [DecidableEq C]
    (root A : Finset C) (children : Finset C → Finset (Finset C))
    (hsub : ∀ B V, V ∈ children B → V ⊆ B) {d : ℕ}
    (nodes : Fin (d+1) → Finset C) (hzero : nodes 0=root) (hlast : nodes (Fin.last d)=A)
    (hedge : ∀ i : Fin d, nodes i.succ ∈ children (nodes i.castSucc)) :
    ∀ i, A ⊆ nodes i ∧ nodes i ⊆ root := by
  have hanti := owned_path_nested children hsub nodes hedge
  intro i
  constructor
  · rw [← hlast]
    exact hanti (Fin.le_last i)
  · rw [← hzero]
    exact hanti (Fin.zero_le i)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.owned_level_path
#print axioms KakeyaTwoScale.owned_frontier_path
#print axioms KakeyaTwoScale.owned_path_nested
#print axioms KakeyaTwoScale.owned_path_root_leaf_subsets
