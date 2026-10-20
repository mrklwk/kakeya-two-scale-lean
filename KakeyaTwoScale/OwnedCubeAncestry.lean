module
public import KakeyaTwoScale.OwnedTreePaths

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- A nonempty child cannot be owned by two distinct parents in the same
actual generated level. This supplies a canonical physical parent without
making fresh local partition choices. -/
theorem owned_level_unique_parent {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C))
    (hc : ∀ A T, T ∈ children A → T.Nonempty ∧ T ⊆ A)
    (hd : ∀ A, (↑(children A) : Set (Finset C)).PairwiseDisjoint id)
    (depth : ℕ) {A B T : Finset C}
    (hA : A ∈ slopeTreeLevels {root} children depth)
    (hB : B ∈ slopeTreeLevels {root} children depth)
    (hAT : T ∈ children A) (hBT : T ∈ children B) : A = B := by
  by_contra hne
  have hdis := owned_level_disjoint root children (fun A T h => (hc A T h).2) hd depth
  obtain ⟨c,hcT⟩ := (hc A T hAT).1
  exact Finset.disjoint_left.mp (hdis hA hB hne)
    ((hc A T hAT).2 hcT) ((hc B T hBT).2 hcT)

/-- Every node in the next ordinary cellular generation has one unique
actual predecessor in the previous generation. -/
theorem owned_level_existsUnique_parent {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C))
    (hc : ∀ A T, T ∈ children A → T.Nonempty ∧ T ⊆ A)
    (hd : ∀ A, (↑(children A) : Set (Finset C)).PairwiseDisjoint id)
    (depth : ℕ) {T : Finset C}
    (hT : T ∈ slopeTreeLevels {root} children (depth+1)) :
    ∃! A, A ∈ slopeTreeLevels {root} children depth ∧ T ∈ children A := by
  obtain ⟨A,hA,hAT⟩ := Finset.mem_biUnion.mp hT
  refine ⟨A,⟨hA,hAT⟩,?_⟩
  intro B hB
  exact owned_level_unique_parent root children hc hd depth hB.1 hA hB.2 hAT

/-- Every point on an actual path belongs to the corresponding generated level. -/
theorem owned_path_mem_level {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C)) {d : ℕ}
    (nodes : Fin (d+1) → Finset C) (hzero : nodes 0 = root)
    (hedge : ∀ i : Fin d, nodes i.succ ∈ children (nodes i.castSucc)) :
    ∀ i, nodes i ∈ slopeTreeLevels {root} children i.val := by
  intro i
  induction i using Fin.induction with
  | zero => simp [slopeTreeLevels,hzero]
  | succ i ih =>
    exact slopeTree_child_mem {root} children i.val ih (hedge i)

/-- Two actual paths to the same nonempty owned mask agree pointwise. -/
theorem owned_path_unique {C : Type*} [DecidableEq C]
    (root A : Finset C) (hA : A.Nonempty)
    (children : Finset C → Finset (Finset C))
    (hsub : ∀ B T, T ∈ children B → T ⊆ B)
    (hd : ∀ B, (↑(children B) : Set (Finset C)).PairwiseDisjoint id)
    {d : ℕ} (f g : Fin (d+1) → Finset C)
    (hf0 : f 0 = root) (hfl : f (Fin.last d) = A)
    (hfe : ∀ i : Fin d, f i.succ ∈ children (f i.castSucc))
    (hg0 : g 0 = root) (hgl : g (Fin.last d) = A)
    (hge : ∀ i : Fin d, g i.succ ∈ children (g i.castSucc)) : f = g := by
  funext i
  by_contra hne
  have hf := owned_path_mem_level root children f hf0 hfe i
  have hg := owned_path_mem_level root children g hg0 hge i
  have hdis := owned_level_disjoint root children hsub hd i.val hf hg hne
  have hsf := (owned_path_root_leaf_subsets root A children hsub f hf0 hfl hfe i).1
  have hsg := (owned_path_root_leaf_subsets root A children hsub g hg0 hgl hge i).1
  obtain ⟨c,hc⟩ := hA
  exact Finset.disjoint_left.mp hdis (hsf hc) (hsg hc)

/-- A nonempty terminal mask appears at exactly one ordinary generation,
even though the stopped frontier carries it through later frontiers. -/
theorem owned_terminal_depth_unique {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C))
    (hsub : ∀ B T, T ∈ children B → T ⊆ B)
    (hd : ∀ B, (↑(children B) : Set (Finset C)).PairwiseDisjoint id)
    {A : Finset C} (hA : A.Nonempty) (hstop : children A = ∅)
    {d e : ℕ} (hAd : A ∈ slopeTreeLevels {root} children d)
    (hAe : A ∈ slopeTreeLevels {root} children e) : d = e := by
  suffices h : ∀ d e, A ∈ slopeTreeLevels {root} children d →
      A ∈ slopeTreeLevels {root} children e → ¬ d < e by
    have hde := h d e hAd hAe
    have hed := h e d hAe hAd
    omega
  intro d e hAd hAe hlt
  obtain ⟨nodes,hzero,hlast,hedge⟩ := owned_level_path root children e A hAe
  let i : Fin e := ⟨d,hlt⟩
  have hnode := owned_path_mem_level root children nodes hzero hedge i.castSucc
  have hAsub := (owned_path_root_leaf_subsets root A children hsub nodes hzero hlast hedge i.castSucc).1
  have heq : nodes i.castSucc = A := by
    by_contra hne
    have hdis := owned_level_disjoint root children hsub hd d hnode hAd hne
    obtain ⟨c,hc⟩ := hA
    exact Finset.disjoint_left.mp hdis (hAsub hc) hc
  have hnext := hedge i
  rw [heq,hstop] at hnext
  exact Finset.notMem_empty _ hnext

/-- Terminal ownership determines a unique stopping depth and, at that depth,
a unique actual path. This includes masks carried by the stopped frontier. -/
theorem owned_frontier_unique_terminal_path {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C))
    (hsub : ∀ B T, T ∈ children B → T ⊆ B)
    (hd : ∀ B, (↑(children B) : Set (Finset C)).PairwiseDisjoint id)
    (s : ℕ) {A : Finset C} (hA : A.Nonempty) (hstop : children A = ∅)
    (hAF : A ∈ ownedTerminalFrontier root children s) :
    ∃ d ≤ s,
      (∀ e, A ∈ slopeTreeLevels {root} children e → e = d) ∧
      ∃! nodes : Fin (d+1) → Finset C,
        nodes 0 = root ∧ nodes (Fin.last d) = A ∧
        ∀ i : Fin d, nodes i.succ ∈ children (nodes i.castSucc) := by
  obtain ⟨d,hds,hAd,_⟩ := owned_frontier_trace root children s A hAF
  obtain ⟨nodes,hzero,hlast,hedge⟩ := owned_level_path root children d A hAd
  refine ⟨d,hds,?_,nodes,⟨hzero,hlast,hedge⟩,?_⟩
  · intro e hAe
    exact owned_terminal_depth_unique root children hsub hd hA hstop hAe hAd
  · intro other ho
    exact owned_path_unique root A hA children hsub hd other nodes
      ho.1 ho.2.1 ho.2.2 hzero hlast hedge

end KakeyaTwoScale
#print axioms KakeyaTwoScale.owned_level_existsUnique_parent

#print axioms KakeyaTwoScale.owned_frontier_unique_terminal_path
