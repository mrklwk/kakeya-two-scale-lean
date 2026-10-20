module
public import KakeyaTwoScale.BufferedPartitionNode

@[expose] public section

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

abbrev ActualBufferedNode {b c J s : ℕ} {C : Type} [DecidableEq C]
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (D : ℕ → ℕ)
    (S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (w : C → ℝ) (η r : ℝ) (A : Finset C) :=
  OwnedPartitionNode w (2*(S.card:ℝ)) s
    (fun A => OrientedWeightedBufferedData (J:=J) (s:=s) P D S A Q w η r)
    (fun _ _ => True) BufferedCellCertificate BufferedLeafCertificate A

/-- The actual finite forest, retaining the geometric record of every node.
Its leaf geometry and weighted retention are conclusions, not constructor inputs
to the existence theorem below. -/
structure ActualBufferedCubeForest {b c J s : ℕ} {C : Type} [DecidableEq C]
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (D : ℕ → ℕ)
    (S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (root : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (w : C → ℝ) (η r : ℝ) (depth : ℕ) where
  node : ∀ A, A ⊆ root → A.Nonempty → ActualBufferedNode (J:=J) (s:=s) P D S Q w η r A
  frontier : Finset (Finset C)
  frontier_exact : frontier=ownedTerminalFrontier root (ownedPartitionChildren root node) depth
  child_decreases : ∀ A T, T ∈ ownedPartitionChildren root node A →
    T.Nonempty ∧ T ⊆ A ∧ T.card < A.card
  terminal : ∀ A ∈ frontier, A.Nonempty ∧ A ⊆ root ∧
    ownedPartitionChildren root node A=∅ ∧
    (ownedPartitionSelected root node A).Nonempty ∧ ownedPartitionSelected root node A ⊆ A ∧
    ownedCubeMass w A ≤ ((2*(S.card:ℝ))*(s+1:ℕ))*ownedCubeMass w (ownedPartitionSelected root node A)
  leaf_geometry : ∀ A ∈ frontier, ∃ (hA : A ⊆ root) (hne : A.Nonempty),
    BufferedLeafCertificate A (node A hA hne).data (ownedPartitionSelected root node A)
  frontier_disjoint : (↑frontier : Set (Finset C)).PairwiseDisjoint id
  selected_disjoint : (↑frontier : Set (Finset C)).PairwiseDisjoint (ownedPartitionSelected root node)
  selected_subset : frontier.biUnion (ownedPartitionSelected root node) ⊆ root
  retention : ownedCubeMass w root /
      ((2*(S.card:ℝ))^depth * ((2*(S.card:ℝ))*(s+1:ℕ))) ≤
    ownedCubeMass w (frontier.biUnion (ownedPartitionSelected root node))
  mass_exact : ownedCubeMass w (frontier.biUnion (ownedPartitionSelected root node)) =
    ∑ A ∈ frontier, ownedCubeMass w (ownedPartitionSelected root node A)

/-- Instantiate every local node with the proved oriented buffered partition.
No local split oracle, assumed tree, selected leaves, or physical seed is supplied.
The sole stopping condition is the displayed numerical logarithmic depth bound. -/
theorem exists_actual_buffered_cube_forest (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      ∀ {J s : ℕ} {C : Type} [DecidableEq C]
        (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ),
        (∀ i, (P i).totalDegree ≤ J) →
        (∀ x, rectangularPolynomialMap P x=0 →
          (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) →
        ∀ (D : ℕ → ℕ), (∀ j < s, 2^j < (D j+1)^b) → 2 ≤ s →
        ∀ (root : Finset C), root.Nonempty →
        ∀ (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (w : C → ℝ),
        (∀ u ∈ root, MeasurableSet (Q u)) →
        (∀ u ∈ root, volume (Q u) ≠ ⊤) →
        (∀ u ∈ root, 0 < volume.real (Q u)) →
        (∀ u ∈ root, IsPreconnected (Q u)) → (∀ u, 1 ≤ w u) →
        ∀ (tag : C → EuclideanSpace ℝ (Fin b ⊕ Fin c)),
        (∀ u ∈ root, rectangularPolynomialMap P (tag u)=0) →
        ∀ (η r : ℝ), 0 < r →
        (∀ u ∈ root, ∀ x ∈ Q u, dist x (tag u) < η) →
        ∀ depth : ℕ,
          Real.log (ownedCubeMass w root) / (-Real.log ((2:ℝ)/2^s)) < depth →
          Nonempty (ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth) := by
  classical
  obtain ⟨S,hS⟩ := exists_oriented_weighted_buffered_partition b c
  refine ⟨S,?_⟩
  intro J s C inst P hPdeg hP D hd hs root hr Q w hQ hf hp hc hw tag htag η r hradius hnear depth hdepth
  have hn : ∀ u, 0 ≤ w u := fun u => (by norm_num : (0:ℝ) ≤ 1).trans (hw u)
  have hex : ∀ A, A ⊆ root → A.Nonempty →
      Nonempty (ActualBufferedNode (J:=J) (s:=s) P D S Q w η r A) := by
    intro A hA hne
    have hmass : 0 < ∑ u ∈ A, w u := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
      (ownedCubeMass_floor w hw A hne)
    obtain ⟨d⟩ := hS P hPdeg hP D hd A Q w (fun u hu => hQ u (hA hu))
      (fun u hu => hf u (hA hu)) (fun u hu => hp u (hA hu))
      (fun u hu => hc u (hA hu)) (fun u _ => hn u) hmass tag
      (fun u hu => htag u (hA hu)) η r hradius (fun u hu => hnear u (hA hu))
    exact orientedBufferedData_node A d (fun u _ => hn u)
  let node : ∀ A, A ⊆ root → A.Nonempty → ActualBufferedNode (J:=J) (s:=s) P D S Q w η r A :=
    fun A hA hne => Classical.choice (hex A hA hne)
  have hSne : S.Nonempty := ⟨(node root (Finset.Subset.refl _) hr).data.orientation,
    (node root (Finset.Subset.refl _) hr).data.orientation_mem⟩
  have ha : 1 ≤ 2*(S.card:ℝ) := by
    have hcard : 1 ≤ S.card := Finset.one_le_card.mpr hSne
    have hc : (1:ℝ) ≤ S.card := by exact_mod_cast hcard
    linarith
  obtain ⟨F,hF,hchild,hterminal,hgeometry,hdis,hselDis,hsub,hretain,hmass⟩ :=
    exists_owned_partition_recursion hw ha hs root hr node depth hdepth
  exact ⟨{
    node := node
    frontier := F
    frontier_exact := hF
    child_decreases := hchild
    terminal := hterminal
    leaf_geometry := fun A hA => by
      obtain ⟨hsub,hne,_,hgeom⟩ := hgeometry A hA
      exact ⟨hsub,hne,hgeom⟩
    frontier_disjoint := hdis
    selected_disjoint := hselDis
    selected_subset := hsub
    retention := hretain
    mass_exact := hmass }⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_actual_buffered_cube_forest
