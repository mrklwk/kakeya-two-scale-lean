module
public import KakeyaTwoScale.ActualBufferedCubeForest
public import KakeyaTwoScale.OwnedCubeAncestry
public import KakeyaTwoScale.WeightedLabelSelection

@[expose] public section

open Set MeasureTheory Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

variable {b c J s : ℕ} {C : Type} [DecidableEq C]
    {P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ} {D : ℕ → ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))}
    {root : Finset C} {Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))}
    {w : C → ℝ} {η r : ℝ} {depth : ℕ}

/-- A heavy common stopping depth of the actual constructed forest. -/
structure ActualBufferedCommonDepth
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth) where
  d : ℕ
  depth_le : d ≤ depth
  leaves : Finset (Finset C)
  leaves_subset : leaves ⊆ forest.frontier
  leaf_level : ∀ A ∈ leaves,
    A ∈ slopeTreeLevels {root} (ownedPartitionChildren root forest.node) d
  cubes : Finset C
  cubes_exact : cubes = leaves.biUnion (ownedPartitionSelected root forest.node)
  cubes_nonempty : cubes.Nonempty
  retention : ownedCubeMass w root /
    (((2*(S.card:ℝ))^depth * ((2*(S.card:ℝ))*(s+1:ℕ))) * (depth+1:ℕ)) ≤ ownedCubeMass w cubes

/-- Choose the depth by summing full original cube weights of the disjoint
selected leaves. This pays only the explicit `depth+1` pigeonhole loss. -/
theorem exists_actual_buffered_common_depth
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (hw : ∀ u, 1 ≤ w u) (hr : root.Nonempty) :
    Nonempty (ActualBufferedCommonDepth forest) := by
  classical
  let children := ownedPartitionChildren root forest.node
  let selected := ownedPartitionSelected root forest.node
  have hlabel : ∀ A : Finset C, ∃ d : Fin (depth+1), A ∈ forest.frontier →
      A ∈ slopeTreeLevels {root} children d.val := by
    intro A
    by_cases hA : A ∈ forest.frontier
    · have hAF := forest.frontier_exact ▸ hA
      obtain ⟨d,hd,hAd,_⟩ := owned_frontier_trace root children depth A hAF
      exact ⟨⟨d,by omega⟩,fun _ => hAd⟩
    · exact ⟨0,fun h => (hA h).elim⟩
  choose label hlabel using hlabel
  obtain ⟨d,hheavy⟩ := exists_heaviest_weighted_label forest.frontier label
    (fun A => ownedCubeMass w (selected A))
  let F := forest.frontier.filter (fun A => label A = d)
  have hF : F ⊆ forest.frontier := Finset.filter_subset _ _
  have hdis : (↑F : Set (Finset C)).PairwiseDisjoint selected :=
    fun _ hA _ hB hAB => forest.selected_disjoint (hF hA) (hF hB) hAB
  have hmass : ownedCubeMass w (F.biUnion selected) = ∑ A ∈ F, ownedCubeMass w (selected A) :=
    Finset.sum_biUnion hdis
  have hh : ownedCubeMass w (forest.frontier.biUnion selected) ≤
      (depth+1:ℕ) * ownedCubeMass w (F.biUnion selected) := by
    rw [forest.mass_exact,hmass]
    simpa only [F,Fintype.card_fin] using hheavy
  have hret : ownedCubeMass w root /
      (((2*(S.card:ℝ))^depth * ((2*(S.card:ℝ))*(s+1:ℕ))) * (depth+1:ℕ)) ≤
      ownedCubeMass w (F.biUnion selected) := by
    rw [← div_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (depth+1:ℕ))).mpr
    exact forest.retention.trans (by simpa only [mul_comm] using hh)
  have hSne : S.Nonempty := ⟨(forest.node root (Finset.Subset.refl _) hr).data.orientation,
    (forest.node root (Finset.Subset.refl _) hr).data.orientation_mem⟩
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have hpos : 0 < ownedCubeMass w root :=
    lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (ownedCubeMass_floor w hw root hr)
  have hne : (F.biUnion selected).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hp : 0 < ownedCubeMass w root /
      (((2*(S.card:ℝ))^depth * ((2*(S.card:ℝ))*(s+1:ℕ))) * (depth+1:ℕ)) := by positivity
    simp only [he,ownedCubeMass,Finset.sum_empty] at hret
    unfold ownedCubeMass at hp
    linarith only [hp,hret]
  refine ⟨⟨d.val,by omega,F,hF,?_,F.biUnion selected,rfl,hne,hret⟩⟩
  intro A hA
  obtain ⟨hAF,he⟩ := Finset.mem_filter.mp hA
  simpa only [he] using hlabel A hAF

/-- A genuine route edge: its next mask is the literal owner fiber for the
same chosen orientation and factors stored at its parent node. -/
structure BufferedRouteStep
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (A B : Finset C) (u : C) where
  subset : A ⊆ root
  nonempty : A.Nonempty
  good : Finset C
  owner : C → Fin s → Bool
  good_subset : good ⊆ (forest.node A subset nonempty).data.selected
  children_exact : ownedPartitionChildren root forest.node A = ownedOwnerCells good owner
  next_exact : B = good.filter (fun v => owner v = owner u)
  cube_good : u ∈ good
  containment : ∀ v ∈ good, Q v ⊆
    (fun x => coordinateBaseProjection ((forest.node A subset nonempty).data.orientation x)) ⁻¹'
      polynomialSignCell (forest.node A subset nonempty).data.q (owner v)
  avoidance : ∀ v ∈ good, ∀ x ∈ Q v,
    coordinateBaseProjection ((forest.node A subset nonempty).data.orientation x) ∉
      thickening r (polynomialFactorZeros (forest.node A subset nonempty).data.q)

/-- Actual routes for all cubes of a selected common-depth family. The
subtype domain ensures every route carries a retained original cube. -/
structure ActualBufferedRoutes
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (selection : ActualBufferedCommonDepth forest) where
  leaf : {u // u ∈ selection.cubes} → Finset C
  leaf_mem : ∀ u, leaf u ∈ selection.leaves
  cube_selected : ∀ u, u.val ∈ ownedPartitionSelected root forest.node (leaf u)
  unique_leaf : ∀ u A, A ∈ selection.leaves →
    u.val ∈ ownedPartitionSelected root forest.node A → A = leaf u
  route : {u // u ∈ selection.cubes} → Fin (selection.d+1) → Finset C
  root_exact : ∀ u, route u 0 = root
  leaf_exact : ∀ u, route u (Fin.last selection.d) = leaf u
  edge : ∀ u (i : Fin selection.d),
    route u i.succ ∈ ownedPartitionChildren root forest.node (route u i.castSucc)
  cube_on_route : ∀ u i, u.val ∈ route u i
  route_subset : ∀ u i, route u i ⊆ root
  route_level : ∀ u i,
    route u i ∈ slopeTreeLevels {root} (ownedPartitionChildren root forest.node) i.val
  cellular : ∀ u (i : Fin selection.d),
    BufferedRouteStep forest (route u i.castSucc) (route u i.succ) u.val
  terminal_geometry : ∀ u, ∃ (hA : leaf u ⊆ root) (hne : (leaf u).Nonempty),
    BufferedLeafCertificate (leaf u) (forest.node (leaf u) hA hne).data
      (ownedPartitionSelected root forest.node (leaf u))
  unique_route : ∀ u (f : Fin (selection.d+1) → Finset C),
    f 0 = root → f (Fin.last selection.d) = leaf u →
    (∀ i : Fin selection.d, f i.succ ∈ ownedPartitionChildren root forest.node (f i.castSucc)) →
    f = route u

/-- Build all routes from the forest's actual generated levels and local
certificates. In particular there is no assumed routing or tube seed input. -/
theorem actual_buffered_routes
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (selection : ActualBufferedCommonDepth forest) :
    Nonempty (ActualBufferedRoutes forest selection) := by
  classical
  let children := ownedPartitionChildren root forest.node
  let selected := ownedPartitionSelected root forest.node
  have hex : ∀ u : {u // u ∈ selection.cubes},
      ∃ A ∈ selection.leaves, u.val ∈ selected A := by
    intro u
    have hu : u.val ∈ selection.leaves.biUnion selected :=
      Eq.mp (congrArg (fun F : Finset C => u.val ∈ F) selection.cubes_exact) u.property
    exact Finset.mem_biUnion.mp hu
  choose leaf hleaf hcsel using hex
  have hlf (u) : leaf u ∈ forest.frontier := selection.leaves_subset (hleaf u)
  have hsub : ∀ A T, T ∈ children A → T ⊆ A :=
    fun A T h => (forest.child_decreases A T h).2.1
  have hdis : ∀ A, (↑(children A) : Set (Finset C)).PairwiseDisjoint id := by
    intro A
    dsimp [children,ownedPartitionChildren]
    split_ifs with hA
    · rcases (forest.node A hA.1 hA.2).split with hl | hc
      · simp [hl.1]
      · exact hc.2.2.1
    · simp
  have hpath : ∀ u : {u // u ∈ selection.cubes}, ∃ f : Fin (selection.d+1) → Finset C,
      f 0 = root ∧ f (Fin.last selection.d) = leaf u ∧
      ∀ i : Fin selection.d, f i.succ ∈ children (f i.castSucc) := by
    intro u
    exact owned_level_path root children selection.d (leaf u) (selection.leaf_level _ (hleaf u))
  choose route hzero hlast hedge using hpath
  have hnest (u) := owned_path_root_leaf_subsets root (leaf u) children hsub
    (route u) (hzero u) (hlast u) (hedge u)
  have hcube (u) (i) : u.val ∈ route u i :=
    (hnest u i).1 ((forest.terminal (leaf u) (hlf u)).2.2.2.2.1 (hcsel u))
  have hcell (u) (i : Fin selection.d) :
      Nonempty (BufferedRouteStep forest (route u i.castSucc) (route u i.succ) u.val) := by
    let A := route u i.castSucc
    let B := route u i.succ
    have hA : A ⊆ root := (hnest u i.castSucc).2
    have hne : A.Nonempty := ⟨u.val,hcube u i.castSucc⟩
    have hch : (children A).Nonempty := ⟨B,hedge u i⟩
    have hcert := (ownedPartition_cellular_certificate root forest.node A hA hne hch).2
    obtain ⟨G,owner,hG,he,hcont,havoid⟩ := hcert
    have hB : B ∈ ownedOwnerCells G owner := by rw [← he]; exact hedge u i
    obtain ⟨_,label,hlabel⟩ := (mem_ownedOwnerCells G owner).mp hB
    have huB : u.val ∈ B := hcube u i.succ
    rw [hlabel] at huB
    obtain ⟨huG,huowner⟩ := Finset.mem_filter.mp huB
    exact ⟨⟨hA,hne,G,owner,hG,he,by simpa only [huowner] using hlabel,huG,hcont,havoid⟩⟩
  refine ⟨{
    leaf := leaf
    leaf_mem := hleaf
    cube_selected := hcsel
    unique_leaf := ?_
    route := route
    root_exact := hzero
    leaf_exact := hlast
    edge := hedge
    cube_on_route := hcube
    route_subset := fun u i => (hnest u i).2
    route_level := fun u i => owned_path_mem_level root children (route u) (hzero u) (hedge u) i
    cellular := fun u i => Classical.choice (hcell u i)
    terminal_geometry := fun u => forest.leaf_geometry _ (hlf u)
    unique_route := ?_ }⟩
  · intro u A hA huA
    by_contra hne
    exact Finset.disjoint_left.mp
      (forest.selected_disjoint (selection.leaves_subset hA) (hlf u) hne) huA (hcsel u)
  · intro u f hf0 hfl hfe
    exact owned_path_unique root (leaf u) (forest.terminal _ (hlf u)).1 children hsub hdis
      f (route u) hf0 hfl hfe (hzero u) (hlast u) (hedge u)

/-- Combined actual selection and routing, including the quantified common-depth loss. -/
theorem exists_actual_buffered_routes
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (hw : ∀ u, 1 ≤ w u) (hr : root.Nonempty) :
    ∃ selection : ActualBufferedCommonDepth forest, Nonempty (ActualBufferedRoutes forest selection) := by
  obtain ⟨selection⟩ := exists_actual_buffered_common_depth forest hw hr
  exact ⟨selection, actual_buffered_routes forest selection⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_actual_buffered_common_depth

#print axioms KakeyaTwoScale.actual_buffered_routes
#print axioms KakeyaTwoScale.exists_actual_buffered_routes
