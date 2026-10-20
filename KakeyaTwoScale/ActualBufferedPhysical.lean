module
public import KakeyaTwoScale.ActualBufferedRoutes
public import KakeyaTwoScale.OrientedCylindricalWall
public import KakeyaTwoScale.PolynomialSuccessorSystem

@[expose] public section

open Set Metric MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The original whole set in the physical Fin-index coordinate system. -/
def physicalCoordinateCube {b c : ℕ} (Q : Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) :
    Set (EuclideanSpace ℝ (Fin (b+c))) := euclideanCoordinateRename finSumFinEquiv '' Q

variable {b c J s : ℕ} {C : Type} [DecidableEq C]
    {P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ} {D : ℕ → ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))}
    {root : Finset C} {Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))}
    {w : C → ℝ} {η r : ℝ} {depth : ℕ}

/-- One actual node supplies physical sign owners, merged child masks and
its exact algebraic successor, with no independently supplied geometry. -/
theorem actual_buffered_node_physical
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (hP : ∀ i, (P i).totalDegree ≤ J) (δ : ℝ) (hr : 0 < r) (hgap : 2*δ < r)
    (A : Finset C) (hA : A ⊆ root) (hne : A.Nonempty) :
    ∃ (p : Fin s → MvPolynomial (Fin (b+c)) ℝ) (owner : C → Fin s → Bool)
      (merge : (Fin s → Bool) → Finset C) (f : Fin (c+1) → MvPolynomial (Fin (b+c)) ℝ),
      (∏ i, p i).totalDegree ≤ b*(∑ j ∈ Finset.range s, D j) ∧
      (∀ i, (f i).totalDegree ≤ max J (max (2*c*(J-1)) (b*(∑ j ∈ Finset.range s, D j)))) ∧
      (∀ B ∈ ownedPartitionChildren root forest.node A, ∀ u ∈ B,
        merge (owner u)=B ∧ physicalCoordinateCube (Q u) ⊆ polynomialSignCell p (owner u) ∧
        ∀ x ∈ physicalCoordinateCube (Q u), x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ i, p i))) ∧
      (∀ u ∈ ownedPartitionSelected root forest.node A,
        physicalCoordinateCube (Q u) ⊆ thickening (η+2*(η+r)) {x | rectangularPolynomialMap f x=0}) ∧
      ((ownedPartitionSelected root forest.node A).Nonempty → ∀ x, rectangularPolynomialMap f x=0 →
        (fderiv ℝ (rectangularPolynomialMap f) x).range=⊤) ∧
      ((ownedPartitionSelected root forest.node A).Nonempty → ∀ i,
        f i.succ=rename finSumFinEquiv (P i)) := by
  let node := forest.node A hA hne
  rw [ownedPartitionChildren_node root forest.node A hA hne,
    ownedPartitionSelected_node root forest.node A hA hne]
  change ∃ p owner merge f, _ ∧ _ ∧ (∀ B ∈ node.children, _) ∧ (∀ u ∈ node.selected, _) ∧ (node.selected.Nonempty → _) ∧ (node.selected.Nonempty → _)
  rcases node.split with hl | hc
  · obtain ⟨he,hsub,hm,i,hcapture⟩ := hl
    refine ⟨fun _ => 1,fun _ _ => false,fun _ => ∅,
      finitePolynomialSuccessor P (node.data.wall i),?_,?_,?_,?_,?_,?_⟩
    · simp
    · exact finitePolynomialSuccessor_degree P (node.data.wall i) hP (node.data.wall_degree i)
    · simp [he]
    · intro u hu x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact (finitePolynomialSuccessor_thickening P (node.data.wall i) y _).mpr (hcapture u hu hy)
    · intro _
      exact finitePolynomialSuccessor_regular P (node.data.wall i) (node.data.wall_regular i)
    · intro _ i; rfl
  · obtain ⟨he,_,_,_,G,owner,hG,hchildren,hcell,havoid⟩ := hc
    let p := fun i => orientedFiniteFactor node.data.orientation (node.data.q i)
    refine ⟨p,owner,fun sign => G.filter (fun u => owner u=sign),fun _ => 0,?_,?_,?_,?_,?_,?_⟩
    · exact (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum (fun i _ =>
        orientedFiniteFactor_degree node.data.orientation (node.data.q i))).trans node.data.factors_degree)
    · intro i; simp
    · intro B hB u hu
      rw [hchildren] at hB
      obtain ⟨_,sign,rfl⟩ := (mem_ownedOwnerCells G owner).mp hB
      obtain ⟨huG,husign⟩ := Finset.mem_filter.mp hu
      refine ⟨by rw [husign],?_,?_⟩
      · intro x hx
        obtain ⟨y,hy,rfl⟩ := hx
        rw [orientedFiniteFactor_signCell]
        have hh := hcell u huG hy
        simpa only [Set.mem_preimage,orientedFiniteProjection,ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.symm_apply_apply] using hh
      · intro x hx
        obtain ⟨y,hy,rfl⟩ := hx
        apply orientedFiniteFactor_avoids_closed_wall node.data.orientation node.data.q _ _ r hr hgap
        have hh := havoid u huG y hy
        simpa only [orientedFiniteProjection,ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.symm_apply_apply] using hh
    · simp [he]
    · simp [he]
    · simp [he]

/-- Total canonical node data for one shared physical recursion. Invalid masks
have no children and no selected cubes; the actual nodes keep their witnesses. -/
theorem actual_buffered_forest_physical
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (hP : ∀ i, (P i).totalDegree ≤ J) (δ : ℝ) (hr : 0 < r) (hgap : 2*δ < r) :
    ∃ (p : Finset C → Fin s → MvPolynomial (Fin (b+c)) ℝ)
      (owner : Finset C → C → Fin s → Bool)
      (merge : Finset C × (Fin s → Bool) → Finset C)
      (f : Finset C → Fin (c+1) → MvPolynomial (Fin (b+c)) ℝ),
      (∀ A, (∏ i, p A i).totalDegree ≤ b*(∑ j ∈ Finset.range s, D j)) ∧
      (∀ A i, (f A i).totalDegree ≤ max J (max (2*c*(J-1)) (b*(∑ j ∈ Finset.range s, D j)))) ∧
      (∀ A B, B ∈ ownedPartitionChildren root forest.node A → ∀ u ∈ B,
        merge (A,owner A u)=B ∧ physicalCoordinateCube (Q u) ⊆ polynomialSignCell (p A) (owner A u) ∧
        ∀ x ∈ physicalCoordinateCube (Q u), x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ i, p A i))) ∧
      (∀ A u, u ∈ ownedPartitionSelected root forest.node A →
        physicalCoordinateCube (Q u) ⊆ thickening (η+2*(η+r)) {x | rectangularPolynomialMap (f A) x=0}) ∧
      (∀ A, (ownedPartitionSelected root forest.node A).Nonempty → ∀ x,
        rectangularPolynomialMap (f A) x=0 → (fderiv ℝ (rectangularPolynomialMap (f A)) x).range=⊤) ∧
      (∀ A, (ownedPartitionSelected root forest.node A).Nonempty → ∀ i,
        f A i.succ=rename finSumFinEquiv (P i)) := by
  have hex : ∀ A : Finset C, ∃ (p : Fin s → MvPolynomial (Fin (b+c)) ℝ)
      (owner : C → Fin s → Bool) (merge : (Fin s → Bool) → Finset C)
      (f : Fin (c+1) → MvPolynomial (Fin (b+c)) ℝ),
      (∏ i, p i).totalDegree ≤ b*(∑ j ∈ Finset.range s, D j) ∧
      (∀ i, (f i).totalDegree ≤ max J (max (2*c*(J-1)) (b*(∑ j ∈ Finset.range s, D j)))) ∧
      (∀ B ∈ ownedPartitionChildren root forest.node A, ∀ u ∈ B,
        merge (owner u)=B ∧ physicalCoordinateCube (Q u) ⊆ polynomialSignCell p (owner u) ∧
        ∀ x ∈ physicalCoordinateCube (Q u), x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ i, p i))) ∧
      (∀ u ∈ ownedPartitionSelected root forest.node A,
        physicalCoordinateCube (Q u) ⊆ thickening (η+2*(η+r)) {x | rectangularPolynomialMap f x=0}) ∧
      ((ownedPartitionSelected root forest.node A).Nonempty → ∀ x, rectangularPolynomialMap f x=0 →
        (fderiv ℝ (rectangularPolynomialMap f) x).range=⊤) ∧
      ((ownedPartitionSelected root forest.node A).Nonempty → ∀ i,
        f i.succ=rename finSumFinEquiv (P i)) := by
    intro A
    by_cases ha : A ⊆ root ∧ A.Nonempty
    · exact actual_buffered_node_physical forest hP δ hr hgap A ha.1 ha.2
    · refine ⟨fun _ : Fin s => (1:MvPolynomial (Fin (b+c)) ℝ),fun _ : C => fun _ : Fin s => false,
        fun _ => (∅:Finset C),fun _ : Fin (c+1) => (0:MvPolynomial (Fin (b+c)) ℝ),?_,?_,?_,?_,?_,?_⟩
      · simp
      · simp
      · simp [ownedPartitionChildren,ha]
      · simp [ownedPartitionSelected,ha]
      · simp [ownedPartitionSelected,ha]
      · simp [ownedPartitionSelected,ha]
  choose p owner merge f hp hf hchild hleaf hregular htail using hex
  exact ⟨p,owner,fun a => merge a.1 a.2,f,hp,hf,hchild,hleaf,hregular,htail⟩

/-- The literal whole cube retains preconnectedness under coordinate renaming. -/
theorem physicalCoordinateCube_preconnected {b c : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (hU : IsPreconnected U) :
    IsPreconnected (physicalCoordinateCube U) :=
  hU.image _ (euclideanCoordinateRename finSumFinEquiv).continuous.continuousOn

/-- All geometry demanded by the shared physical iteration is derived from
actual forest routes. No sign-cell, clearance, merging or capture input is added. -/
theorem actual_buffered_routes_physical
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q w η r depth)
    (selection : ActualBufferedCommonDepth forest) (routes : ActualBufferedRoutes forest selection)
    (hP : ∀ i, (P i).totalDegree ≤ J) (δ : ℝ) (hr : 0 < r) (hgap : 2*δ < r) :
    ∃ (route : ℕ → C → Finset C)
      (p : ℕ → Finset C → Fin s → MvPolynomial (Fin (b+c)) ℝ)
      (owner : ℕ → C → Fin s → Bool)
      (merge : ℕ → Finset C × (Fin s → Bool) → Finset C)
      (f : Finset C → Fin (c+1) → MvPolynomial (Fin (b+c)) ℝ),
      (∀ u, route 0 u=root) ∧
      (∀ i < selection.d, ∀ u ∈ selection.cubes, route (i+1) u=merge i (route i u,owner i u)) ∧
      (∀ i A, (∏ j, p i A j).totalDegree ≤ b*(∑ j ∈ Finset.range s, D j)) ∧
      (∀ i < selection.d, ∀ u ∈ selection.cubes,
        physicalCoordinateCube (Q u) ⊆ polynomialSignCell (p i (route i u)) (owner i u)) ∧
      (∀ i < selection.d, ∀ u ∈ selection.cubes, ∀ x ∈ physicalCoordinateCube (Q u),
        x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ j, p i (route i u) j))) ∧
      (∀ A j, (f A j).totalDegree ≤ max J (max (2*c*(J-1)) (b*(∑ j ∈ Finset.range s, D j)))) ∧
      (∀ u ∈ selection.cubes, physicalCoordinateCube (Q u) ⊆
        thickening (η+2*(η+r)) {x | rectangularPolynomialMap (f (route selection.d u)) x=0}) ∧
      (∀ u : {u // u ∈ selection.cubes}, route selection.d u.val=routes.leaf u) ∧
      (∀ u ∈ selection.cubes, ∀ x, rectangularPolynomialMap (f (route selection.d u)) x=0 →
        (fderiv ℝ (rectangularPolynomialMap (f (route selection.d u))) x).range=⊤) ∧
      (∀ u ∈ selection.cubes, ∀ i,
        f (route selection.d u) i.succ=rename finSumFinEquiv (P i)) := by
  obtain ⟨p,owner,merge,f,hdeg,hf,hchild,hleaf,hregular,htail⟩ := actual_buffered_forest_physical forest hP δ hr hgap
  let route := fun i u => if hu : u ∈ selection.cubes then
    routes.route ⟨u,hu⟩ ⟨min i selection.d,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ else root
  have hroute (i : ℕ) (hi : i ≤ selection.d) (u : C) (hu : u ∈ selection.cubes) :
      route i u=routes.route ⟨u,hu⟩ ⟨i,Nat.lt_succ_of_le hi⟩ := by
    simp only [route,dite_eq_left hu,Nat.min_eq_left hi]
  have hend (u : {u // u ∈ selection.cubes}) : route selection.d u.val=routes.leaf u := by
    rw [hroute selection.d le_rfl u.val u.property]
    exact routes.leaf_exact u
  have hedge (i : ℕ) (hi : i < selection.d) (u : C) (hu : u ∈ selection.cubes) :
      route (i+1) u ∈ ownedPartitionChildren root forest.node (route i u) := by
    rw [hroute (i+1) (by omega) u hu,hroute i hi.le u hu]
    exact routes.edge ⟨u,hu⟩ ⟨i,hi⟩
  have hmem (i : ℕ) (hi : i ≤ selection.d) (u : C) (hu : u ∈ selection.cubes) :
      u ∈ route i u := by
    rw [hroute i hi u hu]
    exact routes.cube_on_route ⟨u,hu⟩ _
  refine ⟨route,fun _ => p,fun i u => owner (route i u) u,fun _ => merge,f,?_,?_,?_,?_,?_,hf,?_,hend,?_,?_⟩
  · intro u
    by_cases hu : u ∈ selection.cubes
    · rw [hroute 0 (Nat.zero_le _) u hu]
      exact routes.root_exact ⟨u,hu⟩
    · simp [route,hu]
  · intro i hi u hu
    exact (hchild _ _ (hedge i hi u hu) u (hmem (i+1) (by omega) u hu)).1.symm
  · intro i A; exact hdeg A
  · intro i hi u hu
    exact (hchild _ _ (hedge i hi u hu) u (hmem (i+1) (by omega) u hu)).2.1
  · intro i hi u hu
    exact (hchild _ _ (hedge i hi u hu) u (hmem (i+1) (by omega) u hu)).2.2
  · intro u hu
    rw [hend ⟨u,hu⟩]
    exact hleaf _ u (routes.cube_selected ⟨u,hu⟩)
  · intro u hu
    rw [hend ⟨u,hu⟩]
    exact hregular _ ⟨u,routes.cube_selected ⟨u,hu⟩⟩
  · intro u hu
    rw [hend ⟨u,hu⟩]
    exact htail _ ⟨u,routes.cube_selected ⟨u,hu⟩⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_buffered_node_physical
#print axioms KakeyaTwoScale.actual_buffered_forest_physical

#print axioms KakeyaTwoScale.physicalCoordinateCube_preconnected
#print axioms KakeyaTwoScale.actual_buffered_routes_physical
