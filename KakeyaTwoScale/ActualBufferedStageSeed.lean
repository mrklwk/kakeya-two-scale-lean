module
public import KakeyaTwoScale.ActualBufferedPhysical
public import KakeyaTwoScale.BufferedTupleForest
public import KakeyaTwoScale.CellularAlgebraicSeed
public import KakeyaTwoScale.SeedSupportTransport
public import KakeyaTwoScale.BufferedSeedMassCap

@[expose] public section

open Set MeasureTheory Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Explicit losses from cellular orientation selection, stopping-depth
selection and the existing exact-length/spatial/whole-grain seed balancing. -/
def bufferedForestLoss (orientationCount s depth : ℕ) : ℝ :=
  ((2*(orientationCount:ℝ))^depth*((2*(orientationCount:ℝ))*(s+1:ℕ)))*(depth+1:ℕ)

def bufferedSeedLoss (n k A Lh B : ℕ) : ℝ :=
  (((Lh+1)^k * (3^k*(2*(A+n+5)+1)^n) * (B+1)^(k+1):ℕ):ℝ)

/-- A genuine shared balanced seed, measured against the original input
relation and original represented parent records. -/
structure ActualBufferedStageSeed {b c J s k A Lh B depth : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (D : ℕ → ℕ)
    (S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O) (root : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (W : CellularPhysicalFamily (b+c) k T O (Finset C)) (alpha δ R : ℝ) where
  cellular_depth : ℕ
  cellular_depth_le : cellular_depth ≤ depth
  leaf_masks : Finset (Finset C)
  leaf_disjoint : (↑leaf_masks : Set (Finset C)).PairwiseDisjoint id
  leaf_subset : ∀ g ∈ leaf_masks, g ⊆ root
  state : FrozenGeometryState (b+c) k T C O
  lift : state.Grain → Finset C
  equations : Finset C → Fin (c+1) → MvPolynomial (Fin (b+c)) ℝ
  selected : Finset C
  leaf_membership : ∀ y ∈ state.tuples, lift (state.grain (cube y)) ∈ leaf_masks
  cube_in_leaf : ∀ y ∈ state.tuples, cube y ∈ lift (state.grain (cube y))
  selected_subset : selected ⊆ root
  selected_fibers : ∀ q ∈ selected,
    (Y.filter fun y => cube y ∈ selected).filter (fun y => cube y=q)=Y.filter (fun y => cube y=q)
  tuples_subset : state.tuples ⊆ Y.filter (fun y => cube y ∈ selected)
  valid : state.Valid Y cube tube (fun q => physicalCoordinateCube (Q q)) δ
  balanced : state.Balanced cube root alpha
  nonempty : state.tuples.Nonempty
  heights : ∀ j, state.height j ≤ Lh
  ball_radius : state.ballRadius ≤ (A+(b+c)+5:ℝ)*δ*(∑ j, (2:ℝ)^(state.height j))
  mass : tupleCubeMass Y cube root alpha /
      (bufferedForestLoss S.card s depth * bufferedSeedLoss (b+c) k A Lh B) ≤
    tupleCubeMass state.tuples cube root alpha
  count : ∀ j, (state.count j:ℝ) ≤
    2*algebraicAxisCoverBudget (b+c) (max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, D i)))) *
      (((b*(∑ i ∈ Finset.range s, D i)+1:ℕ):ℝ)^cellular_depth*((W.records Y j).card:ℝ))
  grain_mass_cap : ∀ g ∈ state.grains cube,
    tupleCubeMass (state.tuples.filter fun y => state.grain (cube y)=g) cube root alpha ≤
      ((2:ℝ)/2^s)^cellular_depth*tupleCubeMass Y cube root alpha
  degrees : ∀ g i, (equations g i).totalDegree ≤
    max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, D i)))
  regular : ∀ y ∈ state.tuples, ∀ x,
    rectangularPolynomialMap (equations (lift (state.grain (cube y)))) x=0 →
      (fderiv ℝ (rectangularPolynomialMap (equations (lift (state.grain (cube y))))) x).range=⊤
  old_equations : ∀ y ∈ state.tuples, ∀ i,
    equations (lift (state.grain (cube y))) i.succ = MvPolynomial.rename finSumFinEquiv (P i)
  geometry : ∀ y ∈ state.tuples, ∀ j, state.geometry δ j (state.parent y j) ⊆
    W.geometry δ (W.parent y j) ∩
      thickening ((R+3)*δ) (polynomialGrainZeroSet equations (lift (state.grain (cube y))))
  axes : ∀ y ∈ state.tuples, ∀ j, state.axis j (state.parent y j)=W.axis (W.parent y j)

/-- Construct the shared seed from an actual forest, discharging every route,
physical-successor and polynomial-axis-cover obligation internally. -/
theorem exists_seed_of_actual_buffered_forest {b c J s k A Lh B depth : ℕ}
    {T C O : Type} [DecidableEq T] [DecidableEq C]
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (hP : ∀ i, (P i).totalDegree ≤ J)
    (D : ℕ → ℕ)
    (S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O) (root : Finset C)
    (hr : root.Nonempty) (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (alpha η r δ R : ℝ) (hp : 0 < alpha) (hp1 : alpha ≤ 1) (hδ : 0 < δ)
    (hradius : 0 < r) (hgap : 2*δ < r) (hR : η+2*(η+r) ≤ R*δ) (hR0 : 0 ≤ (R+1)*δ)
    (hactive : ∀ q ∈ root, 1 ≤ ParentLevel.capacity Y cube q)
    (hQ : ∀ q ∈ root, IsPreconnected (Q q))
    (forest : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q (bufferedTupleWeight Y cube alpha) η r depth)
    (hk : 0 < k) (W : CellularPhysicalFamily (b+c) k T O (Finset C))
    (hW : W.Valid Y cube tube (fun q => physicalCoordinateCube (Q q)) (fun _ => root) δ (δ*2^Lh))
    (hbound : (Y.card:ℝ) ≤ (2:ℝ)^B)
    (center : C → EuclideanSpace ℝ (Fin (b+c)))
    (hdiam : ∀ q ∈ root, ∀ x ∈ physicalCoordinateCube (Q q), dist x (center q) ≤ (A:ℝ)*δ) :
    Nonempty (ActualBufferedStageSeed (J:=J) (s:=s) (A:=A) (Lh:=Lh) (B:=B) (depth:=depth)
      P D S Y cube tube root Q W alpha δ R) := by
  classical
  let w := bufferedTupleWeight Y cube alpha
  have hw : ∀ q, 1 ≤ w q := fun q => le_max_left _ _
  obtain ⟨selection,⟨routes⟩⟩ := exists_actual_buffered_routes forest hw hr
  have hG : selection.cubes ⊆ root := by
    rw [selection.cubes_exact]
    intro q hq
    obtain ⟨leaf,hl,hq⟩ := Finset.mem_biUnion.mp hq
    exact (forest.terminal leaf (selection.leaves_subset hl)).2.1
      ((forest.terminal leaf (selection.leaves_subset hl)).2.2.2.2.1 hq)
  let Z := Y.filter (fun y => cube y ∈ selection.cubes)
  have hZY : Z ⊆ Y := Finset.filter_subset _ _
  have hZ : ∀ y ∈ Z, cube y ∈ selection.cubes := fun y hy => (Finset.mem_filter.mp hy).2
  have hZne : Z.Nonempty := by
    obtain ⟨q,hq⟩ := selection.cubes_nonempty
    have hcap : 0 < ParentLevel.capacity Y cube q := lt_of_lt_of_le (by omega) (hactive q (hG hq))
    obtain ⟨y,hy⟩ := Finset.card_pos.mp hcap
    have hmem := Finset.mem_filter.mp hy
    exact ⟨y,Finset.mem_filter.mpr ⟨hmem.1,hmem.2 ▸ hq⟩⟩
  have heq : ∀ q ∈ root, w q=(ParentLevel.capacity Y cube q:ℝ)^alpha := by
    intro q hq
    exact max_eq_right (Real.one_le_rpow (by exact_mod_cast hactive q hq) hp.le)
  have htotal : ownedCubeMass w root=tupleCubeMass Y cube root alpha :=
    Finset.sum_congr rfl (fun q hq => heq q hq)
  have hselected : ownedCubeMass w selection.cubes=tupleCubeMass Z cube root alpha := by
    rw [whole_cube_selection_mass Y cube root selection.cubes hG hp]
    exact Finset.sum_congr rfl (fun q hq => heq q (hG hq))
  dsimp only [w] at htotal hselected
  have hretain : tupleCubeMass Y cube root alpha / bufferedForestLoss S.card s depth ≤
      tupleCubeMass Z cube root alpha := by
    simpa only [bufferedForestLoss,htotal,hselected] using selection.retention
  obtain ⟨route,p,owner,merge,f,hroot,hroute,hdeg,hcell,hwall,hf,hcapture,hend,hregular,htail⟩ :=
    actual_buffered_routes_physical forest selection routes hP δ hradius hgap
  have hv : W.Valid Z cube tube (fun q => physicalCoordinateCube (Q q)) (route 0) δ (δ*2^Lh) := by
    have hh := W.valid_mono Y Z cube tube (fun q => physicalCoordinateCube (Q q))
      (fun _ => root) δ (δ*2^Lh) hZY hW
    have he : route 0=(fun _ => root) := funext hroot
    simpa only [he] using hh
  have hset (g : Finset C) : {x | rectangularPolynomialMap (f g) x=0}=polynomialGrainZeroSet f g := by
    ext x
    constructor
    · intro hx i
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (c+1)) => v i) hx
    · intro hx
      apply PiLp.ext
      exact hx
  obtain ⟨V,lift,hv',hb,hne,hh,hball,hm,hcount,hl,hgeom,haxis⟩ :=
    CellularPhysicalFamily.exists_iterated_algebraic_seed (A:=A) (J:=Lh) (B:=B) hk W Z cube tube
      (fun q => physicalCoordinateCube (Q q)) selection.cubes route p owner merge hδ hv hZ
      (fun q hq => physicalCoordinateCube_preconnected _ (hQ q (hG hq))) selection.d
      hroute (fun i _ => hdeg i) hcell hwall center f hf hR0 hp hp1 hZne
      (le_trans (by exact_mod_cast Finset.card_le_card hZY) hbound)
      (fun q hq => hdiam q (hG hq)) (by
        intro y hy
        rw [← hset]
        exact (hcapture _ (hZ y hy)).trans (thickening_mono hR _))
  have hVsupport : ∀ y ∈ V.tuples, cube y ∈ selection.cubes := fun y hy => hZ y (hv'.1 hy)
  have hmassZ := tupleCubeMass_eq_of_support Z cube selection.cubes root hG hZ hp
  have hmassV := tupleCubeMass_eq_of_support V.tuples cube selection.cubes root hG hVsupport hp
  have hLoss : 0 < bufferedSeedLoss (b+c) k A Lh B := by
    unfold bufferedSeedLoss
    positivity
  have hmass : tupleCubeMass Y cube root alpha /
      (bufferedForestLoss S.card s depth * bufferedSeedLoss (b+c) k A Lh B) ≤
      tupleCubeMass V.tuples cube root alpha := by
    rw [← div_div]
    apply (div_le_div_of_nonneg_right hretain hLoss.le).trans
    simpa only [bufferedSeedLoss,hmassZ,hmassV] using hm
  have hleaf (y : T) (hy : y ∈ V.tuples) : lift (V.grain (cube y)) ∈ selection.leaves := by
    rw [hl y hy,hend ⟨cube y,hVsupport y hy⟩]
    exact routes.leaf_mem _
  have hcube (y : T) (hy : y ∈ V.tuples) : cube y ∈ lift (V.grain (cube y)) := by
    rw [hl y hy,hend ⟨cube y,hVsupport y hy⟩]
    have hh := routes.cube_on_route ⟨cube y,hVsupport y hy⟩ (Fin.last selection.d)
    rwa [routes.leaf_exact] at hh
  have hcap := actual_buffered_seed_grain_mass_cap Y V.tuples cube root hp (hv'.1.trans hZY)
    hactive forest selection V.grain lift hleaf hcube
  refine ⟨{
    cellular_depth := selection.d
    cellular_depth_le := selection.depth_le
    leaf_masks := selection.leaves
    leaf_disjoint := fun _ ha _ hb hne => forest.frontier_disjoint (selection.leaves_subset ha) (selection.leaves_subset hb) hne
    leaf_subset := fun g hg => (forest.terminal g (selection.leaves_subset hg)).2.1
    state := V
    lift := lift
    equations := f
    selected := selection.cubes
    leaf_membership := hleaf
    cube_in_leaf := hcube
    selected_subset := hG
    selected_fibers := fun q hq => cube_selection_full_fiber Y cube _ hq
    tuples_subset := hv'.1
    valid := ⟨hv'.1.trans hZY,hv'.2⟩
    balanced := V.balanced_of_cube_support cube selection.cubes root hG hVsupport hp hb
    nonempty := hne
    heights := hh
    ball_radius := by simpa only [Nat.cast_add] using hball
    mass := hmass
    count := ?_
    grain_mass_cap := hcap
    degrees := hf
    regular := ?_
    old_equations := ?_
    geometry := ?_
    axes := haxis }⟩
  · intro j
    apply (hcount j).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image hZY)
  · intro y hy
    rw [hl y hy]
    exact hregular _ (hVsupport y hy)
  · intro y hy
    rw [hl y hy]
    exact htail _ (hVsupport y hy)
  · intro y hy j
    rw [hl y hy]
    exact hgeom y hy j

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_seed_of_actual_buffered_forest

namespace KakeyaTwoScale

/-- Complete constructed buffered stage seed from actual incoming polynomial,
cube/tuple and tube-record data. Orientations, partitions, all cellular nodes,
common-depth routes, physical successors and the balanced seed are outputs. -/
theorem exists_actual_buffered_stage_seed (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      ∀ {J s k A Lh B depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
        (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ),
        (∀ i, (P i).totalDegree ≤ J) →
        (∀ x, rectangularPolynomialMap P x=0 →
          (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) →
        ∀ (D : ℕ → ℕ), (∀ j < s, 2^j < (D j+1)^b) → 2 ≤ s →
        ∀ (Y : Finset T) (cube : T → C) (tube : T → Fin k → O) (root : Finset C),
        root.Nonempty → (∀ q ∈ root, 1 ≤ ParentLevel.capacity Y cube q) →
        ∀ (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))),
        (∀ u ∈ root, MeasurableSet (Q u)) → (∀ u ∈ root, volume (Q u) ≠ ⊤) →
        (∀ u ∈ root, 0 < volume.real (Q u)) → (∀ u ∈ root, IsPreconnected (Q u)) →
        ∀ (alpha η r δ R : ℝ), 0 < alpha → alpha ≤ 1 → 0 < δ → 2*δ < r →
        η+2*(η+r) ≤ R*δ → 0 ≤ (R+1)*δ →
        ∀ (tag : C → EuclideanSpace ℝ (Fin b ⊕ Fin c)),
        (∀ u ∈ root, rectangularPolynomialMap P (tag u)=0) →
        (∀ u ∈ root, ∀ x ∈ Q u, dist x (tag u) < η) →
        Real.log (tupleCubeMass Y cube root alpha) / (-Real.log ((2:ℝ)/2^s)) < depth →
        0 < k → ∀ (W : CellularPhysicalFamily (b+c) k T O (Finset C)),
        W.Valid Y cube tube (fun q => physicalCoordinateCube (Q q)) (fun _ => root) δ (δ*2^Lh) →
        (Y.card:ℝ) ≤ (2:ℝ)^B → ∀ (center : C → EuclideanSpace ℝ (Fin (b+c))),
        (∀ q ∈ root, ∀ x ∈ physicalCoordinateCube (Q q), dist x (center q) ≤ (A:ℝ)*δ) →
        Nonempty (ActualBufferedStageSeed (J:=J) (s:=s) (A:=A) (Lh:=Lh) (B:=B) (depth:=depth)
          P D S Y cube tube root Q W alpha δ R) := by
  classical
  obtain ⟨S,hS⟩ := exists_actual_buffered_cube_forest b c
  refine ⟨S,?_⟩
  intro J s k A Lh B depth T C O instT instC P hPdeg hP D hd hs Y cube tube root hr hactive
    Q hQ hf hpositive hc alpha η r δ R hp hp1 hδ hgap hR hR0 tag htag hnear hdepth hk W hW hbound center hdiam
  have hradius : 0 < r := by linarith
  have htotal : ownedCubeMass (bufferedTupleWeight Y cube alpha) root=tupleCubeMass Y cube root alpha := by
    apply Finset.sum_congr rfl
    intro q hq
    exact max_eq_right (Real.one_le_rpow (by exact_mod_cast hactive q hq) hp.le)
  obtain ⟨forest⟩ := hS P hPdeg hP D hd hs root hr Q (bufferedTupleWeight Y cube alpha)
    hQ hf hpositive hc (fun q => le_max_left _ _) tag htag η r hradius hnear depth
    (by simpa only [htotal] using hdepth)
  exact exists_seed_of_actual_buffered_forest (A:=A) (Lh:=Lh) (B:=B)
    P hPdeg D S Y cube tube root hr Q alpha η r δ R hp hp1 hδ hradius hgap hR hR0
    hactive hc forest hk W hW hbound center hdiam

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_actual_buffered_stage_seed
