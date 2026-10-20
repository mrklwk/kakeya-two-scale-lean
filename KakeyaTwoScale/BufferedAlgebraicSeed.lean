module
public import KakeyaTwoScale.PolynomialAlgebraicStageSeed
public import KakeyaTwoScale.WholeCubeTupleSelection

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Construct shared physical pieces and a balanced exact-length seed from
an actual whole-cube algebraic branch. The selected input relation keeps full
original fibers; later seed balancing may filter tuples. No interval cover,
physical output family, or normalized seed is assumed. -/
theorem exists_buffered_algebraic_seed {n k A J B m D : ℕ} {T C O P G : Type}
    [DecidableEq T] [DecidableEq C] (hk : 0 < k)
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (cubes : Finset C)
    (center : C → EuclideanSpace ℝ (Fin n)) (selected : Finset C)
    (parent : T → Fin k → P) (grain : C → G) (origin : Fin k → P → G)
    (original : Fin k → P → O) (b u : Fin k → P → EuclideanSpace ℝ (Fin n))
    (L : Fin k → P → ℝ) (f : G → Fin m → MvPolynomial (Fin n) ℝ)
    (hf : ∀ g j, (f g j).totalDegree ≤ D) {δ p R eta : ℝ}
    (hradius : 0 ≤ (R+1)*δ)
    (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1) (heta : 0 < eta)
    (hpos : 0 < tupleCubeMass Y cube cubes p)
    (hretain : eta * tupleCubeMass Y cube cubes p ≤
      tupleCubeMass (Y.filter fun y => cube y ∈ selected) cube cubes p)
    (hcubes : ∀ y ∈ Y, cube y ∈ cubes) (hbound : (Y.card:ℝ) ≤ (2:ℝ)^B)
    (hu : ∀ j t, ‖u j t‖=1)
    (horiginal : ∀ y ∈ Y, ∀ j, original j (parent y j)=tube y j)
    (horigin : ∀ y ∈ Y, ∀ j, origin j (parent y j)=grain (cube y))
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩
      flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ).Nonempty)
    (hdis : ∀ j o, PairwiseDisjoint
      {t | t ∈ Y.image (fun y => parent y j) ∧ original j t=o}
      (fun t => flatCylinder (b j t) (u j t) (L j t) δ))
    (hlen : ∀ j t, δ ≤ L j t ∧ L j t ≤ δ*2^J)
    (hQ : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*δ)
    (hgood : ∀ q ∈ selected, Q q ⊆ thickening (R*δ) (polynomialGrainZeroSet f (grain q)))
 :
    ∃ (V : FrozenGeometryState n k T C O) (lift : V.Grain → G),
      V.Valid Y cube tube Q δ ∧
      V.tuples ⊆ Y.filter (fun y => cube y ∈ selected) ∧
      (∀ q ∈ selected, (Y.filter fun y => cube y ∈ selected).filter (fun y => cube y=q) =
        Y.filter (fun y => cube y=q)) ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      (∀ j, V.height j ≤ J) ∧
      V.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      (eta * tupleCubeMass Y cube cubes p) /
        ((((J+1)^k * (3^k*(2*(A+n+5)+1)^n) * (B+1)^(k+1):ℕ):ℝ)) ≤
        tupleCubeMass V.tuples cube cubes p ∧
      (∀ j, (V.count j:ℝ) ≤ 2*algebraicAxisCoverBudget n D*((Y.image (fun y => parent y j)).card:ℝ)) ∧
      (∀ y ∈ V.tuples, lift (V.grain (cube y))=grain (cube y)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.geometry δ j (V.parent y j) ⊆
        flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ ∩
          thickening ((R+3)*δ) (polynomialGrainZeroSet f (grain (cube y)))) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=u j (parent y j)) := by
  classical
  let YG := Y.filter fun y => cube y ∈ selected
  have hsub : YG ⊆ Y := Finset.filter_subset _ _
  have hne : YG.Nonempty := by
    by_contra hn
    have he : YG = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : tupleCubeMass YG cube cubes p = 0 := by
      simp [he, tupleCubeMass, ParentLevel.capacity, Real.zero_rpow hp.ne']
    have hr : eta * tupleCubeMass Y cube cubes p ≤ tupleCubeMass YG cube cubes p := hretain
    rw [hz] at hr
    exact (not_le_of_gt (mul_pos heta hpos)) hr
  have hcardG : (YG.card : ℝ) ≤ Y.card := by
    exact_mod_cast Finset.card_le_card hsub
  have hboundG : (YG.card : ℝ) ≤ (2:ℝ)^B := hcardG.trans hbound
  have hdisG : ∀ j o, PairwiseDisjoint
      {t | t ∈ YG.image (fun y => parent y j) ∧ original j t=o}
      (fun t => flatCylinder (b j t) (u j t) (L j t) δ) := by
    intro j o
    have hh : ∀ t, t ∈ YG.image (fun y => parent y j) →
        t ∈ Y.image (fun y => parent y j) := fun t ht =>
      Finset.image_subset_image hsub ht
    intro t ht s hs hts
    exact hdis j o ⟨hh t ht.1,ht.2⟩ ⟨hh s hs.1,hs.2⟩ hts
  obtain ⟨V,lift,hv,hb,hVne,hh,hr,hm,hc,hl,hgeom,haxis⟩ :=
    exists_polynomial_algebraic_stage_seed hk YG cube tube Q cubes center
      parent grain origin original b u L f hf hradius hδ hp hp1 hne
      (fun y hy => hcubes y (hsub hy)) hboundG hu
      (fun y hy => horiginal y (hsub hy)) (fun y hy => horigin y (hsub hy))
      (fun y hy => hinc y (hsub hy)) hdisG hlen hQ
      (fun y hy => hgood (cube y) (Finset.mem_filter.mp hy).2)
  refine ⟨V,lift,⟨hv.1.trans hsub,hv.2⟩,hv.1,?_,hb,hVne,hh,hr,?_,?_,hl,hgeom,haxis⟩
  · intro q hq
    exact cube_selection_full_fiber Y cube selected hq
  · exact (div_le_div_of_nonneg_right hretain (by positivity)).trans hm
  · intro j
    have hi : YG.image (fun y => parent y j) ⊆ Y.image (fun y => parent y j) :=
      Finset.image_subset_image hsub
    exact (hc j).trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_card hi) (by positivity))

/-- Shared children are constructed once per physical parent from its actual
polynomial successor. The pre-normalization relation retains every selected
tuple, independently of how many tuples use that parent. -/
theorem exists_buffered_algebraic_children {n k m D : ℕ} {T C P : Type}
    [DecidableEq T] [DecidableEq C]
    (Y : Finset T) (cube : T → C) (selected : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (parent : T → Fin k → P) (b u : P → EuclideanSpace ℝ (Fin n))
    (L : P → ℝ) (f : P → Fin m → MvPolynomial (Fin n) ℝ)
    (hf : ∀ t i, (f t i).totalDegree ≤ D) {δ R : ℝ}
    (hδ : 0 < δ) (hradius : 0 ≤ (R+1)*δ)
    (hu : ∀ t, ‖u t‖=1) (hL : ∀ t, δ ≤ L t)
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩
      flatCylinder (b (parent y j)) (u (parent y j)) (L (parent y j)) δ).Nonempty)
    (hgood : ∀ y ∈ Y, cube y ∈ selected → ∀ j,
      Q (cube y) ⊆ thickening (R*δ) (polynomialGrainZeroSet f (parent y j))) :
    ∃ U : P → Finset (ℝ × ℝ),
      (∀ t, (U t).card ≤ algebraicAxisCoverBudget n D) ∧
      (∀ t a, a ∈ U t → 0 ≤ a.1 ∧ δ ≤ a.2-a.1 ∧ a.2 ≤ L t) ∧
      (∀ t, PairwiseDisjoint (↑(U t) : Set (ℝ × ℝ)) (fun a => axisCylinder (b t) (u t) a δ)) ∧
      (∀ t a, a ∈ U t → axisCylinder (b t) (u t) a δ ⊆
        flatCylinder (b t) (u t) (L t) δ ∩
          thickening ((R+3)*δ) (polynomialGrainZeroSet f t)) ∧
      (Y.filter (fun y => cube y ∈ selected)).filter (fun y => ∀ j,
        ∃ a ∈ U (parent y j), (Q (cube y) ∩
          axisCylinder (b (parent y j)) (u (parent y j)) a δ).Nonempty) =
        Y.filter (fun y => cube y ∈ selected) := by
  classical
  have hex t := exists_algebraic_axis_intervals (f t) (hf t) (b t) (u t)
    hradius (lt_of_lt_of_le hδ (hL t))
  choose S hcard hS hequiv using hex
  have hsafe t a (ha : a ∈ S t) s (hs : s ∈ Icc a.1 a.2) :
      ∃ z ∈ polynomialGrainZeroSet f t, dist (b t+s • u t) z ≤ (R+1)*δ :=
    ((hequiv t s).mpr ⟨a,ha,hs⟩).2
  have hcover t s (hs : s ∈ Ioo (0:ℝ) (L t))
      (hz : ∃ z ∈ polynomialGrainZeroSet f t, dist (b t+s • u t) z ≤ (R+1)*δ) :
      ∃ a ∈ S t, s ∈ Icc a.1 a.2 :=
    (hequiv t s).mp ⟨⟨hs.1.le,hs.2.le⟩,hz⟩
  have hexU t := exists_algebraic_leaf_pieces (b t) (u t)
    (polynomialGrainZeroSet f t) (S t) (hu t) hδ (hL t) (hS t) (hsafe t) (hcover t)
  choose U hUc hUv hUd hUg hUr using hexU
  refine ⟨U,fun t => (hUc t).trans (hcard t),hUv,hUd,hUg,?_⟩
  apply Finset.filter_eq_self.mpr
  intro y hy j
  obtain ⟨hyY,hyG⟩ := Finset.mem_filter.mp hy
  obtain ⟨x,hxQ,hxp⟩ := hinc y hyY j
  obtain ⟨a,ha,hxa⟩ := Set.mem_iUnion₂.mp
    (hUr (parent y j) ⟨hxp,hgood y hyY hyG j hxQ⟩)
  exact ⟨a,ha,x,hxQ,hxa⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_buffered_algebraic_seed

#print axioms KakeyaTwoScale.exists_buffered_algebraic_children
