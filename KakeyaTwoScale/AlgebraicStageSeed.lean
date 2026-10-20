module
public import KakeyaTwoScale.RawFamilySeed
public import KakeyaTwoScale.AlgebraicLeafPieces

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Construct a simultaneous algebraic-stage seed from incoming physical
cylinders. The ONLY variety-analysis premise is the supplied finite safe axis
cover (and its cardinality bound). Child intervals, incidence choices,
physical sharing, disjointness, exact lengths and balanced state are outputs. -/
theorem exists_algebraic_stage_seed {n k A J B K : ℕ} {T C O P G : Type}
    [DecidableEq T] [DecidableEq C] (hk : 0 < k)
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (cubes : Finset C)
    (center : C → EuclideanSpace ℝ (Fin n))
    (parent : T → Fin k → P) (grain : C → G) (origin : Fin k → P → G)
    (original : Fin k → P → O) (b u : Fin k → P → EuclideanSpace ℝ (Fin n))
    (L : Fin k → P → ℝ) (W : G → Set (EuclideanSpace ℝ (Fin n)))
    (S : Fin k → P → Finset (ℝ × ℝ)) {δ p R : ℝ}
    (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1) (hne : Y.Nonempty)
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
    (hgood : ∀ y ∈ Y, Q (cube y) ⊆ thickening (R*δ) (W (grain (cube y))))
    (hScard : ∀ j t, (S j t).card ≤ K)
    (hS : ∀ j t a, a ∈ S j t → 0 ≤ a.1 ∧ a.1 ≤ a.2 ∧ a.2 ≤ L j t)
    (hsafe : ∀ j t a, a ∈ S j t → ∀ s ∈ Icc a.1 a.2,
      ∃ z ∈ W (origin j t), dist (b j t+s • u j t) z ≤ (R+1)*δ)
    (hcover : ∀ j t s, s ∈ Ioo (0:ℝ) (L j t) →
      (∃ z ∈ W (origin j t), dist (b j t+s • u j t) z ≤ (R+1)*δ) →
        ∃ a ∈ S j t, s ∈ Icc a.1 a.2) :
    ∃ (V : FrozenGeometryState n k T C O) (lift : V.Grain → G),
      V.Valid Y cube tube Q δ ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      (∀ j, V.height j ≤ J) ∧
      V.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      tupleCubeMass Y cube cubes p /
        ((((J+1)^k * (3^k*(2*(A+n+5)+1)^n) * (B+1)^(k+1):ℕ):ℝ)) ≤
        tupleCubeMass V.tuples cube cubes p ∧
      (∀ j, (V.count j:ℝ) ≤ 2*K*((Y.image (fun y => parent y j)).card:ℝ)) ∧
      (∀ y ∈ V.tuples, lift (V.grain (cube y))=grain (cube y)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.geometry δ j (V.parent y j) ⊆
        flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ ∩
          thickening ((R+3)*δ) (W (grain (cube y)))) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=u j (parent y j)) := by
  classical
  let : DecidableEq P := Classical.decEq P
  let : DecidableEq (P × (ℝ × ℝ)) := Classical.decEq _
  have hex j t := exists_algebraic_leaf_pieces (b j t) (u j t) (W (origin j t))
    (S j t) (hu j t) hδ (hlen j t).1 (hS j t) (hsafe j t) (hcover j t)
  choose U hcard hvalid hwithin hgeom hretain using hex
  have hchoose : ∀ y j, ∃ a : ℝ × ℝ, y ∈ Y →
      a ∈ U j (parent y j) ∧
        (Q (cube y) ∩ axisCylinder (b j (parent y j)) (u j (parent y j)) a δ).Nonempty := by
    intro y j
    by_cases hy : y ∈ Y
    · obtain ⟨x,hxQ,hxp⟩ := hinc y hy j
      have hxW : x ∈ thickening (R*δ) (W (origin j (parent y j))) := by
        rw [horigin y hy j]
        exact hgood y hy hxQ
      obtain ⟨a,ha,hxa⟩ := Set.mem_iUnion₂.mp (hretain j (parent y j) ⟨hxp,hxW⟩)
      exact ⟨a,fun _ => ⟨ha,x,hxQ,hxa⟩⟩
    · exact ⟨(0,0),fun hy' => False.elim (hy hy')⟩
  choose chosen hchosen using hchoose
  let child (y : T) (j : Fin k) : P × (ℝ × ℝ) := (parent y j,chosen y j)
  let cb (j : Fin k) (t : P × (ℝ × ℝ)) := b j t.1+t.2.1 • u j t.1
  let cu (j : Fin k) (t : P × (ℝ × ℝ)) := u j t.1
  let cl (j : Fin k) (t : P × (ℝ × ℝ)) := t.2.2-t.2.1
  have hchilddis : ∀ j o, PairwiseDisjoint
      {t | t ∈ Y.image (fun y => child y j) ∧ original j t.1=o}
      (fun t => flatCylinder (cb j t) (cu j t) (cl j t) δ) := by
    intro j o a ha c hc hac
    obtain ⟨y,hy,hya⟩ := Finset.mem_image.mp ha.1
    obtain ⟨z,hz,hzc⟩ := Finset.mem_image.mp hc.1
    subst a c
    change Disjoint (axisCylinder (b j (parent y j)) (u j (parent y j)) (chosen y j) δ)
      (axisCylinder (b j (parent z j)) (u j (parent z j)) (chosen z j) δ)
    by_cases he : parent y j=parent z j
    · have hne : chosen y j ≠ chosen z j := by
        intro hh
        apply hac
        exact Prod.ext he hh
      rw [he]
      exact hwithin j (parent z j) (by simpa only [he,Finset.mem_coe] using (hchosen y j hy).1)
        (hchosen z j hz).1 hne
    · have hd := hdis j o
        ⟨Finset.mem_image_of_mem _ hy,ha.2⟩ ⟨Finset.mem_image_of_mem _ hz,hc.2⟩ he
      exact hd.mono
        ((hgeom j (parent y j) _ (hchosen y j hy).1).trans Set.inter_subset_left)
        ((hgeom j (parent z j) _ (hchosen z j hz).1).trans Set.inter_subset_left)
  have hchildlen : ∀ y ∈ Y, ∀ j,
      δ ≤ cl j (child y j) ∧ cl j (child y j) ≤ δ*2^J := by
    intro y hy j
    have hv := hvalid j (parent y j) _ (hchosen y j hy).1
    dsimp [cl,child]
    exact ⟨hv.2.1,by linarith [(hlen j (parent y j)).2]⟩
  obtain ⟨V,lift,hVv,hVb,hVne,hVH,hVr,hVm,hVc,hVlift,hVgeom,hVaxis⟩ :=
    exists_seed_from_physical_family hk Y cube tube Q cubes center child grain
      (fun j t => origin j t.1) (fun j t => original j t.1) cb cu cl
      hδ hp hp1 hne hcubes hbound (fun j t => hu j t.1)
      horiginal horigin (fun y hy j => (hchosen y j hy).2) hchilddis hchildlen hQ
  refine ⟨V,lift,hVv,hVb,hVne,hVH,hVr,hVm,?_,hVlift,?_,hVaxis⟩
  · intro j
    let F := (Y.image (fun y => parent y j)).biUnion
      (fun t => (U j t).image (fun a => (t,a)))
    have hsub : Y.image (fun y => child y j) ⊆ F := by
      intro t ht
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_biUnion.mpr ⟨parent y j,Finset.mem_image_of_mem _ hy,
        Finset.mem_image_of_mem _ (hchosen y j hy).1⟩
    have hcount : (Y.image (fun y => child y j)).card ≤ K*(Y.image (fun y => parent y j)).card := by
      calc
        _ ≤ F.card := Finset.card_le_card hsub
        _ ≤ ∑ t ∈ Y.image (fun y => parent y j), (U j t).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_image_le))
        _ ≤ ∑ _t ∈ Y.image (fun y => parent y j), K :=
          Finset.sum_le_sum (fun t _ => (hcard j t).trans (hScard j t))
        _ = _ := by simp [mul_comm]
    have hc : ((Y.image (fun y => child y j)).card:ℝ) ≤ K*((Y.image (fun y => parent y j)).card:ℝ) := by
      exact_mod_cast hcount
    exact (hVc j).trans (by nlinarith)
  · intro y hy j
    have hg := hgeom j (parent y j) _ (hchosen y j (hVv.1 hy)).1
    rw [horigin y (hVv.1 hy) j] at hg
    exact (hVgeom y hy j).trans hg

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_algebraic_stage_seed
