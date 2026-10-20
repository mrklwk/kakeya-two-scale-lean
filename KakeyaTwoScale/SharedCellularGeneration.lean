module
public import KakeyaTwoScale.SharedPolynomialCellularStep

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Simultaneously cut actual shared records by the polynomial of their
unique old node. This is the physical successor construction for a whole
cellular generation; distinct node masks do not duplicate parent records. -/
theorem exists_shared_cellular_generation {n k s : ℕ} {T C J O G : Type}
    [DecidableEq T] [DecidableEq C] [DecidableEq J]
    (p : G → Fin s → MvPolynomial (Fin n) ℝ)
    (Y : Finset T) (cube : T → C) (cubes : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (grain : C → G) (owner : C → Fin s → Bool)
    (parent : T → Fin k → J) (node : J → G) (original : J → O)
    (b u : J → EuclideanSpace ℝ (Fin n)) (L : J → ℝ) (δ : ℝ) (D : ℕ)
    (hδ : 0 < δ) (hu : ∀ t, ‖u t‖=1) (hL : ∀ t, δ ≤ L t)
    (hdeg : ∀ g, (∏ i, p g i).totalDegree ≤ D)
    (hY : ∀ y ∈ Y, cube y ∈ cubes)
    (hnode : ∀ y ∈ Y, ∀ j, node (parent y j)=grain (cube y))
    (hQ : ∀ q ∈ cubes, IsPreconnected (Q q))
    (hcell : ∀ q ∈ cubes, Q q ⊆ polynomialSignCell (p (grain q)) (owner q))
    (hwall : ∀ q ∈ cubes, ∀ x ∈ Q q,
      x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ i, p (grain q) i)))
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩ flatCylinder (b (parent y j))
      (u (parent y j)) (L (parent y j)) δ).Nonempty)
    (hdis : ∀ j o, PairwiseDisjoint
      {t | t ∈ Y.image (fun y => parent y j) ∧ original t=o}
      (fun t => flatCylinder (b t) (u t) (L t) δ)) :
    let P := fun t => ∏ i, p (node t) i
    let len := fun t : J×ℝ =>
      rootNext (cellularRoots (P t.1) (b t.1) (u t.1) (L t.1)) (L t.1) t.2-t.2
    let geom := fun t : J×ℝ => flatCylinder (b t.1+t.2 • u t.1) (u t.1) (len t) δ
    ∃ (start : T → Fin k → ℝ) (origin : Fin k → J×ℝ → G×(Fin s → Bool)),
      (∀ y ∈ Y, ∀ j,
        origin j (parent y j,start y j)=(grain (cube y),owner (cube y)) ∧
        (Q (cube y) ∩ geom (parent y j,start y j)).Nonempty ∧
        δ ≤ len (parent y j,start y j) ∧
        geom (parent y j,start y j) ⊆ flatCylinder (b (parent y j))
          (u (parent y j)) (L (parent y j)) δ) ∧
      (∀ j o, PairwiseDisjoint
        {t | t ∈ Y.image (fun y => (parent y j,start y j)) ∧ original t.1=o} geom) ∧
      (∀ t, (tupleChildStarts Y parent start t).card ≤ D+1 ∧
        (tupleChildStarts Y parent start t).sum (fun a => len (t,a)) ≤ L t) ∧
      (∀ j, ((Y.image (fun y => (parent y j,start y j))).card:ℝ) ≤
        (D+1:ℕ) * ((Y.image (fun y => parent y j)).card:ℝ)) := by
  classical
  dsimp only
  let Yg := fun g => Y.filter fun y => grain (cube y)=g
  let Cg := fun g => cubes.filter fun q => grain q=g
  have hsub g : Yg g ⊆ Y := Finset.filter_subset _ _
  have hgcell g q (hq : q ∈ Cg g) : Q q ⊆ polynomialSignCell (p g) (owner q) := by
    have hh := Finset.mem_filter.mp hq
    simpa only [hh.2] using hcell q hh.1
  have hgwall g q (hq : q ∈ Cg g) x (hx : x ∈ Q q) :
      x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ i, p g i)) := by
    have hh := Finset.mem_filter.mp hq
    simpa only [hh.2] using hwall q hh.1 x hx
  have hgd g j o : PairwiseDisjoint
      {t | t ∈ (Yg g).image (fun y => parent y j) ∧ original t=o}
      (fun t => flatCylinder (b t) (u t) (L t) δ) := by
    intro t ht v hv htv
    exact hdis j o ⟨Finset.image_subset_image (hsub g) ht.1,ht.2⟩
      ⟨Finset.image_subset_image (hsub g) hv.1,hv.2⟩ htv
  have hex g := exists_shared_polynomial_cellular_step (p g) (Yg g) cube (Cg g)
    Q owner parent original b u L δ hδ hu hL
    (fun y hy => Finset.mem_filter.mpr ⟨hY y (hsub g hy),(Finset.mem_filter.mp hy).2⟩)
    (fun q hq => hQ q (Finset.mem_filter.mp hq).1) (hgcell g) (hgwall g)
    (fun y hy => hinc y (hsub g hy)) (hgd g)
  choose st org hb hi hd hc using hex
  let start := fun y j => st (grain (cube y)) y j
  let origin := fun (j : Fin k) (t : J×ℝ) => (node t.1,org (node t.1) j t)
  have hyown y (hy : y ∈ Y) : y ∈ Yg (grain (cube y)) := Finset.mem_filter.mpr ⟨hy,rfl⟩
  have hs y (hy : y ∈ Y) j : start y j=st (node (parent y j)) y j := by
    simp only [start,hnode y hy j]
  have hmem t : tupleChildStarts Y parent start t ⊆
      tupleChildStarts (Yg (node t)) parent (st (node t)) t := by
    intro a ha
    obtain ⟨y,hy,j,hj,rfl⟩ := (mem_tupleChildStarts Y parent start t a).mp ha
    have hg : grain (cube y)=node t := by rw [← hj]; exact (hnode y hy j).symm
    exact (mem_tupleChildStarts _ _ _ _ _).mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hg⟩,
      j,hj,by simp only [start,hg]⟩
  have hgeo y (hy : y ∈ Y) j := hi (grain (cube y)) y (hyown y hy) j
  refine ⟨start,origin,?_,?_,?_,?_⟩
  · intro y hy j
    simpa only [origin,start,hnode y hy j] using
      And.intro (congrArg (fun v => (grain (cube y),v)) (hgeo y hy j).1) (hgeo y hy j).2
  · intro j o t ht v hv htv
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp ht.1
    obtain ⟨z,hz,hf⟩ := Finset.mem_image.mp hv.1
    subst t; subst v
    by_cases hg : grain (cube y)=grain (cube z)
    · have hyg := hyown y hy
      have hzg : z ∈ Yg (grain (cube y)) := Finset.mem_filter.mpr ⟨hz,hg.symm⟩
      have hh := hd (grain (cube y)) j o
        (show (parent y j,st (grain (cube y)) y j) ∈
          {t | t ∈ (Yg (grain (cube y))).image (fun w => (parent w j,st (grain (cube y)) w j)) ∧ original t.1=o}
          from ⟨Finset.mem_image.mpr ⟨y,hyg,rfl⟩,ht.2⟩)
        (show (parent z j,st (grain (cube y)) z j) ∈
          {t | t ∈ (Yg (grain (cube y))).image (fun w => (parent w j,st (grain (cube y)) w j)) ∧ original t.1=o}
          from ⟨Finset.mem_image.mpr ⟨z,hzg,rfl⟩,hv.2⟩)
        (by simpa only [start,← hg] using htv)
      simpa only [Function.onFun,Prod.fst,Prod.snd,hnode y hy j,hnode z hz j,← hg,start] using hh
    · have hp : parent y j ≠ parent z j := by
        intro hp
        exact hg ((hnode y hy j).symm.trans ((congrArg node hp).trans (hnode z hz j)))
      have hh := (hdis j o ⟨Finset.mem_image.mpr ⟨y,hy,rfl⟩,ht.2⟩
        ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,hv.2⟩ hp).mono (hgeo y hy j).2.2.2 (hgeo z hz j).2.2.2
      simpa only [Function.onFun,Prod.fst,Prod.snd,hnode y hy j,hnode z hz j,start] using hh
  · intro t
    refine ⟨(Finset.card_le_card (hmem t)).trans ((hb (node t) t).1.trans (Nat.add_le_add_right (hdeg _) 1)),?_⟩
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (hmem t) ?_) (hb (node t) t).2
    intro a ha _
    obtain ⟨y,hy,j,hj,rfl⟩ := (mem_tupleChildStarts _ _ _ _ _).mp ha
    have hh := (hi (node t) y hy j).2.2.1
    rw [hj] at hh
    exact hδ.le.trans hh
  · intro j
    apply variable_child_record_bound Y Y (fun y => parent y j) (fun y => start y j)
      (tupleChildStarts Y parent start) (Finset.Subset.refl Y)
      (fun y hy => (mem_tupleChildStarts _ _ _ _ _).mpr ⟨y,hy,j,rfl,rfl⟩)
    intro t ht
    exact_mod_cast (Finset.card_le_card (hmem t)).trans
      ((hb (node t) t).1.trans (Nat.add_le_add_right (hdeg _) 1))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_shared_cellular_generation
