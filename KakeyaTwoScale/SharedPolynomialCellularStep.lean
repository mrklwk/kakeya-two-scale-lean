module
public import KakeyaTwoScale.SharedCellularFamilies
public import KakeyaTwoScale.SharedChildInvariants
public import KakeyaTwoScale.PartitionComponentMass

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- An actual complementary component containing a cube belongs to its
supplied sign cell. Sign cells themselves need not be connected. -/
theorem geometricCubeCell_subset_signCell {n s : ℕ} {C : Type*}
    (p : Fin s → MvPolynomial (Fin n) ℝ)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (q : C) (owner : Fin s → Bool)
    (hQ : IsPreconnected (Q q)) (hne : (Q q).Nonempty)
    (hcell : Q q ⊆ polynomialSignCell p owner) :
    geometricCubeCell (∏ i, p i) Q q ⊆ polynomialSignCell p owner := by
  classical
  let P := ∏ i, p i
  have hav : ∀ x ∈ Q q, x ∉ ambientPolynomialZeroSet P := by
    intro x hx hz
    have hi := hcell hx
    have hprod : MvPolynomial.eval (fun i => x i) P ≠ 0 := by
      rw [show P = ∏ i, p i from rfl, map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      have hh := hi i
      cases h : owner i <;> simp [polynomialSignSide,h] at hh
      · exact ne_of_lt hh
      · exact ne_of_gt hh
    exact hprod hz
  obtain ⟨x,hx⟩ := hne
  have he := geometricCubeCell_eq P Q q hQ hav hx
  rw [← he]
  let U := (ambientPolynomialZeroSet P)ᶜ
  have hxc : x ∈ connectedComponentIn U x := mem_connectedComponentIn (hav x hx)
  obtain ⟨v,hv⟩ := preconnected_subset_polynomialSignCell p (connectedComponentIn U x)
    isPreconnected_connectedComponentIn ⟨x,hxc⟩
    (fun y hy => connectedComponentIn_subset U x hy)
  have hvowner : v=owner := by
    by_contra hn
    exact Set.disjoint_left.mp (polynomialSignCells_disjoint p hn) (hv hxc) (hcell hx)
  simpa only [hvowner] using hv

/-- Actual root-gap children acquire consistent finite sign-cell origins,
and preserve disjointness across all represented parents of an original tube.
Records are pairs (old parent, start); tuple occurrences never copy them. -/
theorem exists_shared_polynomial_cellular_step {n k s : ℕ} {T C J O : Type}
    [DecidableEq T] [DecidableEq C] [DecidableEq J]
    (p : Fin s → MvPolynomial (Fin n) ℝ)
    (Y : Finset T) (cube : T → C) (cubes : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (owner : C → Fin s → Bool)
    (parent : T → Fin k → J) (original : J → O)
    (b u : J → EuclideanSpace ℝ (Fin n)) (L : J → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hu : ∀ t, ‖u t‖=1) (hL : ∀ t, δ ≤ L t)
    (hY : ∀ y ∈ Y, cube y ∈ cubes)
    (hQ : ∀ q ∈ cubes, IsPreconnected (Q q))
    (hcell : ∀ q ∈ cubes, Q q ⊆ polynomialSignCell p (owner q))
    (hwall : ∀ q ∈ cubes, ∀ x ∈ Q q,
      x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ i, p i)))
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩ flatCylinder (b (parent y j))
      (u (parent y j)) (L (parent y j)) δ).Nonempty)
    (hdis : ∀ j o, PairwiseDisjoint
      {t | t ∈ Y.image (fun y => parent y j) ∧ original t=o}
      (fun t => flatCylinder (b t) (u t) (L t) δ)) :
    let P := ∏ i, p i
    let geom := fun t : J×ℝ => flatCylinder (b t.1+t.2 • u t.1) (u t.1)
      (rootNext (cellularRoots P (b t.1) (u t.1) (L t.1)) (L t.1) t.2-t.2) δ
    ∃ (start : T → Fin k → ℝ) (origin : Fin k → J×ℝ → Fin s → Bool),
      (∀ t, (tupleChildStarts Y parent start t).card ≤ P.totalDegree+1 ∧
        (tupleChildStarts Y parent start t).sum (fun a =>
          rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a-a) ≤ L t) ∧
      (∀ y ∈ Y, ∀ j,
        origin j (parent y j,start y j)=owner (cube y) ∧
        (Q (cube y) ∩ geom (parent y j,start y j)).Nonempty ∧
        δ ≤ rootNext (cellularRoots P (b (parent y j)) (u (parent y j)) (L (parent y j)))
          (L (parent y j)) (start y j)-start y j ∧
        geom (parent y j,start y j) ⊆ flatCylinder (b (parent y j))
          (u (parent y j)) (L (parent y j)) δ) ∧
      (∀ j o, PairwiseDisjoint
        {t | t ∈ Y.image (fun y => (parent y j,start y j)) ∧ original t.1=o} geom) ∧
      (∀ j, ((Y.image (fun y => (parent y j,start y j))).card:ℝ) ≤
        (P.totalDegree+1:ℕ) * ((Y.image (fun y => parent y j)).card:ℝ)) := by
  classical
  dsimp only
  let P := ∏ i, p i
  let geom := fun t : J×ℝ => flatCylinder (b t.1+t.2 • u t.1) (u t.1)
    (rootNext (cellularRoots P (b t.1) (u t.1) (L t.1)) (L t.1) t.2-t.2) δ
  obtain ⟨start,hbudget,hpieces,hinc',_⟩ := shared_cellular_tuple_families
    P Y cube cubes Q parent b u L δ hδ hu hL hY hQ hwall hinc
  have hconsistent j y (hy : y ∈ Y) z (hz : z ∈ Y)
      (he : (parent y j,start y j)=(parent z j,start z j)) : owner (cube y)=owner (cube z) := by
    have hp : parent y j=parent z j := congrArg Prod.fst he
    have hs : start y j=start z j := congrArg Prod.snd he
    have hc : geometricCubeCell P Q (cube y)=geometricCubeCell P Q (cube z) := by
      rw [← (hinc' y hy j).2.1,← (hinc' z hz j).2.1,hp,hs]
    have hsuby := geometricCubeCell_subset_signCell p Q (cube y) (owner (cube y))
      (hQ _ (hY y hy)) ((hinc y hy j).mono fun _ h => h.1) (hcell _ (hY y hy))
    have hsubz := geometricCubeCell_subset_signCell p Q (cube z) (owner (cube z))
      (hQ _ (hY z hz)) ((hinc z hz j).mono fun _ h => h.1) (hcell _ (hY z hz))
    have hlen := (hpieces _ _ (hinc' y hy j).1).1
    let a := start y j
    let e := rootNext (cellularRoots P (b (parent y j)) (u (parent y j)) (L (parent y j))) (L (parent y j)) a
    have hm := (hpieces _ _ (hinc' y hy j).1).2.2 ((a+e)/2)
      (show (a+e)/2 ∈ Ioo a e from ⟨by dsimp [a,e]; linarith,by dsimp [a,e]; linarith⟩)
    rw [(hinc' y hy j).2.1] at hm
    by_contra hn
    exact Set.disjoint_left.mp (polynomialSignCells_disjoint p hn) (hsuby hm) (hsubz (hc ▸ hm))
  have hex j := exists_record_label Y (fun y => (parent y j,start y j))
    (fun y => owner (cube y)) (fun _ => false) (hconsistent j)
  choose origin ho using hex
  refine ⟨start,origin,fun t => ⟨(hbudget t).1,(hbudget t).2.1⟩,?_,?_,?_⟩
  · intro y hy j
    exact ⟨ho j y hy,(hinc' y hy j).2.2,(hpieces _ _ (hinc' y hy j).1).1,
      (hpieces _ _ (hinc' y hy j).1).2.1⟩
  · intro j o t ht v hv htv
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp ht.1
    obtain ⟨z,hz,hf⟩ := Finset.mem_image.mp hv.1
    subst t; subst v
    by_cases he : parent y j=parent z j
    · have hs : start y j ≠ start z j := fun hs => htv (Prod.ext he hs)
      have hd := (hbudget (parent y j)).2.2 (hinc' y hy j).1
        (by simpa only [he, Finset.mem_coe] using (hinc' z hz j).1) hs
      simpa only [he] using hd
    · exact (hdis j o ⟨Finset.mem_image.mpr ⟨y,hy,rfl⟩,ht.2⟩
        ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,hv.2⟩ he).mono
        (hpieces _ _ (hinc' y hy j).1).2.1 (hpieces _ _ (hinc' z hz j).1).2.1

  · intro j
    exact variable_child_record_bound Y Y (fun y => parent y j) (fun y => start y j)
      (tupleChildStarts Y parent start) (Finset.Subset.refl Y)
      (fun y hy => (hinc' y hy j).1)
      (fun t _ => by exact_mod_cast (hbudget t).1)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.geometricCubeCell_subset_signCell
#print axioms KakeyaTwoScale.exists_shared_polynomial_cellular_step
