module
public import KakeyaTwoScale.GlobalCellularTupleTransport

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Deduplicated actual child starts, keeping the original parent identity. -/
def tupleChildStarts {T J : Type*} [DecidableEq T] [DecidableEq J]
    {k : ℕ} (Y : Finset T) (tube : T → Fin k → J) (start : T → Fin k → ℝ)
    (t : J) : Finset ℝ := by
  classical
  exact ((Y.product Finset.univ).filter (fun ij => tube ij.1 ij.2=t)).image
    (fun ij => start ij.1 ij.2)

theorem mem_tupleChildStarts {T J : Type*} [DecidableEq T] [DecidableEq J]
    {k : ℕ} (Y : Finset T) (tube : T → Fin k → J) (start : T → Fin k → ℝ)
    (t : J) (a : ℝ) :
    a ∈ tupleChildStarts Y tube start t ↔ ∃ y ∈ Y, ∃ j, tube y j=t ∧ start y j=a := by
  classical
  simp only [tupleChildStarts,Finset.mem_image,Finset.mem_filter,Prod.exists]
  aesop

/-- A root piece has a canonical cell, independent of its incidence witness. -/
def cellularChildCell {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (L a : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  connectedComponentIn (ambientPolynomialZeroSet P)ᶜ
    (b+((a+rootNext (cellularRoots P b u L) L a)/2) • u)

theorem cellularChildCell_eq {n : ℕ} {C : Type*} (P : MvPolynomial (Fin n) ℝ)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (q : C)
    (b u : EuclideanSpace ℝ (Fin n)) (L a δ : ℝ) (hδ : 0 < δ)
    (hlen : δ ≤ rootNext (cellularRoots P b u L) L a-a)
    (haxis : ∀ r ∈ Ioo a (rootNext (cellularRoots P b u L) L a),
      b+r • u ∈ geometricCubeCell P Q q) :
    cellularChildCell P b u L a = geometricCubeCell P Q q := by
  have hm := haxis ((a+rootNext (cellularRoots P b u L) L a)/2) ⟨by linarith,by linarith⟩
  exact (connectedComponentIn_eq hm).symm

/-- Deduplication preserves the full one-parent degree, axial-mass and
pairwise-disjointness budgets. The input is geometric root membership, not
an assumed numerical budget. -/
theorem tupleChildStarts_budget {n k : ℕ} {T J : Type*}
    [DecidableEq T] [DecidableEq J]
    (P : MvPolynomial (Fin n) ℝ) (Y : Finset T) (tube : T → Fin k → J)
    (start : T → Fin k → ℝ) (b u : J → EuclideanSpace ℝ (Fin n)) (L : J → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hu : ∀ t, ‖u t‖=1) (hL : ∀ t, δ ≤ L t)
    (hroot : ∀ y ∈ Y, ∀ j, start y j ∈ insert 0 (cellularRoots P (b (tube y j))
      (u (tube y j)) (L (tube y j)))) (t : J) :
    (tupleChildStarts Y tube start t).card ≤ P.totalDegree+1 ∧
    (tupleChildStarts Y tube start t).sum (fun a =>
      rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a-a) ≤ L t ∧
    PairwiseDisjoint (↑(tupleChildStarts Y tube start t) : Set ℝ)
      (fun a => flatCylinder (b t+a • u t) (u t)
        (rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a-a) δ) := by
  classical
  have hsub : tupleChildStarts Y tube start t ⊆ insert 0 (cellularRoots P (b t) (u t) (L t)) := by
    intro a ha
    obtain ⟨y,hy,j,hj,rfl⟩ := (mem_tupleChildStarts Y tube start t a).mp ha
    simpa only [hj] using hroot y hy j
  refine ⟨(Finset.card_le_card hsub).trans (cellular_gap_count P (b t) (u t) (L t)),?_,?_⟩
  · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
      (root_intervals_total_length _ _ (hδ.trans_le (hL t)) (cellularRoots_bounds P (b t) (u t) (L t)))
    intro a ha _
    have hal : a < L t := by
      rcases Finset.mem_insert.mp ha with rfl | har
      · exact hδ.trans_le (hL t)
      · exact (cellularRoots_bounds P (b t) (u t) (L t) a har).2
    exact sub_nonneg.mpr (rootNext_bounds _ _ _ hal).1.le
  · intro a ha c hc hne
    exact cellular_cylinders_disjoint P (b t) (u t) (L t) δ (hu t) (hsub ha) (hsub hc) hne

/-- Assigning a deduplicated family to its canonical cells partitions its
cardinality exactly. In particular repeated tuple witnesses do not inflate
cross-cell component counts. -/
theorem child_cell_card_partition {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (L : ℝ) (S : Finset ℝ) :
    (∑ G ∈ S.image (cellularChildCell P b u L),
      (S.filter fun a => cellularChildCell P b u L a=G).card) = S.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (fun a ha => Finset.mem_image_of_mem (cellularChildCell P b u L) ha)).symm

/-- Construct coherent finite child families from the original incidences.
All counts and lengths are on deduplicated starts, with canonical cell labels. -/
theorem shared_cellular_tuple_families {n k : ℕ} {T C J : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq J]
    (P : MvPolynomial (Fin n) ℝ) (Y : Finset T) (cube : T → C)
    (cubes : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (tube : T → Fin k → J) (b u : J → EuclideanSpace ℝ (Fin n)) (L : J → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hu : ∀ j, ‖u j‖=1) (hL : ∀ j, δ ≤ L j)
    (hY : ∀ y ∈ Y, cube y ∈ cubes)
    (hQ : ∀ q ∈ cubes, IsPreconnected (Q q))
    (hwall : ∀ q ∈ cubes, ∀ x ∈ Q q, x ∉ cthickening (2*δ) (ambientPolynomialZeroSet P))
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩ flatCylinder (b (tube y j)) (u (tube y j))
      (L (tube y j)) δ).Nonempty) :
    ∃ start : T → Fin k → ℝ,
      (∀ t, (tupleChildStarts Y tube start t).card ≤ P.totalDegree+1 ∧
        (tupleChildStarts Y tube start t).sum (fun a =>
          rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a-a) ≤ L t ∧
        PairwiseDisjoint (↑(tupleChildStarts Y tube start t) : Set ℝ)
          (fun a => flatCylinder (b t+a • u t) (u t)
            (rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a-a) δ)) ∧
      (∀ t, ∀ a ∈ tupleChildStarts Y tube start t,
        δ ≤ rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a-a ∧
        flatCylinder (b t+a • u t) (u t)
          (rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a-a) δ ⊆
          flatCylinder (b t) (u t) (L t) δ ∧
        ∀ r ∈ Ioo a (rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a),
          b t+r • u t ∈ cellularChildCell P (b t) (u t) (L t) a) ∧
      (∀ y ∈ Y, ∀ j, start y j ∈ tupleChildStarts Y tube start (tube y j) ∧
        cellularChildCell P (b (tube y j)) (u (tube y j)) (L (tube y j)) (start y j) =
          geometricCubeCell P Q (cube y) ∧
        (Q (cube y) ∩ flatCylinder (b (tube y j)+start y j • u (tube y j)) (u (tube y j))
          (rootNext (cellularRoots P (b (tube y j)) (u (tube y j)) (L (tube y j)))
            (L (tube y j)) (start y j)-start y j) δ).Nonempty) ∧
      ∀ p : ℝ, 0 < p →
        (∑ G ∈ cubes.image (geometricCubeCell P Q),
          tupleCubeMass (Y.filter fun y => geometricCubeCell P Q (cube y)=G) cube cubes p) =
        tupleCubeMass Y cube cubes p := by
  classical
  obtain ⟨start,hs,hmass⟩ := global_cellular_tuple_transport P Y cube cubes Q tube b u L δ
    hδ hu hL hY hQ hwall hinc
  refine ⟨start,?_,?_,?_,hmass⟩
  · intro t
    exact tupleChildStarts_budget P Y tube start b u L δ hδ hu hL
      (fun y hy j => (hs y hy j).1) t
  · intro t a ha
    obtain ⟨y,hy,j,hj,rfl⟩ := (mem_tupleChildStarts Y tube start t a).mp ha
    have hh := hs y hy j
    have he := cellularChildCell_eq P Q (cube y) _ _ _ _ δ hδ hh.2.1 hh.2.2.2.2
    rw [hj] at hh he
    exact ⟨hh.2.1,hh.2.2.1,fun r hr => he.symm ▸ hh.2.2.2.2 r hr⟩
  · intro y hy j
    have hh := hs y hy j
    exact ⟨(mem_tupleChildStarts Y tube start _ _).mpr ⟨y,hy,j,rfl,rfl⟩,
      cellularChildCell_eq P Q (cube y) _ _ _ _ δ hδ hh.2.1 hh.2.2.2.2,hh.2.2.2.1⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mem_tupleChildStarts
#print axioms KakeyaTwoScale.cellularChildCell_eq
#print axioms KakeyaTwoScale.tupleChildStarts_budget
#print axioms KakeyaTwoScale.child_cell_card_partition

#print axioms KakeyaTwoScale.shared_cellular_tuple_families
