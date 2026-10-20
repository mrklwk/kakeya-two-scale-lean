module
public import KakeyaTwoScale.SharedCellularGeneration

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

structure CellularPhysicalFamily (n k : ℕ) (T O G : Type) where
  Piece : Type
  parent : T → Fin k → Piece
  node : Piece → G
  original : Piece → O
  base : Piece → EuclideanSpace ℝ (Fin n)
  axis : Piece → EuclideanSpace ℝ (Fin n)
  length : Piece → ℝ

namespace CellularPhysicalFamily
variable {n k : ℕ} {T C O G : Type}

def geometry (W : CellularPhysicalFamily n k T O G) (δ : ℝ) (t : W.Piece) :=
  flatCylinder (W.base t) (W.axis t) (W.length t) δ

def records (W : CellularPhysicalFamily n k T O G) (Y : Finset T) (j : Fin k) : Finset W.Piece := by
  classical
  exact Y.image (fun y => W.parent y j)

def Valid (W : CellularPhysicalFamily n k T O G) (Y : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (grain : C → G) (δ maxLength : ℝ) : Prop :=
  (∀ t, ‖W.axis t‖=1) ∧ (∀ t, δ ≤ W.length t ∧ W.length t ≤ maxLength) ∧
  (∀ y ∈ Y, ∀ j, W.original (W.parent y j)=tube y j) ∧
  (∀ y ∈ Y, ∀ j, W.node (W.parent y j)=grain (cube y)) ∧
  (∀ y ∈ Y, ∀ j, (Q (cube y) ∩ W.geometry δ (W.parent y j)).Nonempty) ∧
  (∀ j o, PairwiseDisjoint {t | t ∈ W.records Y j ∧ W.original t=o} (W.geometry δ))

/-- An actual simultaneous polynomial-cut successor, packaged so it can be
iterated. Unused records are assigned length delta; every represented record
retains its actual root-gap length. -/
theorem exists_cut_successor [DecidableEq T] [DecidableEq C]
    (W : CellularPhysicalFamily n k T O G)
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (cubes : Finset C)
    (grain nextGrain : C → G) {s D : ℕ}
    (p : G → Fin s → MvPolynomial (Fin n) ℝ)
    (owner : C → Fin s → Bool) (merge : G × (Fin s → Bool) → G)
    {δ maxLength : ℝ} (hδ : 0 < δ) (hmax : δ ≤ maxLength)
    (hv : W.Valid Y cube tube Q grain δ maxLength)
    (hY : ∀ y ∈ Y, cube y ∈ cubes)
    (hroute : ∀ q ∈ cubes, nextGrain q=merge (grain q,owner q))
    (hdeg : ∀ g, (∏ i, p g i).totalDegree ≤ D)
    (hQ : ∀ q ∈ cubes, IsPreconnected (Q q))
    (hcell : ∀ q ∈ cubes, Q q ⊆ polynomialSignCell (p (grain q)) (owner q))
    (hwall : ∀ q ∈ cubes, ∀ x ∈ Q q,
      x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ i, p (grain q) i))) :
    ∃ V : CellularPhysicalFamily n k T O G,
      V.Valid Y cube tube Q nextGrain δ maxLength ∧
      (∀ y ∈ Y, ∀ j, V.geometry δ (V.parent y j) ⊆ W.geometry δ (W.parent y j)) ∧
      (∀ y ∈ Y, ∀ j, V.axis (V.parent y j)=W.axis (W.parent y j)) ∧
      (∀ j, ((V.records Y j).card:ℝ) ≤ (D+1:ℕ)*((W.records Y j).card:ℝ)) := by
  classical
  obtain ⟨start,origin,hi,hd,hbudget,hcount⟩ := exists_shared_cellular_generation
    p Y cube cubes Q grain owner W.parent W.node W.original W.base W.axis W.length δ D
    hδ hv.1 (fun t => (hv.2.1 t).1) hdeg hY hv.2.2.2.1 hQ hcell hwall
    hv.2.2.2.2.1 hv.2.2.2.2.2
  let rawLen := fun t : W.Piece×ℝ =>
    rootNext (cellularRoots (∏ i, p (W.node t.1) i) (W.base t.1) (W.axis t.1) (W.length t.1))
      (W.length t.1) t.2-t.2
  let active : Finset (Fin k × (W.Piece×ℝ)) :=
    (Y.product Finset.univ).image (fun yj => (yj.2,(W.parent yj.1 yj.2,start yj.1 yj.2)))
  have ha y (hy : y ∈ Y) j : (j,(W.parent y j,start y j)) ∈ active :=
    Finset.mem_image.mpr ⟨(y,j),Finset.mem_product.mpr ⟨hy,Finset.mem_univ j⟩,rfl⟩
  have hlen y (hy : y ∈ Y) j : rawLen (W.parent y j,start y j) ≤ W.length (W.parent y j) := by
    have hmem := (mem_tupleChildStarts Y W.parent start (W.parent y j) (start y j)).mpr ⟨y,hy,j,rfl,rfl⟩
    have hnonneg : ∀ a ∈ tupleChildStarts Y W.parent start (W.parent y j),
        0 ≤ rawLen (W.parent y j,a) := by
      intro a ha
      obtain ⟨z,hz,l,he,rfl⟩ := (mem_tupleChildStarts _ _ _ _ _).mp ha
      have hh := (hi z hz l).2.2.1
      rw [he] at hh
      exact hδ.le.trans hh
    exact (Finset.single_le_sum hnonneg hmem).trans (hbudget _).2
  let V : CellularPhysicalFamily n k T O G :=
    { Piece := Fin k × (W.Piece×ℝ)
      parent := fun y j => (j,(W.parent y j,start y j))
      node := fun t => merge (origin t.1 t.2)
      original := fun t => W.original t.2.1
      base := fun t => W.base t.2.1+t.2.2 • W.axis t.2.1
      axis := fun t => W.axis t.2.1
      length := fun t => if t ∈ active then rawLen t.2 else δ }
  have hgeom y (hy : y ∈ Y) j : V.geometry δ (V.parent y j)=
      flatCylinder (W.base (W.parent y j)+start y j • W.axis (W.parent y j))
        (W.axis (W.parent y j)) (rawLen (W.parent y j,start y j)) δ := by
    simp only [geometry,V,ha y hy j,ite_true]
  refine ⟨V,?_,?_,fun y hy j => rfl,?_⟩
  · refine ⟨fun t => hv.1 _,?_,fun y hy j => hv.2.2.1 y hy j,?_,?_,?_⟩
    · intro t
      change δ ≤ (if t ∈ active then rawLen t.2 else δ) ∧
        (if t ∈ active then rawLen t.2 else δ) ≤ maxLength
      by_cases ht : t ∈ active
      · obtain ⟨⟨y,j⟩,hy,rfl⟩ := Finset.mem_image.mp ht
        have hyY := (Finset.mem_product.mp hy).1
        simp only [ha y hyY j,ite_true]
        exact ⟨(hi y hyY j).2.2.1,(hlen y hyY j).trans (hv.2.1 _).2⟩
      · simp only [ht,ite_false]
        exact ⟨le_refl _,hmax⟩
    · intro y hy j
      change merge (origin j (W.parent y j,start y j))=nextGrain (cube y)
      rw [(hi y hy j).1,← hroute _ (hY y hy)]
    · intro y hy j
      rw [hgeom y hy j]
      exact (hi y hy j).2.1
    · intro j o t ht v hh htv
      have hti : t ∈ Y.image (fun y => V.parent y j) := by
        simpa only [records,Finset.mem_image] using ht.1
      have hvi : v ∈ Y.image (fun y => V.parent y j) := by
        simpa only [records,Finset.mem_image] using hh.1
      obtain ⟨y,hy,hty⟩ := Finset.mem_image.mp hti
      obtain ⟨z,hz,hvz⟩ := Finset.mem_image.mp hvi
      have hpair : (W.parent y j,start y j) ≠ (W.parent z j,start z j) := by
        intro he
        exact htv (hty.symm.trans ((congrArg (fun a => (j,a)) he).trans hvz))
      have hoy : W.original (W.parent y j)=o := by
        change V.original (V.parent y j)=o
        rw [hty]
        exact ht.2
      have hoz : W.original (W.parent z j)=o := by
        change V.original (V.parent z j)=o
        rw [hvz]
        exact hh.2
      have h := hd j o ⟨Finset.mem_image.mpr ⟨y,hy,rfl⟩,hoy⟩
        ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,hoz⟩ hpair
      change Disjoint (V.geometry δ t) (V.geometry δ v)
      rw [← hty,← hvz,hgeom y hy j,hgeom z hz j]
      exact h
  · intro y hy j
    rw [hgeom y hy j]
    exact (hi y hy j).2.2.2
  · intro j
    have he : V.records Y j=(Y.image (fun y => (W.parent y j,start y j))).image (fun a => (j,a)) := by
      simp only [records,V,Finset.image_image,Function.comp_def]
      ext t
      simp only [Finset.mem_image]
    rw [he]
    have hh : (((Y.image (fun y => (W.parent y j,start y j))).image (fun a => (j,a))).card:ℝ) ≤
        ((Y.image (fun y => (W.parent y j,start y j))).card:ℝ) := by
      exact_mod_cast Finset.card_image_le
    exact hh.trans (hcount j)

end CellularPhysicalFamily
end KakeyaTwoScale
#print axioms KakeyaTwoScale.CellularPhysicalFamily.exists_cut_successor
