module
public import KakeyaTwoScale.EuclideanTubes
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finset.Sort

@[expose] public section

open Metric Set
noncomputable section
namespace KakeyaTwoScale

/-- An off-wall point and any point within the wall radius lie in the same
component of the complement. This uses the actual open ball as a connector. -/
theorem offwall_same_component {n : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin n))) {δ : ℝ} {x a : EuclideanSpace ℝ (Fin n)}
    (hδ : 0 < δ) (hx : x ∉ cthickening δ Z) (ha : dist a x < δ) :
    connectedComponentIn Zᶜ a = connectedComponentIn Zᶜ x := by
  have hball : ball x δ ⊆ Zᶜ := by
    intro y hy hyZ
    exact hx (mem_cthickening_of_dist_le x y δ Z hyZ (by
      simpa [dist_comm] using (mem_ball.mp hy).le))
  symm
  apply connectedComponentIn_eq
  exact (convex_ball x δ).isPreconnected.subset_connectedComponentIn
    (mem_ball_self hδ) hball (mem_ball.mpr ha)

/-- Every capsule point outside the closed wall has a genuine axis parameter
in [0,1] lying outside Z and representing the same complementary cell. -/
theorem capsule_offwall_axis_component {n : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin n))) (b u x : EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (hx : x ∈ euclideanTube b u δ)
    (hwall : x ∉ cthickening δ Z) :
    ∃ t ∈ Icc (0:ℝ) 1, b+t • u ∉ Z ∧
      connectedComponentIn Zᶜ x = connectedComponentIn Zᶜ (b+t • u) := by
  obtain ⟨t,ht,hxt⟩ := hx
  refine ⟨t,ht,?_,?_⟩
  · intro ha
    exact hwall (mem_cthickening_of_dist_le x (b+t • u) δ Z ha hxt.le)
  · exact (offwall_same_component Z hδ hwall (by simpa [dist_comm] using hxt)).symm

/-- The degenerate affine-restriction case is empty outside the wall; no
nonzero-polynomial hypothesis can simply be omitted in a crossing argument. -/
theorem capsule_offwall_empty_of_axis_subset {n : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin n))) (b u : EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (haxis : ∀ t ∈ Icc (0:ℝ) 1, b+t • u ∈ Z) :
    euclideanTube b u δ \ cthickening δ Z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x ⟨hx,hw⟩
  obtain ⟨t,ht,ha,_⟩ := capsule_offwall_axis_component Z b u x hδ hx hw
  exact ha (haxis t ht)

/-- Distinct cells along a continuous affine axis force a root strictly between
their parameters. No partitioning theorem is assumed in this separation step. -/
theorem axis_distinct_components_force_root {n : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin n))) (b u : EuclideanSpace ℝ (Fin n))
    (P : Polynomial ℝ) (hP : ∀ t, P.eval t=0 ↔ b+t • u ∈ Z)
    {a c : ℝ} (hac : a < c) (ha : b+a • u ∉ Z) (hc : b+c • u ∉ Z)
    (hne : connectedComponentIn Zᶜ (b+a • u) ≠ connectedComponentIn Zᶜ (b+c • u)) :
    ∃ t ∈ Ioo a c, P.IsRoot t := by
  by_contra! hroot
  have hz : (fun t : ℝ => b+t • u) '' Icc a c ⊆ Zᶜ := by
    rintro y ⟨t,ht,rfl⟩ hy
    by_cases hat : a=t
    · subst t; exact ha hy
    by_cases htc : t=c
    · subst t; exact hc hy
    exact hroot t ⟨lt_of_le_of_ne ht.1 hat,lt_of_le_of_ne ht.2 htc⟩ ((hP t).mpr hy)
  have hconn : IsPreconnected ((fun t : ℝ => b+t • u) '' Icc a c) :=
    isPreconnected_Icc.image _ (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  have ham : b+a • u ∈ (fun t : ℝ => b+t • u) '' Icc a c :=
    ⟨a,⟨le_rfl,hac.le⟩,rfl⟩
  have hcm : b+c • u ∈ (fun t : ℝ => b+t • u) '' Icc a c :=
    ⟨c,⟨hac.le,le_rfl⟩,rfl⟩
  exact hne (connectedComponentIn_eq (hconn.subset_connectedComponentIn ham hz hcm))

/-- The finite induction/counting core of the polynomial wall crossing bound:
an increasing list of m+1 axis points in different complementary cells forces
m distinct roots, hence m+1 ≤ degree(P)+1. -/
theorem ordered_axis_cells_le_degree {n m : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin n))) (b u : EuclideanSpace ℝ (Fin n))
    (P : Polynomial ℝ) (hP0 : P ≠ 0)
    (hP : ∀ t, P.eval t=0 ↔ b+t • u ∈ Z)
    (t : Fin (m+1) → ℝ) (ht : StrictMono t)
    (hout : ∀ i, b+t i • u ∉ Z)
    (hcells : Function.Injective (fun i => connectedComponentIn Zᶜ (b+t i • u))) :
    m+1 ≤ P.natDegree+1 := by
  classical
  have hgap : ∀ i : Fin m, ∃ r ∈ Ioo (t i.castSucc) (t i.succ), P.IsRoot r := by
    intro i
    apply axis_distinct_components_force_root Z b u P hP
      (ht (by simp [Fin.lt_def])) (hout _) (hout _)
    intro he
    have hh := hcells he
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_castSucc,Fin.val_succ] at hh'
    omega
  choose root hroot using hgap
  have hrootinj : Function.Injective root := by
    intro i j he
    by_contra hne
    wlog hij : i < j generalizing i j
    · exact this he.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hij) (Ne.symm hne))
    have hindices : i.succ ≤ j.castSucc := by
      simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]
      exact Nat.succ_le_of_lt hij
    have horder := ht.monotone hindices
    have hi := (hroot i).1.2
    have hj := (hroot j).1.1
    rw [he] at hi
    linarith
  have hcard : (Finset.univ.image root).card ≤ P.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    change x ∈ Finset.univ.image root at hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact (Polynomial.mem_roots hP0).mpr (hroot i).2
  rw [Finset.card_image_of_injective _ hrootinj] at hcard
  simpa using Nat.succ_le_succ hcard

/-- Unordered finite collections of axis parameters satisfy the same crossing
bound. Ordering is constructed internally by the finite order embedding. -/
theorem finite_axis_cells_le_degree {n : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin n))) (b u : EuclideanSpace ℝ (Fin n))
    (P : Polynomial ℝ) (hP0 : P ≠ 0)
    (hP : ∀ t, P.eval t=0 ↔ b+t • u ∈ Z)
    (A : Finset ℝ) (hout : ∀ t ∈ A, b+t • u ∉ Z)
    (hcells : Set.InjOn (fun t => connectedComponentIn Zᶜ (b+t • u)) (A : Set ℝ)) :
    A.card ≤ P.natDegree+1 := by
  classical
  cases hcard : A.card with
  | zero => omega
  | succ m =>
    let t := A.orderEmbOfFin hcard
    have ht : StrictMono t := t.strictMono
    have hm : ∀ i, t i ∈ A := fun i => A.orderEmbOfFin_mem hcard i
    exact ordered_axis_cells_le_degree Z b u P hP0 hP t ht
      (fun i => hout _ (hm i))
      (fun i j he => t.injective (hcells (hm i) (hm j) he))

/-- Full finite off-wall capsule crossing, stated first for an exact univariate
restriction. Representatives and their sorting are constructed in the proof. -/
theorem finite_capsule_cells_le_restriction_degree {n : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin n))) (b u : EuclideanSpace ℝ (Fin n))
    (P : Polynomial ℝ) (hP0 : P ≠ 0)
    (hP : ∀ t, P.eval t=0 ↔ b+t • u ∈ Z)
    {δ : ℝ} (hδ : 0 < δ) (cells : Finset (Set (EuclideanSpace ℝ (Fin n))))
    (hmeet : ∀ S ∈ cells, ∃ x ∈ euclideanTube b u δ,
      x ∉ cthickening δ Z ∧ connectedComponentIn Zᶜ x=S) :
    cells.card ≤ P.natDegree+1 := by
  classical
  have hrep : ∀ S : cells, ∃ t : ℝ, b+t • u ∉ Z ∧ connectedComponentIn Zᶜ (b+t • u)=S.val := by
    intro S
    obtain ⟨x,hx,hw,hS⟩ := hmeet S S.prop
    obtain ⟨t,_,ht,hcomp⟩ := capsule_offwall_axis_component Z b u x hδ hx hw
    exact ⟨t,ht,hcomp.symm.trans hS⟩
  choose t hout hcomp using hrep
  have htinj : Function.Injective t := by
    intro S T he
    apply Subtype.ext
    rw [← hcomp S, ← hcomp T,he]
  let A := Finset.univ.image t
  have hAout : ∀ a ∈ A, b+a • u ∉ Z := by
    intro a ha
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp ha
    exact hout S
  have hAinj : Set.InjOn (fun a => connectedComponentIn Zᶜ (b+a • u)) (A : Set ℝ) := by
    intro a ha c hc he
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨T,_,rfl⟩ := Finset.mem_image.mp hc
    have hST : S=T := Subtype.ext (by simpa only [hcomp] using he)
    rw [hST]
  have hbound := finite_axis_cells_le_degree Z b u P hP0 hP A hAout hAinj
  simpa only [A,Finset.card_image_of_injective _ htinj,Finset.card_univ,Fintype.card_coe] using hbound

end KakeyaTwoScale
#print axioms KakeyaTwoScale.offwall_same_component
#print axioms KakeyaTwoScale.capsule_offwall_axis_component
#print axioms KakeyaTwoScale.capsule_offwall_empty_of_axis_subset

#print axioms KakeyaTwoScale.axis_distinct_components_force_root

#print axioms KakeyaTwoScale.ordered_axis_cells_le_degree

#print axioms KakeyaTwoScale.finite_axis_cells_le_degree
#print axioms KakeyaTwoScale.finite_capsule_cells_le_restriction_degree
