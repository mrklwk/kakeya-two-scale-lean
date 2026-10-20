module
public import KakeyaTwoScale.PrescribedLengthTupleTransport

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Construct disjoint prescribed-length children while preserving the
original transverse width. The target length delta and width are independent.
One joint color retains at least 3^(-k) of the actual nonlinear tuple mass. -/
theorem family_prescribed_length_transport {n k : ℕ} {T C : Type*} [DecidableEq T] [DecidableEq C]
    (Y : Finset T) (cube : T → C) (cubes : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (b u : T → Fin k → EuclideanSpace ℝ (Fin n)) (L : T → Fin k → ℝ)
    (ell : Fin k → ℝ) {width p : ℝ} (hδ : ∀ j, 0 < ell j) (hp : 0 < p) (hp1 : p ≤ 1)
    (hL : ∀ y ∈ Y, ∀ j, ell j ≤ L y j) (hu : ∀ y ∈ Y, ∀ j, ‖u y j‖=1)
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩ flatCylinder (b y j) (u y j) (L y j) width).Nonempty) :
    ∃ (color : Fin k → Fin 3) (Z : Finset T), Z ⊆ Y ∧
      tupleCubeMass Y cube cubes p / ((3^k:ℕ):ℝ) ≤ tupleCubeMass Z cube cubes p ∧
      ∀ y ∈ Z, ∀ j,
        PairwiseDisjoint (↑(cappedStarts (L y j) (ell j) (color j)) : Set ℝ)
          (fun a => flatCylinder (b y j+a • u y j) (u y j) (ell j) width) ∧
        ell j*((cappedStarts (L y j) (ell j) (color j)).card:ℝ) ≤ L y j ∧
        ∃ a ∈ cappedStarts (L y j) (ell j) (color j),
          (Q (cube y) ∩ flatCylinder (b y j+a • u y j) (u y j) (ell j) width).Nonempty ∧
          flatCylinder (b y j+a • u y j) (u y j) (ell j) width ⊆ flatCylinder (b y j) (u y j) (L y j) width := by
  classical
  have hex : ∀ y, ∀ j : Fin k, ∃ c : Fin 3, ∃ a : ℝ, y ∈ Y →
      a ∈ cappedStarts (L y j) (ell j) c ∧
      (Q (cube y) ∩ flatCylinder (b y j+a • u y j) (u y j) (ell j) width).Nonempty ∧
      flatCylinder (b y j+a • u y j) (u y j) (ell j) width ⊆ flatCylinder (b y j) (u y j) (L y j) width := by
    intro y j
    by_cases hy : y ∈ Y
    · obtain ⟨x,hxQ,hx⟩ := hinc y hy j
      obtain ⟨c,a,ha,hxc,hsub⟩ := prescribed_length_cylinder_cover (b y j) (u y j) x (hδ j) (hL y hy j) hx
      exact ⟨c,a,fun _ => ⟨ha,⟨x,hxQ,hxc⟩,hsub⟩⟩
    · exact ⟨0,0,fun h => False.elim (hy h)⟩
  choose coloring start hstart using hex
  obtain ⟨color,_,hmass⟩ := exists_tuple_color_mass Y cube cubes Finset.univ
    Finset.univ_nonempty coloring (by simp) hp hp1
  let Z := Y.filter (fun y => coloring y=color)
  refine ⟨color,Z,Finset.filter_subset _ _,?_,?_⟩
  · simpa [Z] using hmass
  · intro y hy j
    obtain ⟨hy,hcolor⟩ := Finset.mem_filter.mp hy
    refine ⟨prescribed_length_cylinders_disjoint (b y j) (u y j) (hδ j) (hu y hy j) (color j),
      cappedStarts_length_budget (hδ j) (hL y hy j) (color j),start y j,?_⟩
    simpa only [hcolor] using hstart y j hy


end KakeyaTwoScale
#print axioms KakeyaTwoScale.family_prescribed_length_transport
