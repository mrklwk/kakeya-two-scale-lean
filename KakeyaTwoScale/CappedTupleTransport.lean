module
public import KakeyaTwoScale.CappedIntervalCover
public import KakeyaTwoScale.CellularCylinderSplit
public import KakeyaTwoScale.FrozenFamilyAccounting

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem capped_cylinder_cover {n : ℕ} (b u x : EuclideanSpace ℝ (Fin n))
    {L δ : ℝ} (hδ : 0 < δ) (hL : δ ≤ L) (hx : x ∈ flatCylinder b u L δ) :
    ∃ color : Fin 3, ∃ a ∈ cappedStarts L δ color,
      x ∈ flatCylinder (b+a • u) u δ δ ∧ flatCylinder (b+a • u) u δ δ ⊆ flatCylinder b u L δ := by
  obtain ⟨t,ht0,htL,hti,hxt⟩ := hx
  obtain ⟨color,a,ha,hat,hta⟩ := cappedStarts_cover hδ hL ⟨ht0,htL⟩
  have hb := cappedStarts_bounds hδ hL color ha
  refine ⟨color,a,ha,?_,?_⟩
  · have he : (b+a • u)+(t-a) • u=b+t • u := by module
    exact ⟨t-a,by linarith,by linarith,by simpa only [he] using hti,by simpa only [he] using hxt⟩
  · rintro y ⟨s,hs0,hsδ,hsi,hys⟩
    have he : b+(a+s) • u=(b+a • u)+s • u := by module
    exact ⟨a+s,by linarith [hb.1],by linarith [hb.2],
      by simpa only [he] using hsi,by simpa only [he] using hys⟩

theorem capped_cylinders_disjoint {n : ℕ} (b u : EuclideanSpace ℝ (Fin n))
    {L δ : ℝ} (hδ : 0 < δ) (hu : ‖u‖=1) (color : Fin 3) :
    PairwiseDisjoint (↑(cappedStarts L δ color) : Set ℝ)
      (fun a => flatCylinder (b+a • u) u δ δ) := by
  intro a ha c hc hne
  have hd := cappedStarts_disjoint hδ color ha hc hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t,ht0,htδ,hti,_⟩ := hx
  obtain ⟨s,hs0,hsδ,hsi,_⟩ := hy
  have ht : inner ℝ u (x-(b+(a+t) • u))=0 := by
    simpa only [show b+(a+t) • u=(b+a • u)+t • u by module] using hti
  have hs : inner ℝ u (x-(b+(c+s) • u))=0 := by
    simpa only [show b+(c+s) • u=(b+c • u)+s • u by module] using hsi
  have he := cylinder_parameter_unique b u x hu ht hs
  apply Set.disjoint_left.mp hd (show a+t ∈ Ioo a (a+δ) by constructor <;> linarith)
  rw [he]
  constructor <;> linarith

/-- Construct disjoint exact-delta children with simultaneous actual nonlinear
retention. The three colors cover all incidences; selecting one joint color
costs at most 3^k. Each retained color separately respects every parent budget. -/
theorem capped_tuple_transport {n k : ℕ} {T C : Type*} [DecidableEq T] [DecidableEq C]
    (Y : Finset T) (cube : T → C) (cubes : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (b u : T → Fin k → EuclideanSpace ℝ (Fin n)) (L : T → Fin k → ℝ)
    {δ p : ℝ} (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hL : ∀ y ∈ Y, ∀ j, δ ≤ L y j) (hu : ∀ y ∈ Y, ∀ j, ‖u y j‖=1)
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩ flatCylinder (b y j) (u y j) (L y j) δ).Nonempty) :
    ∃ (color : Fin k → Fin 3) (Z : Finset T), Z ⊆ Y ∧
      tupleCubeMass Y cube cubes p / ((3^k:ℕ):ℝ) ≤ tupleCubeMass Z cube cubes p ∧
      ∀ y ∈ Z, ∀ j,
        PairwiseDisjoint (↑(cappedStarts (L y j) δ (color j)) : Set ℝ)
          (fun a => flatCylinder (b y j+a • u y j) (u y j) δ δ) ∧
        δ*((cappedStarts (L y j) δ (color j)).card:ℝ) ≤ L y j ∧
        ∃ a ∈ cappedStarts (L y j) δ (color j),
          (Q (cube y) ∩ flatCylinder (b y j+a • u y j) (u y j) δ δ).Nonempty ∧
          flatCylinder (b y j+a • u y j) (u y j) δ δ ⊆ flatCylinder (b y j) (u y j) (L y j) δ := by
  classical
  have hex : ∀ y, ∀ j : Fin k, ∃ c : Fin 3, ∃ a : ℝ, y ∈ Y →
      a ∈ cappedStarts (L y j) δ c ∧
      (Q (cube y) ∩ flatCylinder (b y j+a • u y j) (u y j) δ δ).Nonempty ∧
      flatCylinder (b y j+a • u y j) (u y j) δ δ ⊆ flatCylinder (b y j) (u y j) (L y j) δ := by
    intro y j
    by_cases hy : y ∈ Y
    · obtain ⟨x,hxQ,hx⟩ := hinc y hy j
      obtain ⟨c,a,ha,hxc,hsub⟩ := capped_cylinder_cover (b y j) (u y j) x hδ (hL y hy j) hx
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
    refine ⟨capped_cylinders_disjoint (b y j) (u y j) hδ (hu y hy j) (color j),
      cappedStarts_length_budget hδ (hL y hy j) (color j),start y j,?_⟩
    simpa only [hcolor] using hstart y j hy

end KakeyaTwoScale
#print axioms KakeyaTwoScale.capped_cylinder_cover
#print axioms KakeyaTwoScale.capped_cylinders_disjoint
#print axioms KakeyaTwoScale.capped_tuple_transport
