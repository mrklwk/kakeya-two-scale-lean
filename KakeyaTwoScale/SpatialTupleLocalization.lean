module
public import KakeyaTwoScale.NonlinearTupleSelection
public import KakeyaTwoScale.LocalizedAncestorCylinder
public import KakeyaTwoScale.NestedGrid
public import KakeyaTwoScale.BrushGeometry

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def latticeCenter {n : ℕ} (r : ℝ) (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => r*(z i:ℝ))

def latticeColor {n M : ℕ} (hM : 0 < M) (z : Fin n → ℤ) : Fin n → Fin M :=
  fun i => ⟨(z i % (M:ℤ)).toNat,by
    have h0 := Int.emod_nonneg (z i) (show (M:ℤ) ≠ 0 by exact_mod_cast hM.ne')
    have h1 := Int.emod_lt_of_pos (z i) (show (0:ℤ) < M by exact_mod_cast hM)
    omega⟩

theorem rounded_center_dist {n : ℕ} {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) :
    dist x (latticeCenter r (gridIndex r (WithLp.ofLp x))) ≤ (n+1:ℝ)*r := by
  have hs := gridCell_dist_le hr.le (mem_own_gridCell hr (WithLp.ofLp x))
    (gridRound_mem hr (WithLp.ofLp x))
  have hh := euclidean_dist_le_sqrt_mul_sup (WithLp.ofLp x) (gridRound r (WithLp.ofLp x))
  have hroot : Real.sqrt (n:ℝ) ≤ n+1 := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
    nlinarith [Real.sqrt_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  exact (hh.trans (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _))).trans
    (mul_le_mul_of_nonneg_right hroot hr.le)

theorem lattice_color_separation {n M : ℕ} (hM : 0 < M) {r : ℝ} (hr : 0 ≤ r)
    {z w : Fin n → ℤ} (hne : z ≠ w) (hc : latticeColor hM z=latticeColor hM w) :
    (M:ℝ)*r ≤ dist (latticeCenter r z) (latticeCenter r w) := by
  classical
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
  have hi' := congrArg (fun c => (c i).val) hc
  have h0 := Int.emod_nonneg (z i) (show (M:ℤ) ≠ 0 by exact_mod_cast hM.ne')
  have h1 := Int.emod_nonneg (w i) (show (M:ℤ) ≠ 0 by exact_mod_cast hM.ne')
  have he : z i % (M:ℤ)=w i % (M:ℤ) := by
    change (z i % (M:ℤ)).toNat=(w i % (M:ℤ)).toNat at hi'
    omega
  have habs := Int.natAbs_le_of_dvd_ne_zero (Int.modEq_iff_dvd.mp he.symm) (sub_ne_zero.mpr hi)
  have hh : (M:ℝ) ≤ |(z i:ℝ)-(w i:ℝ)| := by
    have hh : (M:ℝ) ≤ ((z i-w i).natAbs:ℝ) := by exact_mod_cast habs
    simpa only [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub] using hh
  have hcoord := PiLp.norm_apply_le (latticeCenter r z-latticeCenter r w) i
  have hd : r*|(z i:ℝ)-(w i:ℝ)| ≤ dist (latticeCenter r z) (latticeCenter r w) := by
    simpa [latticeCenter,dist_eq_norm,Real.norm_eq_abs,← mul_sub,abs_mul,abs_of_nonneg hr] using hcoord
  nlinarith

/-- All full-width cylinders meeting one supplied cube fit in one constructed
ball. The center depends only on the cube, and the whole cube fits as well. -/
theorem cube_and_cylinders_in_grid_ball {n : ℕ} {r δ : ℝ} {A : ℕ}
    (hr : 0 < r) (hδ : δ ≤ r) (Q : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) (hQ : ∀ x ∈ Q, dist x c ≤ (A:ℝ)*r) :
    Q ⊆ ball (latticeCenter r (gridIndex r (WithLp.ofLp c))) ((A+n+5:ℝ)*r) ∧
    ∀ b u : EuclideanSpace ℝ (Fin n), ∀ L : ℝ, ‖u‖=1 → L ≤ 2*r →
      (Q ∩ flatCylinder b u L δ).Nonempty →
      flatCylinder b u L δ ⊆
        ball (latticeCenter r (gridIndex r (WithLp.ofLp c))) ((A+n+5:ℝ)*r) := by
  have hc := rounded_center_dist hr c
  constructor
  · intro x hx
    have ht := dist_triangle x c (latticeCenter r (gridIndex r (WithLp.ofLp c)))
    have hxc := hQ x hx
    change dist x _ < _
    nlinarith
  · intro b u L hu hL hi x hx
    obtain ⟨y,hyQ,hyT⟩ := hi
    have hxy := flatCylinder_pair_dist_lt b u x y L δ hu hx hyT
    have hyc := hQ y hyQ
    have ht := dist_triangle x y c
    have ht' := dist_triangle x c (latticeCenter r (gridIndex r (WithLp.ofLp c)))
    change dist x _ < _
    nlinarith

/-- A finite, dimension-dependent residue coloring gives disjoint open balls
for distinct centers of the same color. -/
theorem same_color_grid_balls_disjoint {n A : ℕ} {r : ℝ} (hr : 0 < r)
    (color : Fin n → Fin (2*(A+n+5)+1)) :
    PairwiseDisjoint {z : Fin n → ℤ | latticeColor (by omega : 0 < 2*(A+n+5)+1) z=color}
      (fun z => ball (latticeCenter r z) ((A+n+5:ℝ)*r)) := by
  intro z hz w hw hne
  apply ball_disjoint_ball
  have hh := lattice_color_separation (by omega : 0 < 2*(A+n+5)+1) hr.le hne (hz.trans hw.symm)
  push_cast at hh
  nlinarith

/-- A single color retains full CURRENT cube fibers, with an explicit
constant loss, and realizes all selected incidences in common disjoint balls. -/
theorem exists_spatial_tuple_localization {n k A : ℕ} {T C : Type*}
    [DecidableEq T] [DecidableEq C]
    (Y : Finset T) (cube : T → C) (cubes : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (center : C → EuclideanSpace ℝ (Fin n))
    (b u : T → Fin k → EuclideanSpace ℝ (Fin n)) (L : T → Fin k → ℝ)
    {δ r p : ℝ} (hr : 0 < r) (hδr : δ ≤ r)
    (hQ : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*r)
    (hY : ∀ y ∈ Y, cube y ∈ cubes)
    (hu : ∀ y ∈ Y, ∀ j, ‖u y j‖=1)
    (hL : ∀ y ∈ Y, ∀ j, L y j ≤ 2*r)
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩ flatCylinder (b y j) (u y j) (L y j) δ).Nonempty)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ (color : Fin n → Fin (2*(A+n+5)+1)) (Z : Finset T),
      Z = Y.filter (fun y => latticeColor (by omega : 0 < 2*(A+n+5)+1)
        (gridIndex r (WithLp.ofLp (center (cube y))))=color) ∧ Z ⊆ Y ∧
      tupleCubeMass Y cube cubes p / (((2*(A+n+5)+1)^n:ℕ):ℝ) ≤ tupleCubeMass Z cube cubes p ∧
      PairwiseDisjoint (↑(Z.image (fun y => gridIndex r (WithLp.ofLp (center (cube y))))) : Set (Fin n → ℤ))
        (fun z => ball (latticeCenter r z) ((A+n+5:ℝ)*r)) ∧
      (∀ y ∈ Z, Q (cube y) ⊆ ball
        (latticeCenter r (gridIndex r (WithLp.ofLp (center (cube y))))) ((A+n+5:ℝ)*r) ∧
        ∀ j, flatCylinder (b y j) (u y j) (L y j) δ ⊆ ball
          (latticeCenter r (gridIndex r (WithLp.ofLp (center (cube y))))) ((A+n+5:ℝ)*r)) ∧
      (∑ z ∈ cubes.image (fun q => gridIndex r (WithLp.ofLp (center q))),
        tupleCubeMass (Z.filter (fun y => gridIndex r (WithLp.ofLp (center (cube y)))=z)) cube cubes p) =
          tupleCubeMass Z cube cubes p := by
  classical
  let label (q : C) := gridIndex r (WithLp.ofLp (center q))
  let coloring (y : T) := latticeColor (by omega : 0 < 2*(A+n+5)+1) (label (cube y))
  obtain ⟨color,_,hmass⟩ := exists_tuple_color_mass Y cube cubes Finset.univ
    Finset.univ_nonempty coloring (by simp) hp hp1
  let Z := Y.filter (fun y => coloring y=color)
  refine ⟨color,Z,rfl,Finset.filter_subset _ _,?_,?_,?_,?_⟩
  · simpa [Z] using hmass
  · intro z hz w hw hne
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    exact same_color_grid_balls_disjoint hr color (Finset.mem_filter.mp hy).2
      (Finset.mem_filter.mp hv).2 hne
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).1
    have hh := cube_and_cylinders_in_grid_ball hr hδr (Q (cube y)) (center (cube y)) (hQ _ (hY y hy'))
    exact ⟨hh.1,fun j => hh.2 (b y j) (u y j) (L y j) (hu y hy' j) (hL y hy' j) (hinc y hy' j)⟩
  · exact cube_label_mass_eq Z cube cubes label hp

/-- Disjoint local balls prevent duplication of a nonempty geometric piece
across two distinct selected centers. -/
theorem localized_piece_center_unique {X I : Type*} (balls : I → Set X) (S : Set I)
    (hd : PairwiseDisjoint S balls) {i j : I} (hi : i ∈ S) (hj : j ∈ S)
    {piece : Set X} (hne : piece.Nonempty) (hpi : piece ⊆ balls i) (hpj : piece ⊆ balls j) : i=j := by
  by_contra h
  obtain ⟨x,hx⟩ := hne
  exact Set.disjoint_left.mp (hd hi hj h) (hpi hx) (hpj hx)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.rounded_center_dist
#print axioms KakeyaTwoScale.lattice_color_separation
#print axioms KakeyaTwoScale.cube_and_cylinders_in_grid_ball
#print axioms KakeyaTwoScale.same_color_grid_balls_disjoint

#print axioms KakeyaTwoScale.exists_spatial_tuple_localization
#print axioms KakeyaTwoScale.localized_piece_center_unique
