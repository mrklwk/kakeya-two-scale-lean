module
public import KakeyaTwoScale.ConcreteRootGeometry
public import KakeyaTwoScale.FrozenStateBalance

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

abbrev RootTuple (n k : ℕ) (O : Type) := (Fin n → ℤ) × (Fin k → O)

def coarseRootTuples {n k : ℕ} {O : Type} (Y : Finset (RootTuple n k O))
    (δ : ℝ) (a : Fin n → ℤ) : Finset (RootTuple n k O) := by
  classical
  exact Y.filter (fun y => rootCoarseOwner δ y.1 = a)

/-- Literal, uncut original cylinders and one grain in a coarse block. -/
def concreteRootState {n k : ℕ} {O : Type} (Y : Finset (RootTuple n k O))
    (q : ℕ) (a : Fin n → ℤ) (b u : O → EuclideanSpace ℝ (Fin n)) :
    FrozenGeometryState n k (RootTuple n k O) (Fin n → ℤ) O where
  Piece := O
  Grain := Unit
  tuples := coarseRootTuples Y ((2:ℝ)^q)⁻¹ a
  parent := fun y j => y.2 j
  grain := fun _ => ()
  origin := fun _ _ => ()
  original := fun _ o => o
  base := fun _ => b
  axis := fun _ => u
  height := fun _ => q
  ballCenter := fun _ => latticeCenter 1 a
  ballRadius := 2*n+6

theorem concreteRootState_length {n k : ℕ} {O : Type} (Y : Finset (RootTuple n k O))
    (q : ℕ) (a : Fin n → ℤ) (b u : O → EuclideanSpace ℝ (Fin n)) (j : Fin k) :
    (concreteRootState Y q a b u).length ((2:ℝ)^q)⁻¹ j = 1 := by
  simp [FrozenGeometryState.length, concreteRootState]

theorem concreteRootState_geometry {n k : ℕ} {O : Type} (Y : Finset (RootTuple n k O))
    (q : ℕ) (a : Fin n → ℤ) (b u : O → EuclideanSpace ℝ (Fin n)) (j : Fin k) (o : O) :
    (concreteRootState Y q a b u).geometry ((2:ℝ)^q)⁻¹ j o =
      flatCylinder (b o) (u o) 1 ((2:ℝ)^q)⁻¹ := by
  simp [FrozenGeometryState.geometry, FrozenGeometryState.length, concreteRootState]

/-- Validity comes from actual incidence; no geometric state certificate is
an input. Unit length and dimension-only localization are proved. -/
theorem concreteRootState_valid {n k : ℕ} {O : Type} (Y : Finset (RootTuple n k O))
    (q : ℕ) (a : Fin n → ℤ) (b u : O → EuclideanSpace ℝ (Fin n))
    (hu : ∀ o, ‖u o‖=1)
    (hinc : ∀ y ∈ Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
      flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty) :
    (concreteRootState Y q a b u).Valid
      (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a) Prod.fst Prod.snd
      (rootGridCube ((2:ℝ)^q)⁻¹) ((2:ℝ)^q)⁻¹ := by
  classical
  have hδ : 0 < ((2:ℝ)^q)⁻¹ := by positivity
  have hδ1 : ((2:ℝ)^q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  refine ⟨Finset.Subset.refl _, fun _ o => hu o, fun _ _ _ => rfl,
    fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro y hy j
    simpa [FrozenGeometryState.geometry, FrozenGeometryState.length, concreteRootState] using
      hinc y (Finset.mem_filter.mp hy).1 j
  · intro j o s hs t ht hst
    exact (hst (hs.2.trans ht.2.symm)).elim
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hh := rootGridCube_common_ball hδ hδ1 y.1
    rw [hy'.2] at hh
    exact ⟨hh.1, fun j => by
      simpa [FrozenGeometryState.geometry, FrozenGeometryState.length, concreteRootState] using
        hh.2 _ _ (hu _) (hinc y hy'.1 j)⟩

theorem concreteRootState_grains {n k : ℕ} {O : Type} (Y : Finset (RootTuple n k O))
    (q : ℕ) (a : Fin n → ℤ) (b u : O → EuclideanSpace ℝ (Fin n))
    (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty) :
    (concreteRootState Y q a b u).grains Prod.fst = {()} := by
  classical
  have he (x y : (concreteRootState Y q a b u).Grain) : x=y := by
    exact @Subsingleton.elim Unit inferInstance x y
  ext g
  constructor
  · intro _
    exact Finset.mem_singleton.mpr (he _ _)
  · intro _
    obtain ⟨y,hy⟩ := hne
    exact Finset.mem_image.mpr ⟨y,hy,he _ _⟩

/-- A nonempty singleton grain is balanced without selecting or discarding
any tuples or original records. -/
theorem concreteRootState_balanced {n k : ℕ} {O : Type} [DecidableEq O]
    (Y : Finset (RootTuple n k O)) (q : ℕ) (a : Fin n → ℤ)
    (b u : O → EuclideanSpace ℝ (Fin n))
    (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
    (cubes : Finset (Fin n → ℤ)) (p : ℝ) :
    (concreteRootState Y q a b u).Balanced Prod.fst cubes p := by
  classical
  intro g hg
  cases g
  have hm : 0 ≤ tupleCubeMass (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a) Prod.fst cubes p := by
    unfold tupleCubeMass
    exact Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hcard : ((concreteRootState Y q a b u).grains Prod.fst).card=1 := by
    rw [concreteRootState_grains Y q a b u hne]
    rfl
  rw [hcard]
  dsimp [concreteRootState, FrozenGeometryState.count, FrozenGeometryState.records,
    grainRecordCount]
  simp only [Finset.filter_true, Nat.cast_one, mul_one, div_one]
  constructor
  · constructor <;> linarith
  · intro j
    constructor
    · exact div_le_self (by positivity) (by norm_num)
    · exact le_mul_of_one_le_left (by positivity) (by norm_num)

/-- Literal original tuple identity; this does not assume a tuple encoding. -/
theorem rootTuple_identity {n k : ℕ} {O : Type} (x y : RootTuple n k O)
    (hc : x.1=y.1) (ht : ∀ j, x.2 j=y.2 j) : x=y :=
  Prod.ext hc (funext ht)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.concreteRootState_length
#print axioms KakeyaTwoScale.concreteRootState_geometry
#print axioms KakeyaTwoScale.concreteRootState_valid
#print axioms KakeyaTwoScale.concreteRootState_grains
#print axioms KakeyaTwoScale.concreteRootState_balanced
#print axioms KakeyaTwoScale.rootTuple_identity
