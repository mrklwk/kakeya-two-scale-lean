module
public import KakeyaTwoScale.AmbientBufferedStageInput

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Ambient data with its dimension equality kept explicit, for recursive
codimension changes in one fixed physical space. -/
structure FixedAmbientBufferedData (n b c k A B Lh J s : ℕ) (T C O : Type)
    [DecidableEq T] [DecidableEq C] where
  ambient_eq : n=b+c
  W : FrozenGeometryState n k T C O
  Y₀ : Finset T
  cube : T→C
  tube : T→Fin k→O
  cubes : Finset C
  Q : C→Set (EuclideanSpace ℝ (Fin n))
  P : W.Grain→Fin c→MvPolynomial (Fin n) ℝ
  D : ℕ→ℕ
  alpha : ℝ
  δ : ℝ
  K : ℝ
  center : C→EuclideanSpace ℝ (Fin n)
  dimension_pos : 0 < b
  families_pos : 0 < k
  exponent_pos : 0 < alpha
  exponent_le_one : alpha ≤ 1
  width_pos : 0 < δ
  capture_nonneg : 0 ≤ K
  valid : W.Valid Y₀ cube tube Q δ
  balanced : W.Balanced cube cubes alpha
  nonempty : W.tuples.Nonempty
  support : ∀ y ∈ Y₀, cube y ∈ cubes
  cardinal_bound : (Y₀.card:ℝ) ≤ (2:ℝ)^B
  height_bound : ∀ j, W.height j ≤ Lh
  degree : ∀ g ∈ W.grains cube, ∀ i, (P g i).totalDegree ≤ J
  regular : ∀ g ∈ W.grains cube, ∀ x, rectangularPolynomialMap (P g) x=0 →
    (fderiv ℝ (rectangularPolynomialMap (P g)) x).range=⊤
  capture : ∀ y ∈ W.tuples, ∀ j, W.geometry δ j (W.parent y j) ⊆
    thickening (K*δ) {x | rectangularPolynomialMap (P (W.grain (cube y))) x=0}
  partition_dimension : ∀ j < s, 2^j < (D j+1)^b
  partition_size : 2 ≤ s
  «measurable» : ∀ q ∈ cubes, MeasurableSet (Q q)
  finite_volume : ∀ q ∈ cubes, volume (Q q)≠⊤
  positive_volume : ∀ q ∈ cubes, 0 < volume.real (Q q)
  preconnected : ∀ q ∈ cubes, IsPreconnected (Q q)
  cube_radius : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*δ

namespace FixedAmbientBufferedData
variable {n b c k A B Lh J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

/-- Reindex only the ambient dimension equality; all raw data is transported
by equality elimination. -/
def toAmbient (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    AmbientBufferedStageData b c k A B Lh J s T C O := by
  have h := I.ambient_eq
  subst n
  exact {
    W := I.W,
    Y₀ := I.Y₀,
    cube := I.cube,
    tube := I.tube,
    cubes := I.cubes,
    Q := I.Q,
    P := I.P,
    D := I.D,
    alpha := I.alpha,
    δ := I.δ,
    K := I.K,
    center := I.center,
    dimension_pos := I.dimension_pos,
    families_pos := I.families_pos,
    exponent_pos := I.exponent_pos,
    exponent_le_one := I.exponent_le_one,
    width_pos := I.width_pos,
    capture_nonneg := I.capture_nonneg,
    valid := I.valid,
    balanced := I.balanced,
    nonempty := I.nonempty,
    support := I.support,
    cardinal_bound := I.cardinal_bound,
    height_bound := I.height_bound,
    degree := I.degree,
    regular := I.regular,
    capture := I.capture,
    partition_dimension := I.partition_dimension,
    partition_size := I.partition_size,
    «measurable» := I.«measurable»,
    finite_volume := I.finite_volume,
    positive_volume := I.positive_volume,
    preconnected := I.preconnected,
    cube_radius := I.cube_radius }

@[simp] theorem toAmbient_tuples (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.W.tuples=I.W.tuples := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_count (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) (j : Fin k) :
    I.toAmbient.W.count j=I.W.count j := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_grain_count (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    (I.toAmbient.W.grains I.toAmbient.cube).card=(I.W.grains I.cube).card := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_height (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) (j : Fin k) :
    I.toAmbient.W.height j=I.W.height j := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_original_data (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.Y₀=I.Y₀ ∧ I.toAmbient.cube=I.cube ∧ I.toAmbient.tube=I.tube ∧
      I.toAmbient.cubes=I.cubes ∧ I.toAmbient.alpha=I.alpha ∧ I.toAmbient.δ=I.δ := by
  have h := I.ambient_eq
  subst n
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

 theorem toAmbient_W (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    HEq I.toAmbient.W I.W := by
  have h := I.ambient_eq
  subst n
  rfl

 theorem toAmbient_Q (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    HEq I.toAmbient.Q I.Q := by
  have h := I.ambient_eq
  subst n
  rfl

 theorem toAmbient_P (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    HEq I.toAmbient.P I.P := by
  have h := I.ambient_eq
  subst n
  rfl

 theorem toAmbient_center (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    HEq I.toAmbient.center I.center := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_Y₀ (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.Y₀=I.Y₀ := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_cube (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.cube=I.cube := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_tube (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.tube=I.tube := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_cubes (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.cubes=I.cubes := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_alpha (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.alpha=I.alpha := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_δ (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.δ=I.δ := by
  have h := I.ambient_eq
  subst n
  rfl

@[simp] theorem toAmbient_K (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.K=I.K := by
  have h := I.ambient_eq
  subst n
  rfl

end FixedAmbientBufferedData
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FixedAmbientBufferedData.toAmbient
