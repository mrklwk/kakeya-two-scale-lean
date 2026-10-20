module
public import KakeyaTwoScale.ReindexedAmbientBufferedData
public import KakeyaTwoScale.ActualNormalizedStageGeometry
public import KakeyaTwoScale.PartitionDegreeBudget

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace AmbientBufferedStageData
variable {b c k A B Lh J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

def successorDegree (I : AmbientBufferedStageData b c k A B Lh J s T C O) : ℕ :=
  max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i)))

/-- Construct the raw data for the next dimension using the actual normalized
output. This frame stays in the original ambient space. -/
def nextFrame (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    FixedAmbientBufferedData (b+c) (b-1) (c+1) k A B Lh I.successorDegree ((b-1)*t) T C O := by
  classical
  refine {
    ambient_eq := by omega,
    W := Z.state, Y₀ := I.Y₀, cube := I.cube, tube := I.tube, cubes := I.cubes,
    Q := I.Q, P := Z.equations, D := partitionBoxDegree (b-1),
    alpha := I.alpha, δ := I.δ, K := I.toInput.R+3, center := I.center,
    dimension_pos := by omega, families_pos := I.families_pos,
    exponent_pos := I.exponent_pos, exponent_le_one := I.exponent_le_one,
    width_pos := I.width_pos,
    capture_nonneg := ?_, valid := ?_, balanced := Z.balanced, nonempty := Z.nonempty,
    support := I.support, cardinal_bound := I.cardinal_bound,
    height_bound := fun j=>(Z.heights j).trans (I.height_bound j),
    degree := fun g _ i=>Z.degrees g i, regular := Z.regular, capture := Z.capture,
    partition_dimension := fun j _=>partitionBoxDegree_dimension (b-1) (by omega) j,
    partition_size := by nlinarith [show 1 ≤ b-1 by omega],
    «measurable» := I.measurable, finite_volume := I.finite_volume,
    positive_volume := I.positive_volume, preconnected := I.preconnected,
    cube_radius := I.cube_radius }
  · change 0  ≤  3*(2*(A:ℝ)+I.K)+6+3
    nlinarith [I.capture_nonneg,Nat.cast_nonneg (α:=ℝ) A]
  · have hv := Z.valid
    change Z.state.Valid I.Y₀ I.cube I.tube (fun q=>physicalCoordinateCube (I.toInput.Q q)) I.δ at hv
    simpa only [toInput_physicalCube] using hv

/-- A genuine next-stage ambient input: polynomial equations and neighborhoods
come from the constructed normalized result, and tags/depth are regenerated
by `toInput` when the next stage runs. -/
def nextData (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    AmbientBufferedStageData (b-1) (c+1) k A B Lh I.successorDegree ((b-1)*t) T C O :=
  (I.nextFrame Z hb t ht).toAmbient

@[simp] theorem nextData_count (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) (j : Fin k) :
    (I.nextData Z hb t ht).W.count j=Z.state.count j :=
  FixedAmbientBufferedData.toAmbient_count _ j

@[simp] theorem nextData_height (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) (j : Fin k) :
    (I.nextData Z hb t ht).W.height j=Z.state.height j :=
  FixedAmbientBufferedData.toAmbient_height _ j

@[simp] theorem nextData_tuples (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).W.tuples=Z.state.tuples :=
  FixedAmbientBufferedData.toAmbient_tuples _

@[simp] theorem nextData_grain_count (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    ((I.nextData Z hb t ht).W.grains (I.nextData Z hb t ht).cube).card=(Z.state.grains I.cube).card :=
  FixedAmbientBufferedData.toAmbient_grain_count _

@[simp] theorem nextData_Y₀ (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).Y₀=I.Y₀ :=
  FixedAmbientBufferedData.toAmbient_Y₀ _

@[simp] theorem nextData_cube (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).cube=I.cube :=
  FixedAmbientBufferedData.toAmbient_cube _

@[simp] theorem nextData_tube (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).tube=I.tube :=
  FixedAmbientBufferedData.toAmbient_tube _

@[simp] theorem nextData_cubes (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).cubes=I.cubes :=
  FixedAmbientBufferedData.toAmbient_cubes _

@[simp] theorem nextData_alpha (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).alpha=I.alpha :=
  FixedAmbientBufferedData.toAmbient_alpha _

@[simp] theorem nextData_δ (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).δ=I.δ :=
  FixedAmbientBufferedData.toAmbient_δ _

theorem nextData_state_HEq (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    HEq (I.nextData Z hb t ht).W Z.state :=
  FixedAmbientBufferedData.toAmbient_W _

@[simp] theorem nextData_delta (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).δ=I.δ := I.nextData_δ Z hb t ht

theorem nextData_equations_HEq (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    HEq (I.nextData Z hb t ht).P Z.equations :=
  FixedAmbientBufferedData.toAmbient_P _

theorem nextData_cubes_HEq (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1 < b) (t : ℕ) (ht : 2 ≤ t) :
    HEq (I.nextData Z hb t ht).Q I.Q :=
  FixedAmbientBufferedData.toAmbient_Q _

end AmbientBufferedStageData
end KakeyaTwoScale
#print axioms KakeyaTwoScale.AmbientBufferedStageData.nextFrame
#print axioms KakeyaTwoScale.AmbientBufferedStageData.nextData
