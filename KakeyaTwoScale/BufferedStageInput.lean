module
public import KakeyaTwoScale.FrozenBufferedLocalSeeds
public import KakeyaTwoScale.FrozenDimensionStage

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- One orientation family fixed before any stage data are supplied. -/
noncomputable def bufferedStageOrientations (b c : ℕ) :
    Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)) :=
  Classical.choose (exists_frozen_buffered_local_seeds b c)

/-- Raw data at one completed incoming dimension. All geometric hypotheses
refer to the input state; there are no chosen partitions or output seeds. -/
structure BufferedStageInput (b c k A B Lh J s depth : ℕ) (T C O : Type)
    [DecidableEq T] [DecidableEq C] where
  W : FrozenGeometryState (b+c) k T C O
  Y₀ : Finset T
  cube : T → C
  tube : T → Fin k → O
  cubes : Finset C
  Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))
  P : W.Grain → Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ
  D : ℕ → ℕ
  alpha : ℝ
  η : ℝ
  r : ℝ
  δ : ℝ
  R : ℝ
  tag : C → EuclideanSpace ℝ (Fin b ⊕ Fin c)
  center : C → EuclideanSpace ℝ (Fin (b+c))
  dimension_pos : 0 < b
  families_pos : 0 < k
  exponent_pos : 0 < alpha
  exponent_le_one : alpha ≤ 1
  width_pos : 0 < δ
  buffer_gap : 2*δ < r
  capture_budget : η+2*(η+r) ≤ R*δ
  radius_nonneg : 0 ≤ (R+1)*δ
  valid : W.Valid Y₀ cube tube (fun q => physicalCoordinateCube (Q q)) δ
  balanced : W.Balanced cube cubes alpha
  nonempty : W.tuples.Nonempty
  support : ∀ y ∈ Y₀, cube y ∈ cubes
  cardinal_bound : (Y₀.card:ℝ) ≤ (2:ℝ)^B
  height_bound : ∀ j, W.height j ≤ Lh
  degree : ∀ g ∈ W.grains cube, ∀ i, (P g i).totalDegree ≤ J
  regular : ∀ g ∈ W.grains cube, ∀ x, rectangularPolynomialMap (P g) x=0 →
    (fderiv ℝ (rectangularPolynomialMap (P g)) x).range=⊤
  partition_dimension : ∀ j < s, 2^j < (D j+1)^b
  partition_size : 2 ≤ s
  measurable : ∀ q ∈ cubes, MeasurableSet (Q q)
  finite_volume : ∀ q ∈ cubes, volume (Q q) ≠ ⊤
  positive_volume : ∀ q ∈ cubes, 0 < volume.real (Q q)
  preconnected : ∀ q ∈ cubes, IsPreconnected (Q q)
  tag_zero : ∀ y ∈ W.tuples, rectangularPolynomialMap (P (W.grain (cube y))) (tag (cube y))=0
  tag_near : ∀ q ∈ W.tuples.image cube, ∀ x ∈ Q q, dist x (tag q) < η
  stopping_depth : ∀ g ∈ W.grains cube,
    Real.log (tupleCubeMass (W.grainTuples cube g) cube (W.grainCubes cube g) alpha) /
      (-Real.log ((2:ℝ)/2^s)) < depth
  cube_radius : ∀ q ∈ cubes, ∀ x ∈ physicalCoordinateCube (Q q), dist x (center q) ≤ (A:ℝ)*δ

namespace BufferedStageInput
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

theorem local_seeds (I : BufferedStageInput b c k A B Lh J s depth T C O) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin b ⊕ Fin c)), S=bufferedStageOrientations b c ∧ S.Nonempty ∧
      ∀ g ∈ I.W.grains I.cube,
        Nonempty (ActualBufferedStageSeed (J:=J) (s:=s) (A:=A) (Lh:=Lh) (B:=B) (depth:=depth)
          (I.P g) I.D S (I.W.grainTuples I.cube g) I.cube I.tube (I.W.grainCubes I.cube g)
          I.Q (I.W.localPhysical I.cube g I.δ) I.alpha I.δ I.R) := by
  classical
  let S := bufferedStageOrientations b c
  have hh := @Classical.choose_spec _ _ (exists_frozen_buffered_local_seeds b c)
    J s k A Lh B depth T C O inferInstance inferInstance I.W I.Y₀ I.cube I.tube I.cubes I.Q I.P I.D I.degree I.regular
    I.partition_dimension I.partition_size (fun y hy => I.support y (I.valid.1 hy))
    I.measurable I.finite_volume I.positive_volume I.preconnected
    I.alpha I.η I.r I.δ I.R I.exponent_pos I.exponent_le_one I.width_pos
    I.buffer_gap I.capture_budget I.radius_nonneg I.tag I.tag_zero I.tag_near I.stopping_depth
    I.families_pos I.valid I.height_bound
    ((show (I.W.tuples.card:ℝ) ≤ I.Y₀.card by exact_mod_cast Finset.card_le_card I.valid.1).trans I.cardinal_bound)
    I.center I.cube_radius
  obtain ⟨g,hg⟩ := I.nonempty.image (I.W.grain ∘ I.cube)
  exact ⟨S,rfl,(hh g hg).1,fun g hg => (hh g hg).2⟩

end BufferedStageInput
end KakeyaTwoScale
#print axioms KakeyaTwoScale.BufferedStageInput.local_seeds
