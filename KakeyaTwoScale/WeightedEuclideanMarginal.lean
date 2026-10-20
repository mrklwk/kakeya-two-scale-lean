module
public import KakeyaTwoScale.WeightedCubeProjection
public import KakeyaTwoScale.CoordinateNormalProjection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open MeasureTheory Set
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Coordinate splitting preserves the canonical Euclidean/product volumes. -/
theorem euclideanSumEquivProd_measurePreserving (b c : ℕ) :
    MeasurePreserving (EuclideanSpace.sumEquivProd (𝕜:=ℝ) (ι:=Fin b) (κ:=Fin c)) := by
  exact (WithLp.volume_preserving_ofLp
    (EuclideanSpace ℝ (Fin b)) (EuclideanSpace ℝ (Fin c))).comp
      (LinearIsometryEquiv.measurePreserving (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin b ⊕ Fin c => ℝ)))

theorem euclideanSumEquivProd_symm_measurePreserving (b c : ℕ) :
    MeasurePreserving (EuclideanSpace.sumEquivProd (𝕜:=ℝ) (ι:=Fin b) (κ:=Fin c)).symm := by
  exact (euclideanSumEquivProd_measurePreserving b c).symm
    (EuclideanSpace.sumEquivProd (𝕜:=ℝ) (ι:=Fin b) (κ:=Fin c)).toHomeomorph.toMeasurableEquiv

theorem euclideanSumEquivProd_fst {b c : ℕ} (x : EuclideanSpace ℝ (Fin b ⊕ Fin c)) :
    (EuclideanSpace.sumEquivProd x).1=coordinateBaseProjection x := by
  apply WithLp.ofLp_injective 2
  funext i
  simp [coordinateBaseProjection_apply,EuclideanSpace.sumEquivProd]

def euclideanSplitSet {b c : ℕ} (Q : Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) :
    Set (EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin c)) :=
  (EuclideanSpace.sumEquivProd (𝕜:=ℝ) (ι:=Fin b) (κ:=Fin c)).symm ⁻¹' Q

theorem measurableSet_euclideanSplitSet {b c : ℕ}
    (Q : Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (hQ : MeasurableSet Q) :
    MeasurableSet (euclideanSplitSet Q) :=
  hQ.preimage (EuclideanSpace.sumEquivProd (𝕜:=ℝ) (ι:=Fin b) (κ:=Fin c)).symm.continuous.measurable

theorem volume_euclideanSplitSet {b c : ℕ}
    (Q : Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (hQ : MeasurableSet Q) :
    volume (euclideanSplitSet Q)=volume Q := by
  exact (euclideanSumEquivProd_symm_measurePreserving b c).measure_preimage hQ.nullMeasurableSet

/-- The actual fiber marginal of normalized finite weighted whole sets. -/
def weightedEuclideanMarginal {b c : ℕ} {J : Type*}
    (cubes : Finset J) (Q : J → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (weight : J → ℝ) :
    EuclideanSpace ℝ (Fin b) → ℝ :=
  projectionMarginal (weightedWholeCubeDensity volume cubes (fun j => euclideanSplitSet (Q j)) weight)

theorem integrable_weightedEuclideanMarginal {b c : ℕ} {J : Type*}
    (cubes : Finset J) (Q : J → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (weight : J → ℝ)
    (hQ : ∀ j ∈ cubes, MeasurableSet (Q j)) (hf : ∀ j ∈ cubes, volume (Q j) ≠ ⊤) :
    Integrable (weightedEuclideanMarginal cubes Q weight) := by
  apply integrable_projectionMarginal
  apply integrable_weightedWholeCubeDensity
  · intro j hj; exact measurableSet_euclideanSplitSet _ (hQ j hj)
  · intro j hj; rw [volume_euclideanSplitSet _ (hQ j hj)]; exact hf j hj

theorem weightedEuclideanMarginal_nonneg {b c : ℕ} {J : Type*}
    (cubes : Finset J) (Q : J → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (weight : J → ℝ)
    (hw : ∀ j ∈ cubes, 0 ≤ weight j) : ∀ x, 0 ≤ weightedEuclideanMarginal cubes Q weight x :=
  projectionMarginal_nonneg _ (weightedWholeCubeDensity_nonneg volume cubes _ weight hw)

theorem integral_weightedEuclideanMarginal {b c : ℕ} {J : Type*}
    (cubes : Finset J) (Q : J → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (weight : J → ℝ)
    (hQ : ∀ j ∈ cubes, MeasurableSet (Q j)) (hf : ∀ j ∈ cubes, volume (Q j) ≠ ⊤)
    (hp : ∀ j ∈ cubes, 0 < volume.real (Q j)) :
    (∫ x, weightedEuclideanMarginal cubes Q weight x)=∑ j ∈ cubes, weight j := by
  have hi := integrable_weightedWholeCubeDensity volume cubes (fun j => euclideanSplitSet (Q j)) weight
    (fun j hj => measurableSet_euclideanSplitSet _ (hQ j hj))
    (fun j hj => by rw [volume_euclideanSplitSet _ (hQ j hj)]; exact hf j hj)
  rw [weightedEuclideanMarginal,projectionMarginal_integral _ hi]
  apply integral_weightedWholeCubeDensity
  · intro j hj; exact measurableSet_euclideanSplitSet _ (hQ j hj)
  · intro j hj; rw [volume_euclideanSplitSet _ (hQ j hj)]; exact hf j hj
  · intro j hj; simpa only [Measure.real,volume_euclideanSplitSet _ (hQ j hj)] using hp j hj

theorem wholeSetWeight_le_marginal_setIntegral {b c : ℕ} {J : Type*}
    (cubes selected : Finset J) (Q : J → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (weight : J → ℝ)
    (hsel : selected ⊆ cubes)
    (hQ : ∀ j ∈ cubes, MeasurableSet (Q j)) (hf : ∀ j ∈ cubes, volume (Q j) ≠ ⊤)
    (hp : ∀ j ∈ cubes, 0 < volume.real (Q j)) (hw : ∀ j ∈ cubes, 0 ≤ weight j)
    (S : Set (EuclideanSpace ℝ (Fin b))) (hS : MeasurableSet S)
    (hcontain : ∀ j ∈ selected, Q j ⊆ coordinateBaseProjection ⁻¹' S) :
    (∑ j ∈ selected, weight j) ≤ ∫ x in S, weightedEuclideanMarginal cubes Q weight x := by
  let T := fun j => euclideanSplitSet (Q j)
  have hT j (hj : j ∈ cubes) : MeasurableSet (T j) := measurableSet_euclideanSplitSet _ (hQ j hj)
  have hTf j (hj : j ∈ cubes) : volume (T j) ≠ ⊤ := by
    rw [show T j=euclideanSplitSet (Q j) from rfl,volume_euclideanSplitSet _ (hQ j hj)]
    exact hf j hj
  have hTp j (hj : j ∈ cubes) : 0 < volume.real (T j) := by
    simpa only [T,Measure.real,volume_euclideanSplitSet _ (hQ j hj)] using hp j hj
  have hi := integrable_weightedWholeCubeDensity volume cubes T weight hT hTf
  have hc : ∀ j ∈ selected, T j ⊆ Prod.fst ⁻¹' S := by
    intro j hj z hz
    have hh := hcontain j hj hz
    change coordinateBaseProjection ((EuclideanSpace.sumEquivProd (𝕜:=ℝ) (ι:=Fin b) (κ:=Fin c)).symm z) ∈ S at hh
    rw [← euclideanSumEquivProd_fst,ContinuousLinearEquiv.apply_symm_apply] at hh
    exact hh
  have hm := wholeCubeWeight_le_setIntegral volume cubes selected T weight hsel hT hTf hTp hw
    (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) hc
  rw [projectionMarginal_setIntegral _ hi S] at hm
  exact hm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclideanSumEquivProd_measurePreserving
#print axioms KakeyaTwoScale.integrable_weightedEuclideanMarginal
#print axioms KakeyaTwoScale.integral_weightedEuclideanMarginal
#print axioms KakeyaTwoScale.wholeSetWeight_le_marginal_setIntegral
