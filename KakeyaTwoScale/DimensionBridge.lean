module
public import KakeyaTwoScale.DyadicCover

@[expose] public section

open MeasureTheory Filter
noncomputable section
namespace KakeyaTwoScale

/-- Upper box dimension by polynomial growth of dyadic metric ball covers.
Nonemptiness of the admissible exponent set is required by the lower-bound
lemma below; its derivation from boundedness is not yet in this project. -/
def upperBoxDimension {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf {d : ℝ | 0 ≤ d ∧ DyadicCoverGrowth K d}

 theorem DyadicCoverGrowth.neighborhoodUpper {n : ℕ} [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} {d : ℝ} (H : DyadicCoverGrowth K d) :
    NeighborhoodUpper n d (fun q => neighborhoodVolume K (20*q)) (neighborhoodVolume K) := by
  obtain ⟨C,hC,Q,hV⟩ := H.volume_bound
  refine ⟨fun _ => ENNReal.toReal_nonneg, fun _ => ENNReal.toReal_nonneg, ?_⟩
  intro ε hε
  refine ⟨C,C,hC,hC,eventually_atTop.mpr ⟨Q,?_⟩⟩
  intro q hq
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hεq : 0 ≤ Real.log 2*ε*q := by positivity
  have hf := hV (20*q) (by omega)
  have hc := hV q hq
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  · apply hc.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    nlinarith

/-- A geometric-to-dimension bridge: transfer estimates for actual Euclidean
neighborhood volumes obstruct every smaller metric covering exponent. -/
theorem cover_exponent_lower_of_transfer (n : ℕ) (hn : 4 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (d : ℝ) (H : DyadicCoverGrowth K d)
    (transfer : BroadTransfer n (n/2:ℕ) (fun q => neighborhoodVolume K (20*q)) ∨
      NarrowTransfer n (n/2:ℕ) (fun q => neighborhoodVolume K (20*q)) (neighborhoodVolume K)) :
    (597/1000:ℝ)*n ≤ d := by
  let : NeZero n := ⟨by omega⟩
  exact endpoint_nat_of_volume_dichotomy n hn d _ _ H.neighborhoodUpper transfer

/-- Conditional upper-box lower bound for an actual Euclidean set.
The transfer alternative remains an explicit geometric hypothesis. -/
theorem upperBoxDimension_lower_of_transfer (n : ℕ) (hn : 4 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hadmissible : ∃ d : ℝ, 0 ≤ d ∧ DyadicCoverGrowth K d)
    (transfer : BroadTransfer n (n/2:ℕ) (fun q => neighborhoodVolume K (20*q)) ∨
      NarrowTransfer n (n/2:ℕ) (fun q => neighborhoodVolume K (20*q)) (neighborhoodVolume K)) :
    (597/1000:ℝ)*n ≤ upperBoxDimension K := by
  apply le_csInf hadmissible
  intro d hd
  exact cover_exponent_lower_of_transfer n hn K d hd.2 transfer
end KakeyaTwoScale
#print axioms KakeyaTwoScale.DyadicCoverGrowth.neighborhoodUpper
#print axioms KakeyaTwoScale.cover_exponent_lower_of_transfer
#print axioms KakeyaTwoScale.upperBoxDimension_lower_of_transfer
