module
public import KakeyaTwoScale.IntegratedPathCrossing
public import KakeyaTwoScale.CoordinateMarginalIntegration

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Same literal localized count, parameterized only by the transverse coordinates. -/
def transverseBallCount {n : ℕ} (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (j : Fin (n+1)) (v : Fin n → ℝ) : ℝ≥0∞ :=
  ballCoordinateCount f j (WithLp.toLp 2 (j.insertNth 0 v))

theorem ballCoordinateCount_transverse {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (j : Fin (n+1))
    (a : EuclideanSpace ℝ (Fin (n+1))) :
    ballCoordinateCount f j a = transverseBallCount f j (fun i => a (j.succAbove i)) := by
  have he (t : ℝ) : coordinateLinePoint j a t =
      coordinateLinePoint j (WithLp.toLp 2 (j.insertNth 0 (fun i => a (j.succAbove i)))) t := by
    ext i
    refine Fin.succAboveCases j ?_ (fun k => ?_) i
    · simp [coordinateLinePoint]
    · simp [coordinateLinePoint,Fin.succAbove_ne]
  simp only [ballCoordinateCount,transverseBallCount,he]

theorem measurable_transverseBallCount {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hf : Continuous f) (j : Fin (n+1)) :
    Measurable (transverseBallCount f j) := by
  apply (measurable_ballCoordinateCount f hf j).comp
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
    (continuous_const.finInsertNth j continuous_id)).measurable

/-- The actual mixed path count has the proved product-marginal formula. No
uniform fiber bound or assumed area estimate replaces these literal counts. -/
theorem actual_mixed_crossing_integral {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hf : Continuous f)
    (μ ν : Fin (n+1) → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (j : Fin (n+1)) :
    (∫⁻ z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ),
      ballCoordinateCount f j (coordinateHybrid (WithLp.toLp 2 z.1) (WithLp.toLp 2 z.2) j.val)
      ∂((Measure.pi μ).prod (Measure.pi ν))) =
      (Measure.pi (fun i => if i.val < j.val then μ i else ν i)) univ * μ j univ *
        ∫⁻ v, transverseBallCount f j v ∂Measure.pi
          (fun i => if (j.succAbove i).val < j.val then ν (j.succAbove i) else μ (j.succAbove i)) := by
  let s : Finset (Fin (n+1)) := Finset.univ.filter (fun i => i.val < j.val)
  have h := lintegral_mixed_transverse s μ ν j (transverseBallCount f j)
    (measurable_transverseBallCount f hf j)
  simp only [s,Finset.mem_filter,Finset.mem_univ,true_and,lt_self_iff_false,ite_false] at h
  simp only [ballCoordinateCount_transverse]
  exact h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ballCoordinateCount_transverse
#print axioms KakeyaTwoScale.measurable_transverseBallCount
#print axioms KakeyaTwoScale.actual_mixed_crossing_integral
