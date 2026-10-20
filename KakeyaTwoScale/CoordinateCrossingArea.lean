module
public import KakeyaTwoScale.ActualMixedCrossingIntegral
public import KakeyaTwoScale.PolynomialCoordinateRename

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def coordinateAxisFrame {n : ℕ} (j : Fin (n+1)) :
    EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  euclideanCoordinateRename ((finSuccEquiv' (0 : Fin (n+1))).trans (finSuccEquiv' j).symm)

theorem coordinateAxisFrame_cons {n : ℕ} (j : Fin (n+1)) (t : ℝ) (v : Fin n → ℝ) :
    orthogonalCoordinates (coordinateAxisFrame j) (Fin.cons t v) = j.insertNth t v := by
  ext i
  refine Fin.succAboveCases j ?_ (fun k => ?_) i
  · simp [orthogonalCoordinates,coordinateAxisFrame,euclideanCoordinateRename,LinearIsometryEquiv.piLpCongrLeft]
  · simp [orthogonalCoordinates,coordinateAxisFrame,euclideanCoordinateRename,LinearIsometryEquiv.piLpCongrLeft]

/-- Exact identification of the transverse root-count integral with the existing
localized atlas directional area, in the actual j-th coordinate direction. -/
theorem transverseBallCount_area {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0}) (j : Fin (n+1)) :
    (∫⁻ v, transverseBallCount (fun x => MvPolynomial.eval x.ofLp P) j v) =
      (A.restrict {x | (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1))) ∈ ball 0 1}
        ((isOpen_ball.preimage (PiLp.continuous_toLp 2 _)).measurableSet)).directionalArea (Pi.single j 1) := by
  let U : Set (Fin (n+1) → ℝ) := {x | (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1))) ∈ ball 0 1}
  have hU : MeasurableSet U := (isOpen_ball.preimage (PiLp.continuous_toLp 2 _)).measurableSet
  have h := (A.restrict U hU).frame_identity (coordinateAxisFrame j)
  have haxis : orthogonalCoordinates (coordinateAxisFrame j) (Pi.single 0 1) = Pi.single j 1 := by
    have hcons : (Pi.single 0 1 : Fin (n+1) → ℝ) = Fin.cons 1 0 := by ext i; cases i using Fin.cases <;> simp
    rw [hcons,coordinateAxisFrame_cons]
    ext i
    refine Fin.succAboveCases j ?_ (fun k => ?_) i <;> simp [Fin.succAbove_ne]
  rw [haxis] at h
  rw [h]
  apply lintegral_congr
  intro v
  unfold transverseBallCount ballCoordinateCount framedLineCount
  congr 2
  ext t
  have he : coordinateLinePoint j (WithLp.toLp 2 (j.insertNth 0 v)) t = WithLp.toLp 2 (j.insertNth t v) := by
    simp [coordinateLinePoint,Fin.update_insertNth]
  simp only [coordinateAxisFrame_cons,he,mem_ofPred_eq,mem_inter_iff,U]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateAxisFrame_cons
#print axioms KakeyaTwoScale.transverseBallCount_area
