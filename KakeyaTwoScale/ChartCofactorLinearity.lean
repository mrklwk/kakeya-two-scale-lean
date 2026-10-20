module
public import KakeyaTwoScale.ChartProjectionCofactor

@[expose] public section

open Matrix
noncomputable section
namespace KakeyaTwoScale

private theorem cofactor_matrix_update {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) (u : Fin (n+1) → ℝ) :
    Matrix.of (Fin.cons u (fun j => A (Pi.single j 1))) =
      Matrix.updateRow (Matrix.of (Fin.cons 0 (fun j => A (Pi.single j 1)))) 0 u := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Matrix.updateRow, Function.update]
  · simp [Matrix.updateRow, Function.update]

theorem chartCofactor_add {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) (u v : Fin (n+1) → ℝ) :
    chartCofactor A (u+v) = chartCofactor A u + chartCofactor A v := by
  unfold chartCofactor
  rw [cofactor_matrix_update A (u+v), cofactor_matrix_update A u, cofactor_matrix_update A v]
  exact Matrix.det_updateRow_add _ _ _ _

theorem chartCofactor_smul {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) (c : ℝ) (u : Fin (n+1) → ℝ) :
    chartCofactor A (c • u) = c * chartCofactor A u := by
  unfold chartCofactor
  rw [cofactor_matrix_update A (c • u), cofactor_matrix_update A u]
  exact Matrix.det_updateRow_smul _ _ _ _

theorem chartCofactor_zero {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) : chartCofactor A 0 = 0 := by
  simpa using chartCofactor_smul A 0 0

theorem chartCofactor_neg {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) (u : Fin (n+1) → ℝ) :
    chartCofactor A (-u) = -chartCofactor A u := by
  simpa using chartCofactor_smul A (-1) u

/-- Continuity in the actual chart differential for every fixed direction. -/
theorem continuous_chartCofactor {n : ℕ} (u : Fin (n+1) → ℝ) :
    Continuous (fun A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) => chartCofactor A u) := by
  unfold chartCofactor
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun k => ?_) i
  · exact continuous_const
  · exact (continuous_apply j).comp (continuous_id.clm_apply continuous_const)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chartCofactor_add
#print axioms KakeyaTwoScale.chartCofactor_smul
#print axioms KakeyaTwoScale.chartCofactor_zero
#print axioms KakeyaTwoScale.chartCofactor_neg
#print axioms KakeyaTwoScale.continuous_chartCofactor
