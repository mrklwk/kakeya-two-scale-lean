module
public import KakeyaTwoScale.ChartCofactorLinearity
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

open Matrix
noncomputable section
namespace KakeyaTwoScale

/-- The row convention equals the standard basis determinant, by transposition. -/
theorem chartCofactor_eq_basis_det {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) (u : Fin (n+1) → ℝ) :
    chartCofactor A u = (Pi.basisFun ℝ (Fin (n+1))).det
      (Fin.cons u (fun j => A (Pi.single j 1))) := by
  rw [Module.Basis.det_apply]
  exact (Matrix.det_transpose _).symm

/-- Exact ambient covariance, including singular maps. Orientation is retained
in the signed formula; no source-coordinate measure change is involved. -/
theorem chartCofactor_comp {n : ℕ}
    (B : (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ))
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) (u : Fin (n+1) → ℝ) :
    chartCofactor (B.comp A) (B u) = B.det * chartCofactor A u := by
  rw [chartCofactor_eq_basis_det,chartCofactor_eq_basis_det]
  have he : Fin.cons (B u) (fun j => (B.comp A) (Pi.single j 1)) =
      B.toLinearMap ∘ Fin.cons u (fun j => A (Pi.single j 1)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he,Module.Basis.det_comp]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chartCofactor_eq_basis_det
#print axioms KakeyaTwoScale.chartCofactor_comp
