module
public import KakeyaTwoScale.PolynomialIntervalL1
public import Mathlib.LinearAlgebra.Matrix.Polynomial

@[expose] public section

open MeasureTheory Polynomial Matrix
noncomputable section
namespace KakeyaTwoScale

private theorem eval_det_pencil {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) :
    Polynomial.eval t (Matrix.det ((Polynomial.X : Polynomial ℝ) • B.map Polynomial.C +
      A.map Polynomial.C)) = Matrix.det (A + t • B) := by
  change (Polynomial.evalRingHom t) _ = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [add_comm]
  ring

/-- The determinant-pencil L1 lower bound on any positive-length interval.
There is no invertibility assumption on either matrix. -/
theorem determinant_pencil_integral (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : Matrix (Fin m) (Fin m) ℝ) (a L : ℝ), 0 < L →
      |Matrix.det B| * L^(m+1) ≤ C * ∫ t in a..(a+L), |Matrix.det (A + t • B)| := by
  obtain ⟨C, hC, hbound⟩ := polynomial_unit_interval_L1 m
  refine ⟨C, hC, ?_⟩
  intro A B a L hL
  let A' := A + a • B
  let B' := L • B
  let p := Matrix.det ((Polynomial.X : Polynomial ℝ) • B'.map Polynomial.C + A'.map Polynomial.C)
  have hp : p.natDegree ≤ m := by
    simpa [p] using Polynomial.natDegree_det_X_add_C_le B' A'
  have hc : p.coeff m = L^m * Matrix.det B := by
    simpa [p, B', Matrix.det_smul] using Polynomial.coeff_det_X_add_C_card B' A'
  have he (t : ℝ) : p.eval t = Matrix.det (A + (a+L*t) • B) := by
    rw [eval_det_pencil]
    congr 1
    ext i j
    simp [A', B']
    ring
  have h := hbound p hp ⟨m, by omega⟩
  change |p.coeff m| ≤ _ at h
  rw [hc, abs_mul, abs_of_pos (pow_pos hL m)] at h
  have hi : L * (∫ t in (0:ℝ)..1, |p.eval t|) =
      ∫ t in a..(a+L), |Matrix.det (A + t • B)| := by
    simp_rw [he]
    simpa using intervalIntegral.smul_integral_comp_add_mul
      (fun t => |Matrix.det (A + t • B)|) (a := (0:ℝ)) (b := 1) L a
  calc
    |Matrix.det B| * L^(m+1) = L * (L^m * |Matrix.det B|) := by ring
    _ ≤ L * (C * ∫ t in (0:ℝ)..1, |p.eval t|) := mul_le_mul_of_nonneg_left h hL.le
    _ = C * ∫ t in a..(a+L), |Matrix.det (A + t • B)| := by rw [← hi]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.determinant_pencil_integral
