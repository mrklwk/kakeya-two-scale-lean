module
public import KakeyaTwoScale.PolynomialExtrapolationL1
public import KakeyaTwoScale.DeterminantPencilIntegral

@[expose] public section

open MeasureTheory Polynomial Matrix
noncomputable section
namespace KakeyaTwoScale

/-- Point evaluation of a determinant pencil, uniformly over singular matrices. -/
theorem determinant_pencil_extrapolation (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (A B : Matrix (Fin m) (Fin m) ℝ) (a L t₀ : ℝ), 0<L →
      |Matrix.det (A+t₀ • B)| * L ≤ C*(max 1 |(t₀-a)/L|)^m *
        ∫ t in a..(a+L), |Matrix.det (A+t • B)| := by
  obtain ⟨C,hC,h⟩ := polynomial_interval_extrapolation_L1 m
  refine ⟨C,hC,?_⟩
  intro A B a L t₀ hL
  let p := Matrix.det ((Polynomial.X : Polynomial ℝ) • B.map Polynomial.C + A.map Polynomial.C)
  have hp : p.natDegree≤m := by simpa [p] using Polynomial.natDegree_det_X_add_C_le B A
  have he (t : ℝ) : p.eval t=Matrix.det (A+t • B) := by
    change (Polynomial.evalRingHom t) _ = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [add_comm]
    ring
  simpa only [he] using h p hp a L t₀ hL

/-- The same exact estimate for actual Fréchet derivative operators. -/
theorem clm_pencil_extrapolation (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (A B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) (a L t₀ : ℝ), 0<L →
      |(A+t₀ • B).det| * L ≤ C*(max 1 |(t₀-a)/L|)^m *
        ∫ t in a..(a+L), |(A+t • B).det| := by
  obtain ⟨C,hC,h⟩ := determinant_pencil_extrapolation m
  refine ⟨C,hC,?_⟩
  intro A B a L t₀ hL
  have hp := h (LinearMap.toMatrix' A.toLinearMap) (LinearMap.toMatrix' B.toLinearMap) a L t₀ hL
  simpa only [← map_smul, ← map_add, LinearMap.det_toMatrix', ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul] using hp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.determinant_pencil_extrapolation
#print axioms KakeyaTwoScale.clm_pencil_extrapolation
