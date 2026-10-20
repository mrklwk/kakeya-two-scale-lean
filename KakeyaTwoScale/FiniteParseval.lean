module
public import KakeyaTwoScale.NormalizedFourier

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators ComplexConjugate

/-- Parseval for mathlib's counting-measure DFT, with its factor p explicit. -/
theorem dft_parseval (p : ℕ) [NeZero p] (f : ZMod p → ℂ) :
    ∑ k, ‖ZMod.dft f k‖^2 = (p:ℝ)*∑ x, ‖f x‖^2 := by
  have ht (x : ZMod p) : ZMod.dft (fun k => conj (ZMod.dft f k)) x = (p:ℂ)*conj (f x) := by
    have h := dft_conjugate_neg p (ZMod.dft f) (-x)
    simp only [neg_neg,ZMod.dft_dft,smul_eq_mul,map_mul,map_natCast] at h
    exact h
  have hc : ((∑ k, Complex.normSq (ZMod.dft f k)):ℂ) = (p:ℂ)*((∑ x, Complex.normSq (f x)):ℂ) := by
    simp only [← Complex.mul_conj]
    rw [dft_bilinear_identity p f (fun k => conj (ZMod.dft f k))]
    simp only [ht,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h := congrArg Complex.re hc
  norm_cast at h
  simpa only [Complex.normSq_eq_norm_sq] using h


/-- Parseval with exactly the normalized-average convention of PZ. -/
theorem normalizedFourier_parseval (p : ℕ) [NeZero p] (f : ZMod p → ℂ) :
    ∑ k, ‖normalizedFourier p f k‖^2 = (p:ℝ)⁻¹*∑ x, ‖f x‖^2 := by
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [normalizedFourier,norm_mul,norm_inv,Complex.norm_natCast,mul_pow,← Finset.mul_sum]
  rw [dft_parseval]
  field_simp

/-- Indicator normalization: its Fourier squared mass is |A|/p. -/
theorem normalizedFourier_indicator_mass (p : ℕ) [NeZero p] (A : Finset (ZMod p)) :
    ∑ k, ‖normalizedFourier p (fun x => if x ∈ A then (1:ℂ) else 0) k‖^2 = (A.card:ℝ)/(p:ℝ) := by
  rw [normalizedFourier_parseval]
  simp only [apply_ite,norm_one,norm_zero]
  simp [div_eq_mul_inv,mul_comm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dft_parseval
#print axioms KakeyaTwoScale.normalizedFourier_parseval
#print axioms KakeyaTwoScale.normalizedFourier_indicator_mass
