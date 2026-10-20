module
public import KakeyaTwoScale.FiniteParseval

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem dft_convolution_sum (p : ℕ) [NeZero p] (f g : ZMod p → ℂ) (k : ZMod p) :
    ZMod.dft (fun x => ∑ y, f y*g (x-y)) k = ZMod.dft f k*ZMod.dft g k := by
  simp only [ZMod.dft_apply,smul_eq_mul]
  conv_lhs =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  have hs : (∑ x : ZMod p, ZMod.stdAddChar (-(x*k))*(f y*g (x-y))) =
      ∑ z : ZMod p, ZMod.stdAddChar (-((y+z)*k))*(f y*g z) := by
    symm
    apply Fintype.sum_equiv (Equiv.addLeft y)
    intro z
    simp
  rw [hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [add_mul,neg_add,AddChar.map_add_eq_mul]
  ring

/-- PZ's normalized convolution becomes a pointwise product under PZ's
normalized Fourier transform, with no missing factor p. -/
theorem normalizedFourier_convolution (p : ℕ) [NeZero p]
    (f g : ZMod p → ℂ) (k : ZMod p) :
    normalizedFourier p (normalizedConvolution p f g) k =
      normalizedFourier p f k*normalizedFourier p g k := by
  unfold normalizedFourier normalizedConvolution
  rw [ZMod.dft_const_mul]
  dsimp only
  rw [dft_convolution_sum]
  ring

/-- The spectral identity used for the total smoothed progression energy. -/
theorem normalized_convolution_parseval (p : ℕ) [NeZero p] (f g : ZMod p → ℂ) :
    (p:ℝ)⁻¹*∑ x, ‖normalizedConvolution p f g x‖^2 =
      ∑ k, ‖normalizedFourier p f k‖^2*‖normalizedFourier p g k‖^2 := by
  rw [← normalizedFourier_parseval]
  simp only [normalizedFourier_convolution,norm_mul,mul_pow]

/-- Finite sums over the actual restricted index set may be interchanged;
the zero-frequency term can subsequently be separated explicitly. -/
theorem progression_spectral_sum (p : ℕ) [Fact p.Prime] (J : Finset (ZMod p))
    (hJ : ∀ j ∈ J, j ≠ 0) (f ψ : ZMod p → ℂ) :
    ∑ j ∈ J, ((p:ℝ)⁻¹*∑ x, ‖normalizedConvolution p f (fun x => ψ (j*x)) x‖^2) =
      ∑ k : ZMod p, ‖normalizedFourier p f k‖^2*
        ∑ j ∈ J, ‖normalizedFourier p ψ (j⁻¹*k)‖^2 := by
  simp only [normalized_convolution_parseval]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [normalizedFourier_dilation p ψ j (hJ j hj)]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dft_convolution_sum
#print axioms KakeyaTwoScale.normalizedFourier_convolution
#print axioms KakeyaTwoScale.normalized_convolution_parseval
#print axioms KakeyaTwoScale.progression_spectral_sum
