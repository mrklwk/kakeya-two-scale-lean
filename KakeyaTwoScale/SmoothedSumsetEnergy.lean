module
public import KakeyaTwoScale.FiniteConvolution

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

theorem finite_support_cauchy {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (f : A → ℂ) (hf : ∀ x, x ∉ S → f x = 0) :
    ‖∑ x, f x‖^2 ≤ (S.card:ℝ)*∑ x, ‖f x‖^2 := by
  have hs : ∑ x, f x = ∑ x ∈ S, f x := Finset.sum_subset (Finset.subset_univ _) (by intro x _ hx; exact hf x hx) |>.symm
  have hs2 : ∑ x, ‖f x‖^2 = ∑ x ∈ S, ‖f x‖^2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp [hf x hx]
  rw [hs,hs2]
  have hn := norm_sum_le S f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) S (fun _ => 1) (fun x => ‖f x‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  have hsum : 0 ≤ ∑ x ∈ S, ‖f x‖ := Finset.sum_nonneg (fun x _ => norm_nonneg _)
  nlinarith [norm_nonneg (∑ x ∈ S, f x)]

theorem normalizedConvolution_support (p : ℕ) [NeZero p] (A B : Finset (ZMod p))
    (f g : ZMod p → ℂ) (hf : ∀ x, x ∉ A → f x = 0) (hg : ∀ x, x ∉ B → g x = 0)
    (x : ZMod p) (hx : x ∉ A+B) : normalizedConvolution p f g x = 0 := by
  unfold normalizedConvolution
  have hs : ∑ y : ZMod p, f y*g (x-y) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y ∈ A
    · have hxy : x-y ∉ B := by
        intro h
        apply hx
        exact Finset.mem_add.mpr ⟨y,hy,x-y,h,by ring⟩
      rw [hg _ hxy,mul_zero]
    · rw [hf _ hy,zero_mul]
  rw [hs,mul_zero]

theorem normalizedConvolution_sum (p : ℕ) [NeZero p] (f g : ZMod p → ℂ) :
    ∑ x, normalizedConvolution p f g x = (p:ℂ)⁻¹*(∑ x, f x)*(∑ x, g x) := by
  have hp : (p:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have h := normalizedFourier_convolution p f g 0
  simp only [normalizedFourier_zero] at h
  field_simp at h ⊢
  linear_combination h

/-- Exact smoothed sumset Cauchy–Schwarz bound. The p³ factor corresponds to
averaged squared convolution norm, as in the primary source's equation (7). -/
theorem smoothed_sumset_energy_bound (p : ℕ) [NeZero p] (A B : Finset (ZMod p))
    (f g : ZMod p → ℂ) (hf : ∀ x, x ∉ A → f x = 0) (hg : ∀ x, x ∉ B → g x = 0) :
    ‖∑ x, f x‖^2*‖∑ x, g x‖^2 ≤
      ((A+B).card:ℝ)*(p:ℝ)^3*((p:ℝ)⁻¹*∑ x, ‖normalizedConvolution p f g x‖^2) := by
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hc := finite_support_cauchy (A+B) (normalizedConvolution p f g)
    (normalizedConvolution_support p A B f g hf hg)
  rw [normalizedConvolution_sum] at hc
  simp only [norm_mul,norm_inv,Complex.norm_natCast,mul_pow] at hc
  have h := mul_le_mul_of_nonneg_left hc (sq_nonneg (p:ℝ))
  field_simp at h ⊢
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_support_cauchy
#print axioms KakeyaTwoScale.normalizedConvolution_support
#print axioms KakeyaTwoScale.normalizedConvolution_sum
#print axioms KakeyaTwoScale.smoothed_sumset_energy_bound
