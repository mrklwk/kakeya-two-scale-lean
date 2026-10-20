module
public import KakeyaTwoScale.IntervalFourier
public import KakeyaTwoScale.FiniteConvolution

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def intervalAverage (p q : ℕ) (f : ZMod p → ℝ) (x : ZMod p) : ℝ :=
  (q:ℝ)⁻¹*∑ y ∈ fieldInterval p q, f (x-y)

theorem intervalAverage_bounds (p q : ℕ) [NeZero p] (hq0 : 0 < q) (hq : q ≤ p)
    (f : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : ZMod p) :
    0 ≤ intervalAverage p q f x ∧ intervalAverage p q f x ≤ 1 := by
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq0
  unfold intervalAverage
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hqR.le) (Finset.sum_nonneg (fun y _ => (hf (x-y)).1))
  · have hsum : ∑ y ∈ fieldInterval p q, f (x-y) ≤ (q:ℝ) := by
      calc
        _ ≤ ∑ _y ∈ fieldInterval p q, (1:ℝ) := Finset.sum_le_sum (fun y _ => (hf (x-y)).2)
        _ = q := by simp [fieldInterval_card p q hq]
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hqR.le)
    simpa only [inv_mul_cancel₀ hqR.ne'] using h

theorem intervalAverage_sum (p q : ℕ) [NeZero p] (hq0 : 0 < q) (hq : q ≤ p)
    (f : ZMod p → ℝ) : ∑ x, intervalAverage p q f x = ∑ x, f x := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  unfold intervalAverage
  rw [← Finset.mul_sum,Finset.sum_comm]
  have he (y : ZMod p) : ∑ x : ZMod p, f (x-y) = ∑ x, f x := by
    apply Fintype.sum_equiv (Equiv.addRight (-y))
    intro x
    simp [sub_eq_add_neg]
  simp only [he,Finset.sum_const,nsmul_eq_mul,fieldInterval_card p q hq]
  rw [← mul_assoc,inv_mul_cancel₀ hqR,one_mul]

theorem intervalAverage_complex (p q : ℕ) [NeZero p] (f : ZMod p → ℝ) (x : ZMod p) :
    (intervalAverage p q f x:ℂ) = (p:ℂ)/(q:ℂ)*
      normalizedConvolution p (fun y => (intervalWeight p q y:ℂ)) (fun y => (f y:ℂ)) x := by
  have hp : (p:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  unfold intervalAverage normalizedConvolution intervalWeight
  push_cast
  simp only [apply_ite,Complex.ofReal_one,Complex.ofReal_zero,ite_mul,one_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter]
  field_simp

theorem intervalAverage_fourier (p q : ℕ) [NeZero p] (f : ZMod p → ℝ) (k : ZMod p) :
    normalizedFourier p (fun x => (intervalAverage p q f x:ℂ)) k =
      ((p:ℂ)/(q:ℂ))*normalizedFourier p (fun x => (intervalWeight p q x:ℂ)) k *
        normalizedFourier p (fun x => (f x:ℂ)) k := by
  simp_rw [intervalAverage_complex]
  unfold normalizedFourier
  rw [ZMod.dft_const_mul]
  dsimp only
  have h := normalizedFourier_convolution p (fun x => (intervalWeight p q x:ℂ)) (fun x => (f x:ℂ)) k
  unfold normalizedFourier at h
  linear_combination ((p:ℂ)/(q:ℂ))*h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.intervalAverage_bounds
#print axioms KakeyaTwoScale.intervalAverage_sum
#print axioms KakeyaTwoScale.intervalAverage_complex
#print axioms KakeyaTwoScale.intervalAverage_fourier
