module
public import KakeyaTwoScale.FiniteProgressions
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators ComplexConjugate

def normalizedFourier (p : ℕ) [NeZero p] (f : ZMod p → ℂ) (k : ZMod p) : ℂ :=
  (p:ℂ)⁻¹*ZMod.dft f k

def normalizedConvolution (p : ℕ) [NeZero p] (f g : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  (p:ℂ)⁻¹*∑ y : ZMod p, f y*g (x-y)

theorem normalizedFourier_zero (p : ℕ) [NeZero p] (f : ZMod p → ℂ) :
    normalizedFourier p f 0 = (p:ℂ)⁻¹*∑ x, f x := by
  rw [normalizedFourier,ZMod.dft_apply_zero]

theorem normalizedFourier_dilation (p : ℕ) [Fact p.Prime]
    (f : ZMod p → ℂ) (j : ZMod p) (hj : j ≠ 0) (k : ZMod p) :
    normalizedFourier p (fun x => f (j*x)) k = normalizedFourier p f (j⁻¹*k) := by
  have h := ZMod.dft_comp_unitMul f (Units.mk0 j hj) k
  simpa only [normalizedFourier,Units.val_mk0,Units.val_inv_eq_inv_val] using
    congrArg (fun z : ℂ => (p:ℂ)⁻¹*z) h

theorem normalizedFourier_inversion (p : ℕ) [NeZero p] (f : ZMod p → ℂ) (x : ZMod p) :
    normalizedFourier p (normalizedFourier p f) x = (p:ℂ)⁻¹*f (-x) := by
  have hp : (p:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  unfold normalizedFourier
  rw [ZMod.dft_const_mul,ZMod.dft_dft]
  simp only [smul_eq_mul]
  field_simp

/-- The transpose identity has no conjugation; it follows from symmetry of
the character matrix. It will be paired with conjugation for Parseval. -/
theorem dft_bilinear_identity (p : ℕ) [NeZero p] (f g : ZMod p → ℂ) :
    ∑ k, ZMod.dft f k*g k = ∑ x, f x*ZMod.dft g x := by
  simp only [ZMod.dft_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm k x]
  ring

theorem dft_conjugate_neg (p : ℕ) [NeZero p] (f : ZMod p → ℂ) (k : ZMod p) :
    ZMod.dft (fun x => conj (f x)) (-k) = conj (ZMod.dft f k) := by
  simp only [ZMod.dft_apply,smul_eq_mul,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_neg,neg_neg]
  congr 1
  rw [← AddChar.inv_apply_eq_conj,AddChar.map_neg_eq_inv,inv_inv]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalizedFourier_zero
#print axioms KakeyaTwoScale.normalizedFourier_dilation
#print axioms KakeyaTwoScale.normalizedFourier_inversion
#print axioms KakeyaTwoScale.dft_bilinear_identity
#print axioms KakeyaTwoScale.dft_conjugate_neg
