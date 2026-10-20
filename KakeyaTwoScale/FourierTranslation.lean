module
public import KakeyaTwoScale.NormalizedFourier

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem normalizedFourier_translate (p : ℕ) [NeZero p] (f : ZMod p → ℂ) (a k : ZMod p) :
    normalizedFourier p (fun x => f (x-a)) k =
      ZMod.stdAddChar (-(a*k))*normalizedFourier p f k := by
  unfold normalizedFourier
  rw [ZMod.dft_apply,ZMod.dft_apply]
  simp only [smul_eq_mul]
  have he : (∑ x : ZMod p, ZMod.stdAddChar (-(x*k))*f (x-a)) =
      ∑ y : ZMod p, ZMod.stdAddChar (-((y+a)*k))*f y := by
    symm
    apply Fintype.sum_equiv (Equiv.addRight a)
    intro y
    simp
  rw [he]
  simp only [add_mul,neg_add,AddChar.map_add_eq_mul]
  simp_rw [show ∀ y : ZMod p, ZMod.stdAddChar (-(y*k))*ZMod.stdAddChar (-(a*k))*f y =
    ZMod.stdAddChar (-(a*k))*(ZMod.stdAddChar (-(y*k))*f y) from fun y => by ring]
  rw [← Finset.mul_sum]
  ring

theorem normalizedFourier_translate_norm (p : ℕ) [NeZero p] (f : ZMod p → ℂ) (a k : ZMod p) :
    ‖normalizedFourier p (fun x => f (x-a)) k‖ = ‖normalizedFourier p f k‖ := by
  rw [normalizedFourier_translate,norm_mul,AddChar.norm_apply,one_mul]

theorem finite_sum_translate {p : ℕ} [NeZero p] (f : ZMod p → ℝ) (a : ZMod p) :
    ∑ x, f (x-a) = ∑ x, f x := by
  apply Fintype.sum_equiv (Equiv.addRight (-a))
  intro x
  simp [sub_eq_add_neg]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalizedFourier_translate
#print axioms KakeyaTwoScale.normalizedFourier_translate_norm
#print axioms KakeyaTwoScale.finite_sum_translate
