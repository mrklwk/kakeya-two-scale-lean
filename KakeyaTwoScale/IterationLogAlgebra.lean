module
public import KakeyaTwoScale.IterationSizeCases

@[expose] public section

namespace KakeyaTwoScale

/-- Exact logarithmic elimination. These are intermediate logarithmic
inequalities, not an assumed exponent update. The rho term has favorable
sign and is discarded only after its sign has been proved. -/
theorem iteration_log_elimination
    (β M ρ g n w l e h l0 l1 kd ko c a b z j : ℝ)
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hM : 0 < M) (hρ : 0 ≤ ρ) (hn : 0 ≤ n)
    (hfinal : β*(β-1)*h+β^2*l1 ≤ β*(β-1)*w+((2*β-1)*(β-1))*n+(β-1)^2*l0+
      β^2*kd+(2*β-1)*c+β*(β-1)*ko)
    (hh : l+e-z ≤ h) (he : w-2/M*n ≤ e)
    (hl1 : w+(ρ-100/M-2)*n ≤ l1) (hl0 : l0 ≤ z+w+(ρ-2)*n)
    (hkd : kd ≤ j+100/M*n) (hl : g-a-n ≤ l) (hw : 2*g-b-n ≤ w) :
    g ≤ ((β*(β-1)*(a+z+ko)+(β-1)^2*z+β^2*j+(2*β-1)*(c+b))/(β^2+3*β-2)) +
      (realArithmeticStep β+102/M)*n := by
  have hb : 0 < β-1 := by linarith
  have hb2 : 0 < 2*β-1 := by linarith
  have hd : 0 < β^2+3*β-2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ β*(β-1) by positivity)
  have h2 := mul_le_mul_of_nonneg_left he (show 0 ≤ β*(β-1) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hl1 (sq_nonneg β)
  have h4 := mul_le_mul_of_nonneg_left hl0 (sq_nonneg (β-1))
  have h5 := mul_le_mul_of_nonneg_left hkd (sq_nonneg β)
  have h6 := mul_le_mul_of_nonneg_left hl (show 0 ≤ β*(β-1) by positivity)
  have h7 := mul_le_mul_of_nonneg_left hw hb2.le
  have hraw : (β^2+3*β-2)*g ≤
      (3*β^2+2*β-2)*n+(1-2*β)*ρ*n+(200*β^2+2*β*(β-1))/M*n+
      (β*(β-1)*(a+z+ko)+(β-1)^2*z+β^2*j+(2*β-1)*(c+b)) := by
    have hid : (200*β^2+2*β*(β-1))/M = 2/M*(β*(β-1))+2*(100/M)*β^2 := by ring
    rw [hid]
    nlinarith only [hfinal,h1,h2,h3,h4,h5,h6,h7]
  have hrho : (1-2*β)*ρ*n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) hρ) hn
  have hcoef : 200*β^2+2*β*(β-1) ≤ 102*(β^2+3*β-2) := by
    have hp := mul_nonneg (show 0 ≤ β-1 by linarith) (show 0 ≤ 2-β by linarith)
    nlinarith
  have hcoef' := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef hM.le) hn
  apply (mul_le_mul_iff_right₀ hd).mp
  have hid : (β^2+3*β-2)*
      ((β*(β-1)*(a+z+ko)+(β-1)^2*z+β^2*j+(2*β-1)*(c+b))/(β^2+3*β-2)+
        (realArithmeticStep β+102/M)*n) =
      β*(β-1)*(a+z+ko)+(β-1)^2*z+β^2*j+(2*β-1)*(c+b)+
        (3*β^2+2*β-2)*n+102*(β^2+3*β-2)/M*n := by
    unfold realArithmeticStep
    simp only [mul_add, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hd)]
    ring
  rw [hid]
  nlinarith only [hraw,hrho,hcoef']

end KakeyaTwoScale
#print axioms KakeyaTwoScale.iteration_log_elimination
