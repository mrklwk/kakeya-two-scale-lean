module
public import KakeyaTwoScale.IntegerEncoding
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Real floor errors are bounded uniformly, with no sign restriction. -/
theorem floor_error_bound (x : ℝ) : |(⌊x⌋:ℝ)-x| ≤ 1 := by
  rw [abs_sub_comm,Int.self_sub_floor,abs_of_nonneg (Int.fract_nonneg x)]
  exact (Int.fract_lt_one x).le

/-- Signed integer coefficients are allowed. The carry bound depends only
on those coefficients, not on the inputs or the later modulus. -/
theorem linear_floor_carry_bound (a b : ℤ) (x y : ℝ) :
    |a*⌊x⌋+b*⌊y⌋-⌊(a:ℝ)*x+(b:ℝ)*y⌋| ≤ |a|+|b|+1 := by
  have hid : ((a*⌊x⌋+b*⌊y⌋-⌊(a:ℝ)*x+(b:ℝ)*y⌋:ℤ):ℝ) =
      (a:ℝ)*((⌊x⌋:ℝ)-x)+(b:ℝ)*((⌊y⌋:ℝ)-y)-
        ((⌊(a:ℝ)*x+(b:ℝ)*y⌋:ℝ)-((a:ℝ)*x+(b:ℝ)*y)) := by push_cast; ring
  have hx := mul_le_mul_of_nonneg_left (floor_error_bound x) (abs_nonneg (a:ℝ))
  have hy := mul_le_mul_of_nonneg_left (floor_error_bound y) (abs_nonneg (b:ℝ))
  have hz := floor_error_bound ((a:ℝ)*x+(b:ℝ)*y)
  have hab := abs_add_le ((a:ℝ)*((⌊x⌋:ℝ)-x)) ((b:ℝ)*((⌊y⌋:ℝ)-y))
  have hall := abs_sub ((a:ℝ)*((⌊x⌋:ℝ)-x)+(b:ℝ)*((⌊y⌋:ℝ)-y))
    ((⌊(a:ℝ)*x+(b:ℝ)*y⌋:ℝ)-((a:ℝ)*x+(b:ℝ)*y))
  simp only [abs_mul,mul_one] at hx hy hab
  have hh : |((a*⌊x⌋+b*⌊y⌋-⌊(a:ℝ)*x+(b:ℝ)*y⌋:ℤ):ℝ)| ≤
      |(a:ℝ)|+|(b:ℝ)|+1 := by rw [hid]; linarith
  exact_mod_cast hh

def modularRound (p : ℕ) (θ : ℝ) (x : ℤ) : ZMod p := (⌊θ*(x:ℝ)⌋:ℤ)

def integerLinearForm (a b : ℤ) (v : ℤ × ℤ) : ℤ := a*v.1+b*v.2

def modularLinearForm (p : ℕ) (a b : ℤ) (v : ZMod p × ZMod p) : ZMod p :=
  (a:ZMod p)*v.1+(b:ZMod p)*v.2

def modularPair (p : ℕ) (θ : ℝ) (v : ℤ × ℤ) : ZMod p × ZMod p :=
  (modularRound p θ v.1,modularRound p θ v.2)

/-- The modular projection is a rounded original linear form plus one of a
fixed finite set of carries. No primality or denominator-invertibility is
needed for this integer-coefficient statement. -/
theorem modular_projection_carry (p : ℕ) (θ : ℝ) (a b : ℤ) (v : ℤ × ℤ) :
    ∃ c : ℤ, |c| ≤ |a|+|b|+1 ∧
      modularLinearForm p a b (modularPair p θ v) =
        modularRound p θ (integerLinearForm a b v)+(c:ZMod p) := by
  let c := a*⌊θ*(v.1:ℝ)⌋+b*⌊θ*(v.2:ℝ)⌋-⌊θ*(integerLinearForm a b v:ℝ)⌋
  have he : θ*(integerLinearForm a b v:ℝ) = (a:ℝ)*(θ*(v.1:ℝ))+(b:ℝ)*(θ*(v.2:ℝ)) := by
    simp only [integerLinearForm,Int.cast_add,Int.cast_mul]
    ring
  refine ⟨c,?_,?_⟩
  · dsimp [c]
    rw [he]
    exact linear_floor_carry_bound a b _ _
  · simp only [modularLinearForm,modularPair,modularRound,c,Int.cast_sub,Int.cast_add,Int.cast_mul]
    ring

/-- Correct denominator clearing: r=a/b corresponds to b*x+a*y. -/
theorem rational_projection_integer_form (a b : ℤ) (hb : b ≠ 0) (v : ℤ × ℤ) :
    (b:ℚ)*integerProjection ((a:ℚ)/(b:ℚ)) v = (integerLinearForm b a v:ℚ) := by
  have hbq : (b:ℚ) ≠ 0 := by exact_mod_cast hb
  simp only [integerProjection,integerLinearForm,Int.cast_add,Int.cast_mul]
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.floor_error_bound
#print axioms KakeyaTwoScale.linear_floor_carry_bound
#print axioms KakeyaTwoScale.modular_projection_carry
#print axioms KakeyaTwoScale.rational_projection_integer_form
