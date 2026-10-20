module
public import KakeyaTwoScale.UniformPowerThresholds

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

theorem floor_power_bounds (x : ℝ) (hx : 2 ≤ x) :
    x/2 ≤ (Nat.floor x:ℝ) ∧ (Nat.floor x:ℝ) ≤ x := by
  have h1 := Nat.floor_le (by linarith : 0 ≤ x)
  have h2 := Nat.lt_floor_add_one x
  constructor <;> linarith

/-- Integer cutoff U=(Kp)/m satisfies both needed scale bounds. -/
theorem frequency_floor_parameters (p m K : ℕ) (hm : 0 < m) (hmp : m ≤ p) :
    (K*p/m)*m ≤ K*p ∧ (K:ℝ) ≤ 1+(K*p/m:ℕ)*(m:ℝ)/(p:ℝ) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast (lt_of_lt_of_le hm hmp)
  have he := Nat.mod_add_div (K*p) m
  have hr := Nat.mod_lt (K*p) hm
  have hnat : K*p ≤ p+(K*p/m)*m := by nlinarith
  refine ⟨Nat.div_mul_le_self _ _,?_⟩
  have hreal : (K:ℝ)*(p:ℝ) ≤ (p:ℝ)+(K*p/m:ℕ)*(m:ℝ) := by exact_mod_cast hnat
  have h := (le_div_iff₀ hp).mpr hreal
  convert h using 1
  field_simp

theorem half_interval_parameters (m : ℕ) (hm : 0 < m) :
    1 ≤ (m+1)/2 ∧ (m+1)/2 ≤ m ∧ (m:ℝ)/2 ≤ ((m+1)/2:ℕ) := by
  refine ⟨by omega,by omega,?_⟩
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  exact_mod_cast (show m ≤ (m+1)/2*2 by omega)

/-- The strict positive exponent gap absorbs the dyadic-prime divisor
constant, with the floor loss written explicitly. -/
theorem divisor_power_domination (x ε δ : ℝ) (b : ℕ) (hx : 0 < x)
    (hgap : 3*(2:ℝ)^b < x^(ε*(b:ℝ)-1-δ)) :
    3*x^δ*x < (x^ε/2)^b := by
  have hxpow : 0 < x^(1+δ) := Real.rpow_pos_of_pos hx _
  have h := mul_lt_mul_of_pos_right hgap hxpow
  have he : x^(ε*(b:ℝ)-1-δ)*x^(1+δ) = x^(ε*(b:ℝ)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [he] at h
  have he2 : x^(1+δ) = x*x^δ := by rw [Real.rpow_add hx,Real.rpow_one]
  rw [he2] at h
  rw [div_pow,← Real.rpow_natCast,← Real.rpow_mul hx.le]
  apply (lt_div_iff₀ (by positivity : 0 < (2:ℝ)^b)).mpr
  convert h using 1; ring

theorem floor_divisor_cut (p m B : ℕ) (ε δ : ℝ) (hp : 0 < p)
    (hpδ : 2 ≤ (p:ℝ)^δ) (hm : (p:ℝ)^ε ≤ (m:ℝ))
    (hgap : 3*(2:ℝ)^(B+1) < (p:ℝ)^(ε*((B:ℝ)+1)-1-δ)) :
    (Nat.floor ((p:ℝ)^δ)+2)*p < ((m+1)/2)^(B+1) := by
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp
  have hm0 : 0 < m := by
    have : 0 < (m:ℝ) := (Real.rpow_pos_of_pos hpR ε).trans_le hm
    exact_mod_cast this
  have hK := (floor_power_bounds _ hpδ).2
  have hL := (half_interval_parameters m hm0).2.2
  have hK3 : (Nat.floor ((p:ℝ)^δ):ℝ)+2 ≤ 3*(p:ℝ)^δ := by linarith
  have hbase : (p:ℝ)^ε/2 ≤ ((m+1)/2:ℕ) := (div_le_div_of_nonneg_right hm (by norm_num)).trans hL
  have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ (p:ℝ)^ε/2) hbase (B+1)
  have hdom := divisor_power_domination p ε δ (B+1) hpR (by simpa only [Nat.cast_add,Nat.cast_one] using hgap)
  have hleft := mul_le_mul_of_nonneg_right hK3 hpR.le
  have hfinal := hleft.trans_lt (hdom.trans_le hpower)
  exact_mod_cast hfinal

end KakeyaTwoScale
#print axioms KakeyaTwoScale.floor_power_bounds
#print axioms KakeyaTwoScale.frequency_floor_parameters
#print axioms KakeyaTwoScale.half_interval_parameters
#print axioms KakeyaTwoScale.divisor_power_domination
#print axioms KakeyaTwoScale.floor_divisor_cut
