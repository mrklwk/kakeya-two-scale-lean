module
public import KakeyaTwoScale.ActualTerminalObjective

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A joint root count band converts the root alpha mass directly to its
k-fold tuple scale. No retained marginal or retained-beta comparison is used. -/
theorem root_band_mass_power {k : ℕ} (hk : 2≤k)
    {theta v mu mass rho R : ℝ} (htheta : 0≤theta) (hv : 0≤v)
    (hmu : 0 < mu) (hrho : 0<rho)
    (hlower : v*(mu^k)^(1/((k-1:ℕ):ℝ))≤ mass)
    (han : theta*(mass/rho)^(k-1)≤R) :
    theta*mu^k*v^(k-1)≤R*rho^(k-1) := by
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg (mul_nonneg hv (Real.rpow_nonneg (pow_nonneg hmu.le _) _)) hrho.le)
      (div_le_div_of_nonneg_right hlower hrho.le) (k-1)) htheta
  have hpow : ((mu^k)^(1/((k-1:ℕ):ℝ)))^(k-1)=mu^k := by
    rw [one_div,Real.rpow_inv_natCast_pow (pow_nonneg hmu.le _) (by omega)]
  rw [div_pow,mul_pow,hpow] at hh
  have hx := (div_le_iff₀ (pow_pos hrho (k-1))).mp
    (show theta*(v^(k-1)*mu^k)/rho^(k-1)≤R by
      simpa only [mul_div_assoc] using hh.trans han)
  convert hx using 1
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.root_band_mass_power
