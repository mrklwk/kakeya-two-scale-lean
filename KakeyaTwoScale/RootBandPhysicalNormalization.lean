module
public import KakeyaTwoScale.RootBandMassPower

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem root_band_scale_identity (n k : ℕ) (hk : 1≤k) {delta : ℝ} (hd : 0<delta) :
    delta^((k:ℝ)-(n+1))*(delta^n)^k=(delta^(n+1))^(k-1) := by
  simp only [←Real.rpow_natCast]
  rw [←Real.rpow_mul hd.le,←Real.rpow_mul hd.le,←Real.rpow_add hd]
  congr 1
  rw [Nat.cast_sub hk]
  push_cast
  ring

/-- Exact physical volume and population normalization of the root analytic
bound. The scale exponent is k-d in ambient d=n+1. -/
theorem root_band_physical_normalization (n k : ℕ) (hk : 1≤k)
    (theta mu v delta F T : ℝ) (N : Fin k→ℝ) (hd : 0<delta)
    (han : theta*mu^k*v^(k-1)≤F*(∏j, N j)/Real.exp T) :
    theta*mu^(k:ℝ)*(v*delta^(n+1))^((k:ℝ)-1) ≤
      F*delta^((k:ℝ)-(n+1))*(∏j, delta^n*N j)/Real.exp T := by
  have hh := mul_le_mul_of_nonneg_right han (pow_nonneg (pow_nonneg hd.le (n+1)) (k-1))
  have hp : (∏j : Fin k, delta^n*N j)=(delta^n)^k*∏j, N j := by
    rw [Finset.prod_mul_distrib]
    simp
  have hs := root_band_scale_identity n k hk hd
  rw [Real.rpow_natCast,show (k:ℝ)-1=((k-1:ℕ):ℝ) by rw [Nat.cast_sub hk]; norm_num,
    Real.rpow_natCast,mul_pow,hp]
  calc
    _ ≤ (F*(∏j, N j)/Real.exp T)*(delta^(n+1))^(k-1) := by
      convert hh using 1
      ring
    _ = F*(delta^((k:ℝ)-(n+1))*(delta^n)^k)*(∏j, N j)/Real.exp T := by rw [hs]; ring
    _ = _ := by ring

/-- Effective length in the optimizer is exactly the already proved archive
normalization, using positive scaled populations. -/
theorem root_band_effective_length (n k : ℕ) (hk : 0<k)
    (v mu delta : ℝ) (N : Fin k→ℝ) (hd : 0<delta) (hN : ∀j, 0<N j) :
    (v*delta^(n+1))*mu/(∏j, delta^n*N j)^(1/(k:ℝ))=
      v*mu*delta/(∏j, N j)^(1/(k:ℝ)) := by
  have hp : (∏j : Fin k, delta^n*N j)=(delta^n)^k*∏j, N j := by
    rw [Finset.prod_mul_distrib]
    simp
  rw [hp,Real.mul_rpow (by positivity) (Finset.prod_pos (fun j _ => hN j)).le]
  have hroot : ((delta^n)^k)^(1/(k:ℝ))=delta^n := by
    rw [one_div,Real.pow_rpow_inv_natCast (pow_nonneg hd.le _) (by omega)]
  rw [hroot,pow_succ]
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.root_band_physical_normalization
#print axioms KakeyaTwoScale.root_band_effective_length
