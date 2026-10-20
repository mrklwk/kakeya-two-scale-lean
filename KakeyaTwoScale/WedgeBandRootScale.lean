module
public import KakeyaTwoScale.FiniteRootIntegral

@[expose] public section

namespace KakeyaTwoScale

theorem wedge_band_root_weight {k : ℕ} {B theta : ℝ}
    (hk : 0<k) (hB : 1<B) (htheta : 0<theta) :
    ((2*theta)^((k:ℝ)/B))^(B/((k:ℝ)*(B-1)))=
      (2:ℝ)^(1/(B-1))*theta^(1/(B-1)) := by
  rw [←Real.rpow_mul (by positivity : 0≤2*theta)]
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hB0 : B≠0 := by linarith
  have he : ((k:ℝ)/B)*(B/((k:ℝ)*(B-1)))=1/(B-1) := by field_simp
  rw [he,Real.mul_rpow (by norm_num : (0:ℝ)≤2) htheta.le]

theorem dyadic_rate_scale (q : ℕ) (rate e : ℝ) :
    (2:ℝ)^(rate*(q:ℝ))*(((2:ℝ)^q)⁻¹)^e=(((2:ℝ)^q)⁻¹)^(e-rate) := by
  have he : (((2:ℝ)^q)⁻¹)^(-rate)=(2:ℝ)^(rate*(q:ℝ)) := by
    rw [Real.inv_rpow (by positivity : (0:ℝ)≤2^q),Real.rpow_neg (by positivity : (0:ℝ)≤2^q),inv_inv,
      ←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  rw [←he,←Real.rpow_add (by positivity : (0:ℝ)<((2:ℝ)^q)⁻¹)]
  congr 1
  ring

theorem published_band_scale_exponent {B d loss : ℝ} (hB : 1<B) :
    (B-d)/(B-1)-B/(B-1)*loss=B/(B-1)*(1-d/B-loss) := by
  have hB0 : B≠0 := by linarith
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.wedge_band_root_weight
#print axioms KakeyaTwoScale.dyadic_rate_scale
