module
public import KakeyaTwoScale.OptimizedRootObjective

@[expose] public section

namespace KakeyaTwoScale

theorem root_loss_power_le {k : ℕ} (hk : 1≤k) {rho U R : ℝ}
    (hrho : 1≤rho) (hU : 0≤U) (hR : rho*U≤R) :
    rho^(k-1)*U^k≤R^k := by
  have hp : rho^(k-1)≤rho^k := pow_le_pow_right₀ hrho (by omega)
  exact (mul_le_mul_of_nonneg_right hp (pow_nonneg hU k)).trans
    (by rw [←mul_pow]; exact pow_le_pow_left₀ (mul_nonneg (by linarith) hU) hR k)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.root_loss_power_le
