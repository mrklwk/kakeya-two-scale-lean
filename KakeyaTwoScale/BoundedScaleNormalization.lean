module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

namespace KakeyaTwoScale

/-- Uniform normalization on a radius interval bounded away from zero.
A population cap and one positive volume floor suffice; positions do not enter. -/
theorem bounded_scale_normalization {V v M N delta p gamma e : ℝ}
    (hV : 0<V) (hv : 0<v) (hM : 0<M) (hN : 0≤N) (hdelta : 0<delta)
    (hd1 : delta≤1) (hp : 1≤p) (hg : 1≤gamma) (he : e≤0)
    (hcap : N≤M) (hfloor : v≤V) :
    N^(p-1)*V≤(M^(p-1)*v^(1-gamma))*delta^e*V^gamma := by
  have hVp : V≤v^(1-gamma)*V^gamma := by
    apply (Real.log_le_log_iff hV (by positivity)).mp
    rw [Real.log_mul (Real.rpow_pos_of_pos hv _).ne' (Real.rpow_pos_of_pos hV _).ne',
      Real.log_rpow hv,Real.log_rpow hV]
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hv hfloor) (show 0≤gamma-1 by linarith)
    nlinarith
  have hpow := Real.rpow_le_rpow hN hcap (show 0≤p-1 by linarith)
  have hd := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hd1 he
  calc
    _ ≤ M^(p-1)*V := mul_le_mul_of_nonneg_right hpow hV.le
    _ ≤ M^(p-1)*(v^(1-gamma)*V^gamma) :=
      mul_le_mul_of_nonneg_left hVp (Real.rpow_nonneg hM.le _)
    _ ≤ (M^(p-1)*v^(1-gamma))*delta^e*V^gamma := by
      have hh := mul_le_mul_of_nonneg_left hd
        (show 0≤M^(p-1)*v^(1-gamma)*V^gamma by positivity)
      nlinarith only [hh]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.bounded_scale_normalization
