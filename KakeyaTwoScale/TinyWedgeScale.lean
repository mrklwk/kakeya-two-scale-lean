module
public import KakeyaTwoScale.TinyWedgeIntegral

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- Exact scalar normalization of the δ^d tiny-wedge tail to the published
volume-sum power. Sharp sphere packing and a lower tube-volume comparison
enter with their true exponents; neither is replaced by ambient-ball packing.
All constants are explicit and independent of δ, population and volume. -/
theorem tiny_wedge_scale_normalization {d B δ N V K c : ℝ}
    (hd : 1 < d) (hB : 1 < B) (hBd : B ≤ d)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) (hV : 0 < V)
    (hK : 0 < K) (hc : 0 < c)
    (hpack : N ≤ K * δ ^ (1 - d))
    (hvol : c * N * δ ^ (d - 1) ≤ V) :
    δ ^ (d / (B - 1)) * N ^ (B / (B - 1) - 1) * V ≤
      (K ^ ((d - B) / ((B - 1) * (d - 1))) * c ^ (-(1 / (d - 1)))) *
        δ ^ ((B / (B - 1)) * (1 - d / B)) * V ^ (d / (d - 1)) := by
  have hBm : 0 < B - 1 := by linarith
  have hdm : 0 < d - 1 := by linarith
  have hB0 : 0 < B := by linarith
  let e := (d - B) / ((B - 1) * (d - 1))
  let v := 1 / (d - 1)
  have he : 0 ≤ e := div_nonneg (sub_nonneg.mpr hBd) (mul_pos hBm hdm).le
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpacklog := Real.log_le_log hN hpack
  rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hδ _).ne', Real.log_rpow hδ] at hpacklog
  have hvollog := Real.log_le_log (show 0 < c * N * δ ^ (d - 1) by positivity) hvol
  rw [Real.log_mul (mul_pos hc hN).ne' (Real.rpow_pos_of_pos hδ _).ne',
    Real.log_mul hc.ne' hN.ne', Real.log_rpow hδ] at hvollog
  have hp := mul_le_mul_of_nonneg_left hpacklog he
  have hq := mul_le_mul_of_nonneg_left hvollog hv
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hcut : 0 ≤ d / (B - 1) - 1 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hBm).mpr
    linarith
  have hcutlog := mul_nonpos_of_nonneg_of_nonpos hcut hlogδ
  have hexp : (B / (B - 1)) * (1 - d / B) = (1 - d) * e := by
    dsimp [e]
    field_simp
    ring
  have hpop : B / (B - 1) - 1 = e + v := by
    dsimp [e, v]
    field_simp
    ring
  have hvolume : d / (d - 1) = 1 + v := by
    dsimp [v]
    field_simp
    ring
  have hvdim : v * (d - 1) = 1 := by dsimp [v]; field_simp
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  repeat' rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_rpow hδ, Real.log_rpow hN,
    Real.log_rpow hV, Real.log_rpow hK, Real.log_rpow hc]
  change d / (B - 1) * Real.log δ + (B / (B - 1) - 1) * Real.log N + Real.log V ≤
    (e * Real.log K + -v * Real.log c) + (B / (B - 1) * (1 - d / B)) * Real.log δ +
      d / (d - 1) * Real.log V
  rw [hexp, hpop, hvolume]
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tiny_wedge_scale_normalization
