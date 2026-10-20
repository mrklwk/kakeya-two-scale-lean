module
public import KakeyaTwoScale.IntegerModelSequences

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

theorem log_rate_comparable (n x y : ℕ → ℝ) (a c C : ℝ)
    (hn : Tendsto n atTop atTop) (hc : 0 < c) (hC : 0 < C)
    (hpos : ∀ᶠ i in atTop, 0 < n i ∧ 0 < x i ∧ 0 < y i)
    (hbound : ∀ᶠ i in atTop, c*x i ≤ y i ∧ y i ≤ C*x i)
    (hx : Tendsto (fun i => Real.log (x i)/n i) atTop (𝓝 a)) :
    Tendsto (fun i => Real.log (y i)/n i) atTop (𝓝 a) := by
  have hlo : Tendsto (fun i => Real.log c/n i+Real.log (x i)/n i) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds.div_atTop hn).add hx
  have hhi : Tendsto (fun i => Real.log C/n i+Real.log (x i)/n i) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds.div_atTop hn).add hx
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hpos,hbound] with i hi hb
    have h := Real.log_le_log (mul_pos hc hi.2.1) hb.1
    rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hi.2.1)] at h
    simpa only [add_div] using div_le_div_of_nonneg_right h hi.1.le
  · filter_upwards [hpos,hbound] with i hi hb
    have h := Real.log_le_log hi.2.2 hb.2
    rw [Real.log_mul (ne_of_gt hC) (ne_of_gt hi.2.1)] at h
    simpa only [add_div] using div_le_div_of_nonneg_right h hi.1.le

theorem log_rate_pos_atTop (n x : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hn : Tendsto n atTop atTop) (hpos : ∀ᶠ i in atTop, 0 < n i ∧ 0 < x i)
    (hx : Tendsto (fun i => Real.log (x i)/n i) atTop (𝓝 a)) :
    Tendsto x atTop atTop := by
  have hlow := hx.eventually (Ioi_mem_nhds (show a/2 < a by linarith))
  have hlog : Tendsto (fun i => Real.log (x i)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hn.const_mul_atTop (show 0 < a/2 by positivity))
    filter_upwards [hpos,hlow] with i hi hh
    exact ((lt_div_iff₀ hi.1).mp hh).le
  apply (Real.tendsto_exp_atTop.comp hlog).congr'
  filter_upwards [hpos] with i hi
  exact Real.exp_log hi.2

theorem log_rate_eventually_lt (n x y : ℕ → ℝ) (a b : ℝ) (hab : a < b)
    (hpos : ∀ᶠ i in atTop, 0 < n i ∧ 0 < x i ∧ 0 < y i)
    (hx : Tendsto (fun i => Real.log (x i)/n i) atTop (𝓝 a))
    (hy : Tendsto (fun i => Real.log (y i)/n i) atTop (𝓝 b)) :
    ∀ᶠ i in atTop, x i < y i := by
  have hlow := hx.eventually (Iio_mem_nhds (show a < (a+b)/2 by linarith))
  have hhi := hy.eventually (Ioi_mem_nhds (show (a+b)/2 < b by linarith))
  filter_upwards [hpos,hlow,hhi] with i hi hl hh
  have he : Real.log (x i) < Real.log (y i) := (div_lt_div_iff_of_pos_right hi.1).mp (hl.trans hh)
  exact (Real.log_lt_log_iff hi.2.1 hi.2.2).mp he

end KakeyaTwoScale
#print axioms KakeyaTwoScale.log_rate_comparable
#print axioms KakeyaTwoScale.log_rate_pos_atTop
#print axioms KakeyaTwoScale.log_rate_eventually_lt
