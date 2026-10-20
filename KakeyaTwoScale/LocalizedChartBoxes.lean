module
public import KakeyaTwoScale.LocalizedFixedInterceptBall

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

theorem positive_chart_slope_bound {n : ℕ} (h : Fin (n+1))
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1) (hh : 1/(n+2:ℝ)≤u h) (j : Fin n) :
    |chartSlope h u j|≤n+2 := by
  have hN : 0<(n+2:ℝ) := by positivity
  have hp : 0<u h := (one_div_pos.mpr hN).trans_le hh
  have hc : |u (h.succAbove j)|≤1 := by
    simpa only [Real.norm_eq_abs,hu] using PiLp.norm_apply_le u (h.succAbove j)
  have hm := (div_le_iff₀ hN).mp hh
  rw [chartSlope,abs_div,abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (by nlinarith)

theorem localized_base_dist {n : ℕ} (c u center w : EuclideanSpace ℝ (Fin (n+1)))
    (ell delta C : ℝ) (hu : ‖u‖=1) (hell : ell≤1) (hd : delta≤1) (hC : 0≤C)
    (hw : w∈flatCylinder c u ell delta) (hwb : dist w center<C*ell) :
    dist c center<C+2 := by
  obtain ⟨t,ht,htL,_,he⟩ := hw
  rw [sub_add_eq_sub_sub] at he
  have hid : w-c=t • u+(w-c-t • u) := by abel
  have hn := norm_add_le (t • u) (w-c-t • u)
  rw [← hid,norm_smul,Real.norm_eq_abs,abs_of_pos ht,hu,mul_one] at hn
  have hcw : dist c w<ell+delta := by rw [dist_comm,dist_eq_norm]; linarith
  have hc := mul_le_mul_of_nonneg_left hell hC
  have htri := dist_triangle c w center
  linarith

theorem localized_chart_intercept_box {n : ℕ} (h : Fin (n+1))
    (c u center w : EuclideanSpace ℝ (Fin (n+1))) (ell delta C : ℝ)
    (hu : ‖u‖=1) (hh : 1/(n+2:ℝ)≤u h) (hell : ell≤1) (hd : delta≤1) (hC : 0≤C)
    (hw : w∈flatCylinder c u ell delta) (hwb : dist w center<C*ell) (j : Fin n) :
    (chartIntercept h (c-center) u 0 j)^2<((C+3)*(n+3:ℝ)+1)^2 := by
  have hdist := localized_base_dist c u center w ell delta C hu hell hd hC hw hwb
  have hcoord (i : Fin (n+1)) : |(c-center) i|<C+2 :=
    (show |(c-center) i|≤dist c center by
      simpa only [dist_eq_norm,Real.norm_eq_abs] using PiLp.norm_apply_le (c-center) i).trans_lt hdist
  have hs := positive_chart_slope_bound h u hu hh j
  have hm := mul_le_mul (le_of_lt (hcoord h)) hs (abs_nonneg _) (by linarith : 0≤C+2)
  have ha := abs_add_le ((c-center) (h.succAbove j)) (-(c-center) h*chartSlope h u j)
  rw [abs_mul,abs_neg] at ha
  have habs : |chartIntercept h (c-center) u 0 j|<((C+3)*(n+3:ℝ)+1) := by
    unfold chartIntercept
    rw [zero_sub]
    have := hcoord (h.succAbove j)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr habs

theorem perturbed_chart_slope_box {n : ℕ} (h : Fin (n+1))
    (u : EuclideanSpace ℝ (Fin (n+1))) (delta C : ℝ)
    (hu : ‖u‖=1) (hh : 1/(n+2:ℝ)≤u h) (hd : delta≤1) (hC : 0≤C)
    (v : Fin n→ℝ) (hv : v∈ball (chartSlope h u) (delta/(16*(n+2:ℝ)*(C+3)))) (j : Fin n) :
    (v j)^2<(n+3:ℝ)^2 := by
  have hden : 0<16*(n+2:ℝ)*(C+3) := by positivity
  have hr : delta/(16*(n+2:ℝ)*(C+3))<1 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : |v j-chartSlope h u j|<1 :=
    (show |v j-chartSlope h u j|≤dist v (chartSlope h u) by
      simpa only [Real.dist_eq] using dist_le_pi_dist v (chartSlope h u) j).trans_lt
      ((show dist v (chartSlope h u)<_ from hv).trans hr)
  have hs := positive_chart_slope_bound h u hu hh j
  have ha := abs_add_le (v j-chartSlope h u j) (chartSlope h u j)
  have habs : |v j|<n+3 := by rw [sub_add_cancel] at ha; linarith
  simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr habs

end KakeyaTwoScale
#print axioms KakeyaTwoScale.localized_chart_intercept_box
#print axioms KakeyaTwoScale.perturbed_chart_slope_box
