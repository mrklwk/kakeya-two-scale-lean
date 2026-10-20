module
public import KakeyaTwoScale.RestrictedIndexCounting

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

theorem eventually_nat_rpow_ge (r C : ℝ) (hr : 0 < r) :
    ∀ᶠ p : ℕ in atTop, C ≤ (p:ℝ)^r :=
  tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hr).eventually (eventually_ge_atTop C))

theorem eventually_nat_rpow_gt (r C : ℝ) (hr : 0 < r) :
    ∀ᶠ p : ℕ in atTop, C < (p:ℝ)^r :=
  tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hr).eventually (eventually_gt_atTop C))

theorem eventually_nat_log_le_rpow (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ p : ℕ in atTop, Real.log (p:ℝ) ≤ c*(p:ℝ)^r := by
  have h := tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_atTop hr).def hc)
  filter_upwards [h] with p hp
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) r)] at hp
  exact (le_abs_self _).trans hp

/-- Quantitative thresholds depending only on p, not on the interval m.
Their strict exponent gaps are exposed explicitly. -/
theorem pz_uniform_power_thresholds (ε δ A c : ℝ) (B D N : ℕ)
    (hε : 0 < ε) (hδ : 0 < δ) (hgap : 0 < ε*((B:ℝ)+1)-1-δ)
    (htail : 0 < 2*(D:ℝ)*δ-1) (hδε : δ < ε) (hA : 0 < A) (hc : 0 < c)
    (hB : 0 < B) :
    ∀ᶠ p : ℕ in atTop,
      2 ≤ p ∧ (2:ℝ) ≤ (p:ℝ)^δ ∧
      max (max 2 (N:ℝ)) (10*A) ≤ (p:ℝ)^ε ∧
      3*(2:ℝ)^(B+1) < (p:ℝ)^(ε*((B:ℝ)+1)-1-δ) ∧
      (2:ℝ)^(2*D+1) ≤ (p:ℝ)^(2*(D:ℝ)*δ-1) ∧
      Real.log (p:ℝ) ≤ min (c/2) (c/(20*A*(B:ℝ)))*(p:ℝ)^(ε-δ) := by
  have hBc : 0 < (B:ℝ) := by exact_mod_cast hB
  have hcoeff : 0 < min (c/2) (c/(20*A*(B:ℝ))) := by positivity
  filter_upwards [eventually_ge_atTop (2:ℕ),eventually_nat_rpow_ge δ 2 hδ,
    eventually_nat_rpow_ge ε (max (max 2 (N:ℝ)) (10*A)) hε,
    eventually_nat_rpow_gt (ε*((B:ℝ)+1)-1-δ) (3*(2:ℝ)^(B+1)) hgap,
    eventually_nat_rpow_ge (2*(D:ℝ)*δ-1) ((2:ℝ)^(2*D+1)) htail,
    eventually_nat_log_le_rpow (ε-δ) _ (sub_pos.mpr hδε) hcoeff] with p h1 h2 h3 h4 h5 h6
  exact ⟨h1,h2,h3,h4,h5,h6⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_nat_rpow_ge
#print axioms KakeyaTwoScale.eventually_nat_rpow_gt
#print axioms KakeyaTwoScale.eventually_nat_log_le_rpow
#print axioms KakeyaTwoScale.pz_uniform_power_thresholds
