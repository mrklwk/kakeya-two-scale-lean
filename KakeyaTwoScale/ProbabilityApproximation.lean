module
public import KakeyaTwoScale.EmpiricalSDEntropy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped BigOperators Topology

def roundedCount (q : ℝ) (k : ℕ) : ℕ := Nat.floor ((k:ℝ)*q)

theorem roundedCount_scaled_tendsto (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun k : ℕ => (roundedCount q k:ℝ)/(k:ℝ)) atTop (𝓝 q) := by
  have hn : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun k : ℕ => q-1/(k:ℝ)) atTop (𝓝 q) := by
    simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hn) :
      Tendsto (fun k : ℕ => q-1/(k:ℝ)) atTop (𝓝 (q-0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    apply (le_div_iff₀ hkR).mpr
    have h := Nat.lt_floor_add_one ((k:ℝ)*q)
    have he : (q-1/(k:ℝ))*(k:ℝ) = (k:ℝ)*q-1 := by field_simp
    rw [he]
    unfold roundedCount
    exact le_of_lt (by linarith)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    apply (div_le_iff₀ hkR).mpr
    have h := Nat.floor_le (mul_nonneg hkR.le hq)
    exact le_trans h (by ring_nf; exact le_refl _)

def normalizedCounts {A : Type*} [Fintype A] (c : A → ℕ) (a : A) : ℝ :=
  (c a:ℝ)/(∑ b, (c b:ℝ))

theorem normalizedCounts_sum {A : Type*} [Fintype A] (c : A → ℕ)
    (hc : 0 < ∑ a, c a) : ∑ a, normalizedCounts c a = 1 := by
  unfold normalizedCounts
  rw [← Finset.sum_div]
  apply div_self
  have h : (0:ℝ) < ∑ a, (c a:ℝ) := by exact_mod_cast hc
  exact ne_of_gt h

/-- Rounded counts become positive in total before normalization. -/
theorem roundedCount_total_eventually_pos {A : Type*} [Fintype A] (q : A → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hsum : ∑ a, q a = 1) :
    ∀ᶠ k : ℕ in atTop, 0 < ∑ a, roundedCount (q a) k := by
  have hh := tendsto_finsetSum Finset.univ (fun a _ => roundedCount_scaled_tendsto (q a) (hq a))
  rw [hsum] at hh
  have hp := hh.eventually (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hp] with k hk
  rw [← Finset.sum_div,← Nat.cast_sum] at hk
  have hnum : (0:ℝ) < (∑ a, roundedCount (q a) k) :=
    (div_pos_iff.mp hk).resolve_right (by intro h; have h0 : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith [h.2]) |>.1
  exact_mod_cast hnum

/-- Every finite probability law, including zero masses, is a limit of
normalized integer-count laws. No positivity or rationality approximation
hypothesis is supplied. -/
theorem normalized_roundedCounts_tendsto {A : Type*} [Fintype A] (q : A → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hsum : ∑ a, q a = 1) :
    Tendsto (fun k : ℕ => normalizedCounts (fun a => roundedCount (q a) k)) atTop (𝓝 q) := by
  apply tendsto_pi_nhds.mpr
  intro a
  have ht := tendsto_finsetSum Finset.univ (fun b _ => roundedCount_scaled_tendsto (q b) (hq b))
  rw [hsum] at ht
  have hh := (roundedCount_scaled_tendsto (q a) (hq a)).div ht (by norm_num)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  simp only [Pi.div_apply]
  rw [← Finset.sum_div]
  unfold normalizedCounts
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.roundedCount_scaled_tendsto
#print axioms KakeyaTwoScale.normalizedCounts_sum
#print axioms KakeyaTwoScale.roundedCount_total_eventually_pos
#print axioms KakeyaTwoScale.normalized_roundedCounts_tendsto
