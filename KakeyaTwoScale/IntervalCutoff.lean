module
public import KakeyaTwoScale.ScaledIntervalDecay
public import KakeyaTwoScale.PositiveIntervalSupport

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- The one-point cutoff handles all intervals too short for averaging. -/
theorem singleton_cutoff_decay (p m d : ℕ) [NeZero p] (hm0 : 0 < m) (hmp : m ≤ p)
    (hsmall : m ≤ 2*(d+1)) (k : ZMod p) :
    ‖normalizedFourier p (fun x => (intervalWeight p 1 x:ℂ)) k‖ ≤
      ((d:ℝ)+2)^(d+1)*((m:ℝ)/(p:ℝ))/(1+frequencySize k*(m:ℝ)/(p:ℝ))^(d+1) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hf := frequencySize_nonneg k
  have hhalf := frequencySize_le_half k
  have hmR : (m:ℝ) ≤ 2*((d:ℝ)+1) := by exact_mod_cast hsmall
  have ht : frequencySize k*(m:ℝ)/(p:ℝ) ≤ (d:ℝ)+1 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg m : (0:ℝ) ≤ m),
      mul_le_mul_of_nonneg_right hmR hp.le]
  have hden : 0 < 1+frequencySize k*(m:ℝ)/(p:ℝ) := by positivity
  have hpow : (1+frequencySize k*(m:ℝ)/(p:ℝ))^(d+1) ≤ ((d:ℝ)+2)^(d+1) := by
    exact pow_le_pow_left₀ hden.le (by linarith) _
  have hbase := intervalFourier_mass_bound p 1 (by omega) k
  norm_num only [Nat.cast_one] at hbase
  apply (le_div_iff₀ (pow_pos hden (d+1))).mpr
  calc
    _ ≤ (1/(p:ℝ))*(1+frequencySize k*(m:ℝ)/(p:ℝ))^(d+1) :=
      mul_le_mul_of_nonneg_right hbase (pow_nonneg hden.le _)
    _ ≤ (1/(p:ℝ))*((d:ℝ)+2)^(d+1) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ ((d:ℝ)+2)^(d+1)*((m:ℝ)/(p:ℝ)) := by
      have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm0
      have h := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ ((d:ℝ)+2)^(d+1)/(p:ℝ) by positivity)
      convert h using 1 <;> ring

/-- PZ's smooth cutoff, constructed for every interval 1≤m<p and every
positive integer decay order d+1. Explicit constants, zero frequency,
small m and integer rounding are all included. -/
theorem exists_interval_cutoff (p m d : ℕ) [NeZero p] (hm0 : 0 < m) (hmp : m < p) :
    ∃ ψ : ZMod p → ℝ,
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ x, x ∉ positiveFieldInterval p m → ψ x = 0) ∧
      ((m:ℝ)/(2*((d:ℝ)+1)) ≤ ∑ x, ψ x) ∧
      (∀ k, ‖normalizedFourier p (fun x => (ψ x:ℂ)) k‖ ≤
        ((d:ℝ)+2)^(d+1)*((m:ℝ)/(p:ℝ))/(1+frequencySize k*(m:ℝ)/(p:ℝ))^(d+1)) := by
  by_cases hm : 2*(d+1) ≤ m
  · obtain ⟨hq0,hqm,hprod,hscale⟩ := floor_cutoff_parameters m d hm
    have hqp : m/(d+1) ≤ p := hqm.trans hmp.le
    refine ⟨fun x => smoothInterval p (m/(d+1)) d (x-1),?_,?_,?_,?_⟩
    · intro x
      exact smoothInterval_bounds p (m/(d+1)) hq0 hqp d (x-1)
    · exact translate_interval_support p ((d+1)*(m/(d+1))) m hprod _
        (smoothInterval_support p (m/(d+1)) d)
    · rw [finite_sum_translate,smoothInterval_sum p (m/(d+1)) hq0 hqp]
      apply (div_le_iff₀ (by positivity : 0 < 2*((d:ℝ)+1))).mpr
      exact_mod_cast (show m ≤ m/(d+1)*(2*(d+1)) by nlinarith)
    · intro k
      dsimp only
      rw [normalizedFourier_translate_norm p (fun x => (smoothInterval p (m/(d+1)) d x:ℂ)) 1 k]
      exact smoothInterval_scaled_decay p (m/(d+1)) m d hq0 hqp hqm hscale k
  · have hp1 : 1 ≤ p := by omega
    refine ⟨fun x => intervalWeight p 1 (x-1),?_,?_,?_,?_⟩
    · intro x
      simp only [intervalWeight]
      split_ifs <;> norm_num
    · apply translate_interval_support p 1 m (by omega)
      intro x hx
      simp [intervalWeight,hx]
    · rw [finite_sum_translate]
      have hs : ∑ x : ZMod p, intervalWeight p 1 x = (1:ℝ) := by
        simp [intervalWeight,fieldInterval_card p 1 hp1]
      rw [hs]
      apply (div_le_iff₀ (by positivity : 0 < 2*((d:ℝ)+1))).mpr
      have hh : (m:ℝ) ≤ 2*((d:ℝ)+1) := by exact_mod_cast (show m ≤ 2*(d+1) by omega)
      simpa only [one_mul] using hh
    · intro k
      dsimp only
      rw [normalizedFourier_translate_norm p (fun x => (intervalWeight p 1 x:ℂ)) 1 k]
      exact singleton_cutoff_decay p m d hm0 hmp.le (by omega) k

end KakeyaTwoScale
#print axioms KakeyaTwoScale.singleton_cutoff_decay
#print axioms KakeyaTwoScale.exists_interval_cutoff
