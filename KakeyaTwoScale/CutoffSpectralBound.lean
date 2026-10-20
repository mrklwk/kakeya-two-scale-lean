module
public import KakeyaTwoScale.SmallFrequencyIndices
public import KakeyaTwoScale.IntervalCutoff

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

theorem cutoff_fourier_sq_bound (p m D : ℕ) [NeZero p] (C : ℝ) (hC : 0 ≤ C)
    (ψ : ZMod p → ℂ)
    (hdec : ∀ k, ‖normalizedFourier p ψ k‖ ≤ C*((m:ℝ)/(p:ℝ))/(1+frequencySize k*(m:ℝ)/(p:ℝ))^D)
    (U : ℝ) (hU : 0 ≤ U) (k : ZMod p) (hk : U ≤ frequencySize k) :
    ‖normalizedFourier p ψ k‖^2 ≤ (C*((m:ℝ)/(p:ℝ)))^2/(1+U*(m:ℝ)/(p:ℝ))^(2*D) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hf := frequencySize_nonneg k
  have hdu : 0 < 1+U*(m:ℝ)/(p:ℝ) := by positivity
  have hden : (1+U*(m:ℝ)/(p:ℝ))^D ≤ (1+frequencySize k*(m:ℝ)/(p:ℝ))^D := by
    apply pow_le_pow_left₀ hdu.le
    gcongr
  have hbound := (hdec k).trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hdu D) hden)
  have hs := pow_le_pow_left₀ (norm_nonneg (normalizedFourier p ψ k)) hbound 2
  convert hs using 1
  rw [div_pow,← pow_mul]
  rw [Nat.mul_comm D 2]

/-- Sum the actual dilated Fourier coefficients, separating the counted
small-frequency indices from the decaying tail. -/
theorem cutoff_dilation_spectral_bound (p m U D E : ℕ) [NeZero p]
    (J : Finset ℕ) (C : ℝ) (hC : 0 ≤ C) (ψ : ZMod p → ℂ)
    (hdec : ∀ k, ‖normalizedFourier p ψ k‖ ≤ C*((m:ℝ)/(p:ℝ))/(1+frequencySize k*(m:ℝ)/(p:ℝ))^D)
    (k : ZMod p) (hcount : (smallFrequencyIndices p U J k).card ≤ E) :
    ∑ j ∈ J, ‖normalizedFourier p ψ ((j:ZMod p)⁻¹*k)‖^2 ≤
      (C*((m:ℝ)/(p:ℝ)))^2*((E:ℝ)+(J.card:ℝ)/(1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*D)) := by
  let S := smallFrequencyIndices p U J k
  let V := (C*((m:ℝ)/(p:ℝ)))^2
  let t := V/(1+(U:ℝ)*(m:ℝ)/(p:ℝ))^(2*D)
  have hV : 0 ≤ V := sq_nonneg _
  have ht : 0 ≤ t := by dsimp [t,V]; positivity
  have hall (j : ℕ) : ‖normalizedFourier p ψ ((j:ZMod p)⁻¹*k)‖^2 ≤ V := by
    have h := cutoff_fourier_sq_bound p m D C hC ψ hdec 0 (by norm_num)
      ((j:ZMod p)⁻¹*k) (frequencySize_nonneg _)
    simpa only [zero_mul,zero_div,add_zero,one_pow,div_one] using h
  have hpoint (j : ℕ) (hj : j ∈ J) :
      ‖normalizedFourier p ψ ((j:ZMod p)⁻¹*k)‖^2 ≤ (if j ∈ S then V else 0)+t := by
    by_cases hs : j ∈ S
    · simp only [hs,ite_true]
      exact (hall j).trans (le_add_of_nonneg_right ht)
    · simp only [hs,ite_false,zero_add]
      have hk : (U:ℝ) ≤ frequencySize ((j:ZMod p)⁻¹*k) := by
        have hn : ¬frequencySize ((j:ZMod p)⁻¹*k) ≤ (U:ℝ) := by
          intro h
          exact hs (Finset.mem_filter.mpr ⟨hj,h⟩)
        exact (lt_of_not_ge hn).le
      exact cutoff_fourier_sq_bound p m D C hC ψ hdec U (Nat.cast_nonneg _) _ hk
  have hsum : (∑ j ∈ J, if j ∈ S then V else 0) = (S.card:ℝ)*V := by
    have hsub : S ⊆ J := Finset.filter_subset _ _
    rw [Finset.sum_ite_mem,Finset.inter_eq_right.mpr hsub]
    simp
  have hc : (S.card:ℝ) ≤ (E:ℝ) := by exact_mod_cast hcount
  calc
    _ ≤ ∑ j ∈ J, ((if j ∈ S then V else 0)+t) := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*V+(J.card:ℝ)*t := by rw [Finset.sum_add_distrib,hsum]; simp
    _ ≤ (E:ℝ)*V+(J.card:ℝ)*t := add_le_add (mul_le_mul_of_nonneg_right hc hV) le_rfl
    _ = _ := by dsimp [V,t]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cutoff_fourier_sq_bound
#print axioms KakeyaTwoScale.cutoff_dilation_spectral_bound
