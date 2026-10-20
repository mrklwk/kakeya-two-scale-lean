module
public import KakeyaTwoScale.CharacterSeparation
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def intervalWeight (p q : ℕ) (x : ZMod p) : ℝ := if x ∈ fieldInterval p q then 1 else 0

theorem intervalFourier_eq_geom (p q : ℕ) [NeZero p] (hq : q ≤ p) (k : ZMod p) :
    normalizedFourier p (fun x => (intervalWeight p q x:ℂ)) k =
      (p:ℂ)⁻¹*∑ i ∈ Finset.range q, (ZMod.stdAddChar (-k))^i := by
  unfold normalizedFourier
  rw [ZMod.dft_apply]
  congr 1
  simp only [intervalWeight,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,smul_eq_mul,mul_one,mul_zero]
  rw [Finset.sum_ite_mem,Finset.univ_inter]
  unfold fieldInterval
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← AddChar.map_nsmul_eq_pow,nsmul_eq_mul,mul_neg]
  · intro i hi j hj he
    have hi' := lt_of_lt_of_le (Finset.mem_range.mp hi) hq
    have hj' := lt_of_lt_of_le (Finset.mem_range.mp hj) hq
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hi',Nat.mod_eq_of_lt hj'] using hv

theorem intervalFourier_mass_bound (p q : ℕ) [NeZero p] (hq : q ≤ p) (k : ZMod p) :
    ‖normalizedFourier p (fun x => (intervalWeight p q x:ℂ)) k‖ ≤ (q:ℝ)/(p:ℝ) := by
  rw [intervalFourier_eq_geom p q hq,norm_mul,norm_inv,Complex.norm_natCast]
  have hs : ‖∑ i ∈ Finset.range q, (ZMod.stdAddChar (-k))^i‖ ≤ (q:ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range q, ‖(ZMod.stdAddChar (-k))^i‖ := norm_sum_le _ _
      _ = (q:ℝ) := by simp [norm_pow,AddChar.norm_apply]
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg p))

/-- The interval's reciprocal-frequency Fourier bound, with its exact
balanced-frequency constant. No primality assumption is required. -/
theorem intervalFourier_decay (p q : ℕ) [NeZero p] (hq : q ≤ p)
    (k : ZMod p) (hk : k ≠ 0) :
    ‖normalizedFourier p (fun x => (intervalWeight p q x:ℂ)) k‖ ≤ 1/(2*frequencySize k) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hf := frequencySize_pos k hk
  let z := ZMod.stdAddChar (-k)
  let S := ∑ i ∈ Finset.range q, z^i
  have hz : ‖z‖ = 1 := AddChar.norm_apply _ _
  have hg : ‖S‖*‖1-z‖ ≤ 2 := by
    calc
      _ = ‖1-z^q‖ := by rw [← norm_mul]; exact congrArg norm (geom_sum_mul_neg z q)
      _ ≤ ‖(1:ℂ)‖+‖z^q‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one,norm_pow,hz]; norm_num
  have hs := stdAddChar_neg_separation k
  have hh : ‖S‖*(4*frequencySize k/(p:ℝ)) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hs (norm_nonneg S)).trans hg
  rw [intervalFourier_eq_geom p q hq,norm_mul,norm_inv,Complex.norm_natCast]
  change (p:ℝ)⁻¹*‖S‖ ≤ _
  apply (le_div_iff₀ (by positivity : 0 < 2*frequencySize k)).mpr
  have he : ((p:ℝ)⁻¹*‖S‖)*(2*frequencySize k) = (‖S‖*(4*frequencySize k/(p:ℝ)))/2 := by ring
  rw [he]
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.intervalFourier_eq_geom
#print axioms KakeyaTwoScale.intervalFourier_mass_bound
#print axioms KakeyaTwoScale.intervalFourier_decay
