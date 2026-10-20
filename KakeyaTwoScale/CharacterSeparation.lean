module
public import KakeyaTwoScale.NormalizedFourier
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped ComplexConjugate

def frequencySize {p : ℕ} (k : ZMod p) : ℝ := |(k.valMinAbs:ℝ)|

theorem frequencySize_nonneg {p : ℕ} (k : ZMod p) : 0 ≤ frequencySize k := abs_nonneg _

theorem frequencySize_pos {p : ℕ} (k : ZMod p) (hk : k ≠ 0) : 0 < frequencySize k := by
  apply abs_pos.mpr
  exact_mod_cast (mt k.valMinAbs_eq_zero.mp hk)

theorem frequencySize_le_half {p : ℕ} [NeZero p] (k : ZMod p) :
    2*frequencySize k ≤ (p:ℝ) := by
  have h := k.valMinAbs_mem_Ioc
  have h1 : -(p:ℝ) < (k.valMinAbs:ℝ)*2 := by exact_mod_cast h.1
  have h2 : (k.valMinAbs:ℝ)*2 ≤ (p:ℝ) := by exact_mod_cast h.2
  unfold frequencySize
  rcases le_total 0 (k.valMinAbs:ℝ) with ha | ha
  · rw [abs_of_nonneg ha]; linarith
  · rw [abs_of_nonpos ha]; linarith

/-- Exact sine lower bound for the standard character, using the balanced
integer representative and valid also at zero frequency. -/
theorem stdAddChar_separation {p : ℕ} [NeZero p] (k : ZMod p) :
    4*frequencySize k/(p:ℝ) ≤ ‖1-ZMod.stdAddChar k‖ := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hpi := Real.pi_pos
  let a : ℝ := k.valMinAbs
  have ha : 2*|a| ≤ (p:ℝ) := frequencySize_le_half k
  have ht : |Real.pi*a/(p:ℝ)| ≤ Real.pi/2 := by
    rw [abs_div,abs_mul,abs_of_pos hpi,abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hs := Real.mul_abs_le_abs_sin ht
  have hc : ZMod.stdAddChar k = Complex.exp (Complex.I*(2*Real.pi*a/(p:ℝ):ℝ)) := by
    rw [← k.coe_valMinAbs,ZMod.stdAddChar_coe]
    dsimp only [a]
    push_cast
    congr 1
    ring
  rw [norm_sub_rev,hc,Complex.norm_exp_I_mul_ofReal_sub_one]
  have he : (2*Real.pi*a/(p:ℝ))/2 = Real.pi*a/(p:ℝ) := by ring
  rw [he,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [abs_div,abs_mul,abs_of_pos hpi,abs_of_pos hp] at hs
  have he2 : (2/Real.pi)*(Real.pi*|a|/(p:ℝ)) = 2*frequencySize k/(p:ℝ) := by
    dsimp only [frequencySize,a]
    field_simp
  rw [he2] at hs
  calc
    4*frequencySize k/(p:ℝ) = 2*(2*frequencySize k/(p:ℝ)) := by ring
    _ ≤ 2*|Real.sin (Real.pi*a/(p:ℝ))| := mul_le_mul_of_nonneg_left hs (by norm_num)

theorem stdAddChar_neg_separation {p : ℕ} [NeZero p] (k : ZMod p) :
    4*frequencySize k/(p:ℝ) ≤ ‖1-ZMod.stdAddChar (-k)‖ := by
  have he : 1-ZMod.stdAddChar (-k) = conj (1-ZMod.stdAddChar k) := by
    rw [map_sub,map_one,AddChar.map_neg_eq_inv,AddChar.inv_apply_eq_conj]
  rw [he,Complex.norm_conj]
  exact stdAddChar_separation k

end KakeyaTwoScale
#print axioms KakeyaTwoScale.frequencySize_pos
#print axioms KakeyaTwoScale.frequencySize_le_half
#print axioms KakeyaTwoScale.stdAddChar_separation

#print axioms KakeyaTwoScale.stdAddChar_neg_separation
