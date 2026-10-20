module
public import KakeyaTwoScale.SmoothInterval

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Interpolation of the mass and reciprocal-frequency bounds with an
explicit coefficient. The zero frequency is included, not divided by. -/
theorem intervalFourier_scaled_bound (p q m D : ℕ) [NeZero p] (hq : q ≤ p)
    (hm : m ≤ 2*D*q) (k : ZMod p) :
    ‖normalizedFourier p (fun x => (intervalWeight p q x:ℂ)) k‖ ≤
      ((q:ℝ)/(p:ℝ))*(((D:ℝ)+1)/(1+frequencySize k*(m:ℝ)/(p:ℝ))) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hf := frequencySize_nonneg k
  let A := ‖normalizedFourier p (fun x => (intervalWeight p q x:ℂ)) k‖
  have hA : A ≤ (q:ℝ)/(p:ℝ) := intervalFourier_mass_bound p q hq k
  have hfreq : A*(2*frequencySize k) ≤ 1 := by
    by_cases hk : k = 0
    · subst k
      simp [frequencySize]
    · have hfpos := frequencySize_pos k hk
      exact (le_div_iff₀ (by positivity : 0 < 2*frequencySize k)).mp
        (intervalFourier_decay p q hq k hk)
  have hmR : (m:ℝ) ≤ 2*(D:ℝ)*(q:ℝ) := by exact_mod_cast hm
  have hprod : A*frequencySize k*(m:ℝ) ≤ (D:ℝ)*(q:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hfreq (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    nlinarith
  change A ≤ _
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 1+frequencySize k*(m:ℝ)/(p:ℝ))).mpr
  calc
    A*(1+frequencySize k*(m:ℝ)/(p:ℝ)) = A+(A*frequencySize k*(m:ℝ))/(p:ℝ) := by ring
    _ ≤ (q:ℝ)/(p:ℝ)+((D:ℝ)*(q:ℝ))/(p:ℝ) :=
      add_le_add hA (div_le_div_of_nonneg_right hprod hp.le)
    _ = (q:ℝ)/(p:ℝ)*((D:ℝ)+1) := by ring

/-- Full natural-power Fourier decay for the actual repeated-average cutoff. -/
theorem smoothInterval_scaled_decay (p q m d : ℕ) [NeZero p]
    (hq0 : 0 < q) (hq : q ≤ p) (hqm : q ≤ m) (hm : m ≤ 2*(d+1)*q) (k : ZMod p) :
    ‖normalizedFourier p (fun x => (smoothInterval p q d x:ℂ)) k‖ ≤
      ((d:ℝ)+2)^(d+1)*((m:ℝ)/(p:ℝ))/(1+frequencySize k*(m:ℝ)/(p:ℝ))^(d+1) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast NeZero.pos p
  have hf := frequencySize_nonneg k
  have hbase := intervalFourier_scaled_bound p q m (d+1) hq hm k
  have hb : 0 ≤ (((d+1:ℕ):ℝ)+1)/(1+frequencySize k*(m:ℝ)/(p:ℝ)) := by positivity
  have h := smoothInterval_fourier_bound p q hq0 k _ hb hbase d
  refine h.trans ?_
  have hqR : (q:ℝ)/(p:ℝ) ≤ (m:ℝ)/(p:ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hqm) hp.le
  calc
    _ ≤ ((m:ℝ)/(p:ℝ))*((((d+1:ℕ):ℝ)+1)/(1+frequencySize k*(m:ℝ)/(p:ℝ)))^(d+1) :=
      mul_le_mul_of_nonneg_right hqR (pow_nonneg hb _)
    _ = _ := by push_cast; rw [div_pow]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.intervalFourier_scaled_bound
#print axioms KakeyaTwoScale.smoothInterval_scaled_decay
