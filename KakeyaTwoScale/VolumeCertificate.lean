module
public import KakeyaTwoScale.Exponents
public import KakeyaTwoScale.LogLoss

@[expose] public section

/-! Analytic certificate for the narrow branch. This is not a Kakeya theorem:
geometry must produce these bounds and identify D with upper Minkowski dimension. -/
open Filter
noncomputable section
namespace KakeyaTwoScale

def transferExponent (n k : ℝ) : ℝ :=
  20*omega n + gamma n k + (2*a-1)*(n-1)

/-- The exact product occurring in the two-scale transfer inequality. -/
def volumeProduct (fine coarse : ℕ → ℝ) (q : ℕ) : ℝ :=
  fine q * (coarse q)^(2+a/theta)

/-- Separate fine/coarse neighborhood estimates imply the product bound
used by the transfer argument. All signs and constants are explicit. -/
theorem volumeProduct_upper (fine coarse : ℕ → ℝ) (q : ℕ)
    (s Cf Cc : ℝ) (_hf0 : 0 ≤ fine q) (hc0 : 0 ≤ coarse q)
    (hCf : 0 < Cf) (hCc : 0 < Cc)
    (hf : fine q ≤ Cf*Real.exp (-Real.log 2*20*s*q))
    (hc : coarse q ≤ Cc*Real.exp (-Real.log 2*s*q)) :
    volumeProduct fine coarse q ≤ (Cf*Cc^(2+a/theta))*
      Real.exp (-Real.log 2*(denominator*s)*q) := by
  have hb : (0:ℝ) ≤ 2+a/theta := by norm_num [a,theta]
  have hp := Real.rpow_le_rpow hc0 hc hb
  unfold volumeProduct
  calc
    fine q * coarse q^(2+a/theta) ≤
        (Cf*Real.exp (-Real.log 2*20*s*q))*
          (Cc*Real.exp (-Real.log 2*s*q))^(2+a/theta) :=
      mul_le_mul hf hp (Real.rpow_nonneg hc0 _) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hCc.le (Real.exp_pos _).le, ← Real.exp_mul]
      calc
        _ = (Cf*Cc^(2+a/theta))*
          (Real.exp (-Real.log 2*20*s*q)*
            Real.exp ((-Real.log 2*s*q)*(2+a/theta))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; unfold denominator; ring

/-- Upper volume exponents with arbitrary epsilon loss and a lower transfer
bound with polynomial-in-q loss imply the narrow numerical endpoint.
The lower bound need hold only frequently; the upper bound holds eventually. -/
theorem narrow_endpoint_of_volume_certificate
    (n k D : ℝ) (hn : 0 ≤ n) (hk : k ≤ n/2)
    (fine coarse : ℕ → ℝ)
    (upper : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ q : ℕ in atTop, volumeProduct fine coarse q ≤
        C*Real.exp (-Real.log 2*(denominator*(n-D-ε))*q))
    (lower : ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ,
      ∃ᶠ q : ℕ in atTop,
        c*Real.exp (-Real.log 2*transferExponent n k*q)/(q:ℝ)^L ≤
          volumeProduct fine coarse q) :
    (597/1000 : ℝ)*n < D := by
  obtain ⟨c,hc,L,hl⟩ := lower
  have he : ∀ ε : ℝ, 0 < ε →
      denominator*(n-D)-denominator*ε ≤ transferExponent n k := by
    intro ε hε
    obtain ⟨C,hC,hu⟩ := upper ε hε
    have h := exponent_le_of_dyadic_envelopes (volumeProduct fine coarse)
      (denominator*(n-D-ε)) (transferExponent n k) c C L hc hC
      (hl.and_eventually hu)
    nlinarith
  have hpos : 0 < denominator := by norm_num [denominator,a,theta]
  exact narrow_endpoint n k D hn hk
    (le_of_forall_positive_loss _ _ denominator hpos he)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.narrow_endpoint_of_volume_certificate

#print axioms KakeyaTwoScale.volumeProduct_upper
