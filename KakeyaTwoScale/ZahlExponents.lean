module
public import KakeyaTwoScale.TwoScaleCertificate

@[expose] public section

/-! Algebra needed to convert the precise multilinear norm estimate into
the broad volume estimate. This file does not assume or prove that estimate. -/
noncomputable section
namespace KakeyaTwoScale

theorem zahlB_sub_k (n k : ℝ) (hn : n ≠ 0) :
    zahlB n k - k = (n-k)*(n-k+1)/(2*n) := by
  unfold zahlB
  field_simp
  ring

theorem zahlB_ge_k {n k : ℝ} (hn : 0 < n) (hk : k ≤ n) :
    k ≤ zahlB n k := by
  have h := zahlB_sub_k n k hn.ne'
  have : 0 ≤ (n-k)*(n-k+1)/(2*n) := by positivity
  linarith

theorem zahlB_gt_one {n k : ℝ} (hn : 0 < n) (hklo : 2 ≤ k) (hkhi : k ≤ n) :
    1 < zahlB n k := by
  have := zahlB_ge_k hn hkhi
  linarith

theorem zahlB_le_n {n k : ℝ} (hn : 0 < n) (hklo : 1 ≤ k) (hkhi : k ≤ n) :
    zahlB n k ≤ n := by
  unfold zahlB
  apply (div_le_iff₀ (by positivity)).2
  have h : 0 ≤ (n-k)*(n+k-1) :=
    mul_nonneg (sub_nonneg.mpr hkhi) (by linarith)
  nlinarith

/-- The norm exponent has conjugate exponent B, so the support-volume
factor is V^(1/B); the explicit positivity is used by Holder. -/
theorem zahl_holder_conjugacy {B : ℝ} (hB : 1 < B) :
    1 < B/(B-1) ∧ (B/(B-1))⁻¹ + B⁻¹ = 1 := by
  have hpos : 0 < B-1 := by linarith
  constructor
  · exact (lt_div_iff₀ hpos).2 (by linarith)
  · field_simp
    ring

/-- After Holder and raising to power B, the fine radius exponent is
n-B+B*epsilon and the coarse transversality exponent is k-1. -/
theorem zahl_broad_power_exponent (n k B ε : ℝ) (hB : B ≠ 0) :
    B*((n-1)-(n*(B-1)/B)+(k-1)/(20*B)+ε) =
      n-(B-(k-1)/20)+B*ε := by
  field_simp
  ring

theorem zahl_loss_reparameterization {B η : ℝ} (hB : 0 < B) (hη : 0 < η) :
    0 < η/B ∧ B*(η/B) = η := by
  exact ⟨div_pos hη hB, mul_div_cancel₀ η hB.ne'⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.zahlB_sub_k
#print axioms KakeyaTwoScale.zahlB_ge_k
#print axioms KakeyaTwoScale.zahlB_gt_one
#print axioms KakeyaTwoScale.zahlB_le_n
#print axioms KakeyaTwoScale.zahl_holder_conjugacy
#print axioms KakeyaTwoScale.zahl_broad_power_exponent
#print axioms KakeyaTwoScale.zahl_loss_reparameterization
