module
public import KakeyaTwoScale.ActualSeedLossLedger

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- All scale-independent terms of the actual seed loss. Orientation size,
partition parameter, ambient dimension and cardinality slope are fixed first. -/
def seedLogConstant (m s n k A M : ℕ) : ℝ :=
  2*Real.log (2*(m:ℝ))+Real.log (s+1:ℕ)+2*Real.log (M+2:ℕ)+
  k*Real.log 3+n*Real.log (2*(A+n+5)+1:ℕ)+2*(k+1)*Real.log (M+1:ℕ)

namespace ActualSynchronizedBufferedSeed
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {I : BufferedStageInput b c k A B Lh J s depth T C O}

/-- Uniform scale ledger for a literal constructed seed. The original tuple
and height calendars are explicit; no data-dependent constants are absorbed. -/
theorem log_loss_le (S : ActualSynchronizedBufferedSeed I) (M q : ℕ)
    (hs : 2  ≤  s) (hdepth : depth  ≤  B/(s-1)+1)
    (hB : B  ≤  M*q) (hLh : Lh  ≤  q) :
    Real.log S.loss  ≤
      ((M:ℝ)*Real.log (2*(S.orientations.card:ℝ))/((s:ℝ)-1))*(q:ℝ) +
      seedLogConstant S.orientations.card s (b+c) k A M +
      (4*k+4:ℝ)*Real.log (q+1:ℕ) := by
  have hm : 1  ≤  S.orientations.card := Finset.card_pos.mpr S.orientations_nonempty
  have hmR : (1:ℝ)  ≤  S.orientations.card := by exact_mod_cast hm
  have hlogm : 0  ≤  Real.log (2*(S.orientations.card:ℝ)) := Real.log_nonneg (by linarith)
  have hden : (0:ℝ)<(s:ℝ)-1 := by
    have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hBR : (B:ℝ) ≤ (M:ℝ)*q := by exact_mod_cast hB
  have hd := sharp_depth_real_bound B s depth hs hdepth
  have hd' : (depth:ℝ)+1  ≤  (M:ℝ)*q/((s:ℝ)-1)+2 := by
    have := div_le_div_of_nonneg_right hBR hden.le
    linarith
  have hmterm := mul_le_mul_of_nonneg_right hd' hlogm
  have hdNat : depth+1  ≤  (M+2)*(q+1) := by
    have hdiv := Nat.div_le_self B (s-1)
    nlinarith
  have hdlog : Real.log (depth+1:ℕ)  ≤  Real.log (M+2:ℕ)+Real.log (q+1:ℕ) := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(depth+1:ℕ))
      (by exact_mod_cast hdNat : ((depth+1:ℕ):ℝ)  ≤  ((M+2:ℕ):ℝ)*(q+1:ℕ))
    rwa [Real.log_mul (by positivity) (by positivity)] at h
  have hBlog : Real.log (B+1:ℕ)  ≤  Real.log (M+1:ℕ)+Real.log (q+1:ℕ) := by
    have hn : B+1  ≤  (M+1)*(q+1) := by nlinarith
    have h := Real.log_le_log (by positivity : (0:ℝ)<(B+1:ℕ))
      (by exact_mod_cast hn : ((B+1:ℕ):ℝ)  ≤  ((M+1:ℕ):ℝ)*(q+1:ℕ))
    rwa [Real.log_mul (by positivity) (by positivity)] at h
  have hLlog : Real.log (Lh+1:ℕ)  ≤  Real.log (q+1:ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hLh 1)
  rw [S.log_loss]
  unfold seedLogConstant
  push_cast
  push_cast at hmterm hdlog hBlog hLlog
  simp only [div_eq_mul_inv] at hmterm ⊢
  nlinarith [mul_le_mul_of_nonneg_left hLlog (show (0:ℝ) ≤ 2*k by positivity),
    mul_le_mul_of_nonneg_left hBlog (show (0:ℝ) ≤ 2*(k+1) by positivity)]

end ActualSynchronizedBufferedSeed
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualSynchronizedBufferedSeed.log_loss_le
