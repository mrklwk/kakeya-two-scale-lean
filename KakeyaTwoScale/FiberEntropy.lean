module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Shannon entropy of a finite law, using natural logarithms and 0 log 0=0. -/
def finiteEntropy {J : Type*} (S : Finset J) (q : J → ℝ) : ℝ :=
  -∑ j ∈ S, q j * Real.log (q j)

def fiberPartition {J : Type*} (S : Finset J) (m : J → ℝ) (p : ℝ) : ℝ :=
  ∑ j ∈ S, (m j)^p

def fiberLaw {J : Type*} (S : Finset J) (m : J → ℝ) (p : ℝ) (j : J) : ℝ :=
  (m j)^p / fiberPartition S m p

variable {J : Type*} (S : Finset J) (m : J → ℝ) (p : ℝ)

theorem fiberPartition_pos (hne : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j) :
    0 < fiberPartition S m p :=
  Finset.sum_pos (fun j hj => Real.rpow_pos_of_pos (hm j hj) p) hne

theorem fiberLaw_pos (hne : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j) {j : J} (hj : j ∈ S) :
    0 < fiberLaw S m p j :=
  div_pos (Real.rpow_pos_of_pos (hm j hj) p) (fiberPartition_pos S m p hne hm)

theorem fiberLaw_sum (hne : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j) :
    ∑ j ∈ S, fiberLaw S m p j = 1 := by
  simp only [fiberLaw, ← Finset.sum_div]
  exact div_self (fiberPartition_pos S m p hne hm).ne'

/-- The exact entropy cancellation in the author's arithmetic appendix.
This is proved for the actual normalized law, not an entropy hypothesis. -/
theorem fiberLaw_entropy_identity (hne : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j) :
    finiteEntropy S (fiberLaw S m p) + p * ∑ j ∈ S, fiberLaw S m p j * Real.log (m j) =
      Real.log (fiberPartition S m p) := by
  have hz := fiberPartition_pos S m p hne hm
  have hl (j) (hj : j ∈ S) : Real.log (fiberLaw S m p j) =
      p * Real.log (m j) - Real.log (fiberPartition S m p) := by
    rw [fiberLaw, Real.log_div (Real.rpow_pos_of_pos (hm j hj) p).ne' hz.ne',
      Real.log_rpow (hm j hj)]
  unfold finiteEntropy
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ S, fiberLaw S m p j * Real.log (fiberPartition S m p) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hl j hj]
      ring
    _ = _ := by rw [← Finset.sum_mul, fiberLaw_sum S m p hne hm, one_mul]

/-- Exact source exponent specialization: p=theta/a=252/373 and beta=p+1. -/
theorem source_fiber_entropy_identity (hne : S.Nonempty) (hm : ∀ j ∈ S, 0 < m j) :
    finiteEntropy S (fiberLaw S m (252/373)) + ((625/373:ℝ)-1) *
      ∑ j ∈ S, fiberLaw S m (252/373) j * Real.log (m j) =
      Real.log (fiberPartition S m (252/373)) := by
  convert fiberLaw_entropy_identity S m (252/373) hne hm using 1; norm_num

/-- Support bound for a finite probability law, including zero masses. -/
theorem finiteEntropy_le_log_card (q : J → ℝ) (hq : ∀ j ∈ S, 0 ≤ q j)
    (hsum : ∑ j ∈ S, q j = 1) : finiteEntropy S q ≤ Real.log S.card := by
  have hne : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hsum
  have hN : 0 < (S.card : ℝ) := by exact_mod_cast hne.card_pos
  have hterm (j) (hj : j ∈ S) :
      (S.card : ℝ)*q j-1 ≤ (S.card : ℝ)*(q j*Real.log (q j)+q j*Real.log S.card) := by
    have hh := Real.self_sub_one_le_mul_log (mul_nonneg hN.le (hq j hj))
    by_cases hz : q j = 0
    · simp [hz]
    · rw [Real.log_mul hN.ne' hz] at hh
      nlinarith
  have hh : 0 ≤ (S.card : ℝ)*((∑ j ∈ S, q j*Real.log (q j))+Real.log S.card) := by
    calc
      0 = ∑ j ∈ S, ((S.card : ℝ)*q j-1) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
        simp
      _ ≤ ∑ j ∈ S, (S.card : ℝ)*(q j*Real.log (q j)+q j*Real.log S.card) :=
        Finset.sum_le_sum hterm
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hb := (mul_nonneg_iff_of_pos_left hN).mp hh
  unfold finiteEntropy
  linarith

/-- Entropy of the actual uniform law on a nonempty finite support. -/
theorem finiteEntropy_uniform (hne : S.Nonempty) :
    finiteEntropy S (fun _ => (S.card : ℝ)⁻¹) = Real.log S.card := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  simp only [finiteEntropy, Finset.sum_const, nsmul_eq_mul, Real.log_inv]
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fiberLaw_sum
#print axioms KakeyaTwoScale.fiberLaw_entropy_identity
#print axioms KakeyaTwoScale.source_fiber_entropy_identity

#print axioms KakeyaTwoScale.finiteEntropy_le_log_card
#print axioms KakeyaTwoScale.finiteEntropy_uniform
