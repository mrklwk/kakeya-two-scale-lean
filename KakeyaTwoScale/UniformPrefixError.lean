module
public import KakeyaTwoScale.PrefixErrorEnvelope

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Choose precision before the calendar-dependent constants. Afterwards one
threshold absorbs those fixed constants simultaneously for every prefix. -/
theorem uniform_prefix_error_absorption (m : ℕ) (epsilon : ℝ) (he : 0<epsilon) :
    ∃ eta : ℝ, 0<eta ∧ eta≤epsilon ∧ ∀ K C : ℝ, ∃ Q : ℕ, ∀ q : ℕ, Q≤q →
      ∀ r : ℕ, r ≤ m →
      Real.log K+(r:ℝ)*Real.log C+(r:ℝ)*(r+1)/2*(eta*(q:ℝ)*Real.log 2)≤
        epsilon*(q:ℝ)*Real.log 2 := by
  let eta := epsilon/(2*(m+1:ℝ)^2)
  have heta : 0<eta := by dsimp [eta]; positivity
  have heta_le : eta≤epsilon := by
    dsimp [eta]
    apply (div_le_iff₀ (by positivity : 0<2*(m+1:ℝ)^2)).mpr
    have hm : (0:ℝ)≤ m := Nat.cast_nonneg _
    have hh : 1≤2*(m+1:ℝ)^2 := by nlinarith
    exact le_mul_of_one_le_right he.le hh
  refine ⟨eta,heta,heta_le,?_⟩
  intro K C
  let F := |Real.log K|+(m:ℝ)*|Real.log C|
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Q,hQ⟩ := exists_nat_gt (F/(epsilon*Real.log 2/2))
  refine ⟨Q,?_⟩
  intro q hq r hr
  have hrR : (r:ℝ)≤ m := by exact_mod_cast hr
  have hqR : (Q:ℝ)≤q := by exact_mod_cast hq
  have hF : F≤epsilon*Real.log 2/2*(q:ℝ) := by
    have hh := (div_lt_iff₀ (by positivity : 0<epsilon*Real.log 2/2)).mp (hQ.trans_le hqR)
    linarith
  have hfixed : Real.log K+(r:ℝ)*Real.log C≤F := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self (Real.log C)) (Nat.cast_nonneg (α:=ℝ) r)
    have hm := mul_le_mul_of_nonneg_right hrR (abs_nonneg (Real.log C))
    have hk := le_abs_self (Real.log K)
    dsimp [F]
    linarith
  have hcoef : (r:ℝ)*(r+1)/2≤(m+1:ℝ)^2 := by
    have hm : (0:ℝ)≤ m := Nat.cast_nonneg _
    have hh := mul_le_mul hrR (by linarith : (r:ℝ)+1≤ m+1) (by positivity : (0:ℝ)≤r+1) hm
    nlinarith
  have hetaEq : (m+1:ℝ)^2*eta=epsilon/2 := by dsimp [eta]; field_simp
  have heps : (r:ℝ)*(r+1)/2*eta≤epsilon/2 := by
    simpa only [hetaEq] using mul_le_mul_of_nonneg_right hcoef heta.le
  have hh := mul_le_mul_of_nonneg_right heps (show 0≤(q:ℝ)*Real.log 2 by positivity)
  nlinarith only [hh,hfixed,hF]

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

/-- Insert an actual simultaneous envelope into the previously chosen scalar
budget. This theorem reads the literal archive upper factors. -/
theorem long_prefix_error_absorbed
    (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (hP : 0<P) (hU : 1≤U) (eta epsilon : ℝ) (q r : ℕ) (hr : r≤H.drops)
    (K C : ℝ) (hC : 0<C)
    (henv : ∀E∈H.countLedger, H.loss*E.upper≤(2:ℝ)^(eta*(q:ℝ)))
    (hbudget : Real.log K+(r:ℝ)*Real.log C+(r:ℝ)*(r+1)/2*(eta*(q:ℝ)*Real.log 2)≤
      epsilon*(q:ℝ)*Real.log 2) :
    Real.log K+(r:ℝ)*Real.log (C*(H.loss*(H.entryAt r hr).upper))+
      (∑i∈Finset.range r, (i:ℝ)*Real.log (H.upperAt i)) ≤ epsilon*(q:ℝ)*Real.log 2 :=
  (H.long_prefix_error_le hP hU eta q henv r hr K C hC).trans hbudget

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_prefix_error_absorption
#print axioms KakeyaTwoScale.ActualBufferedArchive.long_prefix_error_absorbed
