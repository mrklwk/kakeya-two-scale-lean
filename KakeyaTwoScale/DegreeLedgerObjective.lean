module
public import KakeyaTwoScale.ActualDegreeLedger
public import KakeyaTwoScale.TerminalDegreeConstraints

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Decreasing real exponent weights; unlike the actual degree parameter,
the coefficient is allowed to become negative. -/
def degreeWeightedLog (v : ℝ) : List ℝ → ℝ
  | [] => 0
  | D::ds => v*Real.log D+degreeWeightedLog (v-1) ds

theorem degreeLedger_length (b : ℕ) (P G : ℝ) (ds : List ℝ) :
    (degreeLedger b P G ds).length=ds.length+1 := by
  induction ds generalizing b P G with
  | nil => rfl
  | cons D ds ih => simpa only [degreeLedger,List.length_cons] using congrArg (·+1) (ih (b-1) (P*D) (G*D^(b:ℝ)))

/-- Exact finite sum identity for the executed prefix, with no sign restriction
on log D. The default degree one is never used inside the requested prefix. -/
theorem degreeWeightedLog_take (v : ℝ) (ds : List ℝ) (r : ℕ) (hr : r≤ds.length) :
    degreeWeightedLog v (ds.take r)=
      ∑i∈Finset.range r, (v-i)*Real.log (ds[i]?.getD 1) := by
  induction r generalizing v ds with
  | zero => simp [degreeWeightedLog]
  | succ r ih =>
    cases ds with
    | nil => simp at hr
    | cons D ds =>
      simp only [List.take_succ_cons,degreeWeightedLog]
      rw [ih (v-1) ds (by simpa using hr),Finset.sum_range_succ']
      simp only [List.getElem?_cons_zero,Option.getD_some,Nat.cast_zero,sub_zero,
        List.getElem?_cons_succ,Nat.cast_add,Nat.cast_one]
      rw [add_comm (v*Real.log D)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring

/-- The actual degree-ledger ratio is the exact optimizer exponential.
Initial product and grain factors are displayed, not normalized away. -/
theorem degreeLedger_ratio (b k : ℕ) (P G : ℝ) (ds : List ℝ) (r : ℕ)
    (hr : r≤ds.length) (hb : r≤b) (hG : 0<G) (hd : ∀D∈ds, 0<D) :
    let E := (degreeLedger b P G ds)[r]'(by rw [degreeLedger_length]; omega)
    E.1^k/E.2=(P^k/G)*Real.exp (-degreeWeightedLog ((b:ℝ)-k) (ds.take r)) := by
  induction r generalizing b P G ds with
  | zero => cases ds <;> simp [degreeLedger,degreeWeightedLog]
  | succ r ih =>
    cases ds with
    | nil => simp at hr
    | cons D ds =>
      have hD : 0<D := hd D (by simp)
      have hb0 : 1≤b := by omega
      have hh := ih (b-1) (P*D) (G*D^(b:ℝ)) ds (by simpa using hr) (by omega)
        (by positivity) (fun d h => hd d (by simp [h]))
      have hidx : r<(degreeLedger (b-1) (P*D) (G*D^(b:ℝ)) ds).length := by
        rw [degreeLedger_length]
        simp only [List.length_cons] at hr
        omega
      change (degreeLedger (b-1) (P*D) (G*D^(b:ℝ)) ds)[r].1^k /
        (degreeLedger (b-1) (P*D) (G*D^(b:ℝ)) ds)[r].2 = _
      rw [hh]
      simp only [List.take_succ_cons,degreeWeightedLog,Nat.cast_sub hb0,Nat.cast_one]
      have he : (b:ℝ)-1-k=(b:ℝ)-k-1 := by ring
      rw [he,neg_add,Real.exp_add]
      have hexp : Real.exp (-(((b:ℝ)-k)*Real.log D))=D^k/D^b := by
        rw [show -(((b:ℝ)-k)*Real.log D)=Real.log D*((k:ℝ)-b) by ring,
          ←Real.rpow_def_of_pos hD,Real.rpow_sub hD,Real.rpow_natCast,Real.rpow_natCast]
      rw [hexp,Real.rpow_natCast,mul_pow]
      field_simp

/-- The existing objective uses the same zero-indexed coefficients. -/
theorem degreeWeightedLog_objective (m : ℕ) (ds : List ℝ) (r : ℕ) (hr : r≤ds.length) :
    degreeWeightedLog m (ds.take r)=
      degreeObjectiveLog m r (fun i => Real.log (ds[i]?.getD 1)) := by
  exact degreeWeightedLog_take m ds r hr

end KakeyaTwoScale
#print axioms KakeyaTwoScale.degreeLedger_ratio
#print axioms KakeyaTwoScale.degreeWeightedLog_objective
