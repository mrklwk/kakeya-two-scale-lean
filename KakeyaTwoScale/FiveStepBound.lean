module
public import KakeyaTwoScale.KatzTaoUpdate

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Rational upper targets leave a strictly positive loss at every genuine
update. The fifth target still lies strictly below 625/373. -/
def controlledExponent : ℕ → ℝ
  | 0 => 2
  | 1 => 17501/10000
  | 2 => 16932/10000
  | 3 => 16796/10000
  | 4 => 16763/10000
  | _ => 16755/10000

theorem controlledExponent_range {n : ℕ} (hn : n ≤ 5) :
    1 < controlledExponent n ∧ controlledExponent n ≤ 2 := by
  interval_cases n <;> norm_num [controlledExponent]

theorem controlledExponent_gap {n : ℕ} (hn : n < 5) :
    0 < controlledExponent (n+1)-realArithmeticStep (controlledExponent n) := by
  interval_cases n <;> norm_num [controlledExponent,realArithmeticStep]

theorem controlledExponent_final_margin :
    (625/373:ℝ)-controlledExponent 5 = 77/746000 := by
  norm_num [controlledExponent]

/-- Five applications of the proved update, carrying an actual finite
slope family and positive constant through every step. -/
theorem controlled_finiteSD (n : ℕ) (hn : n ≤ 5) :
    ∃ R : Finset ℚ, ∃ C : ℝ, 0 < C ∧ (∀ r ∈ R, r ≠ -1) ∧
      FiniteSDBound R (controlledExponent n) C := by
  induction n with
  | zero =>
    refine ⟨{0,1},1,by norm_num,?_,?_⟩
    · intro r hr
      simp only [Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> norm_num
    · exact finiteSD_two_slopes 0 1 (by norm_num)
  | succ n ih =>
    obtain ⟨R,C,hC,hproper,hSD⟩ := ih (by omega)
    have hr := controlledExponent_range (show n ≤ 5 by omega)
    obtain ⟨P,B,hB,hP,hbound⟩ := hSD.katzTao_update hproper hr.1 hr.2 hC
      (controlledExponent (n+1)-realArithmeticStep (controlledExponent n))
      (controlledExponent_gap (by omega))
    refine ⟨P,B,hB,hP,?_⟩
    have he : realArithmeticStep (controlledExponent n)+
        (controlledExponent (n+1)-realArithmeticStep (controlledExponent n)) = controlledExponent (n+1) := by ring
    rwa [he] at hbound

/-- The ordinary rational projection bound at the exact scalar exponent
required by the September 10 argument. This is not yet homogenization. -/
theorem finiteSD_625_373 :
    ∃ R : Finset ℚ, ∃ C : ℝ, 0 < C ∧ (∀ r ∈ R, r ≠ -1) ∧
      FiniteSDBound R (625/373) C := by
  obtain ⟨R,C,hC,hproper,hSD⟩ := controlled_finiteSD 5 (le_refl _)
  refine ⟨R,C,hC,hproper,?_⟩
  exact hSD.increase_exponent (hSD.slopes_nonempty (by norm_num [controlledExponent])) hC.le
    (by norm_num [controlledExponent])

end KakeyaTwoScale
#print axioms KakeyaTwoScale.controlledExponent_range
#print axioms KakeyaTwoScale.controlledExponent_gap
#print axioms KakeyaTwoScale.controlledExponent_final_margin
#print axioms KakeyaTwoScale.controlled_finiteSD
#print axioms KakeyaTwoScale.finiteSD_625_373
