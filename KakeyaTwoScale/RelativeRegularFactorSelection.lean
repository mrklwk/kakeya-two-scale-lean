module
public import KakeyaTwoScale.SmoothFiberRegularValues
public import KakeyaTwoScale.SignCellMassStability
public import KakeyaTwoScale.PolynomialEuclideanJacobian
public import KakeyaTwoScale.CoordinateNormalProjection

@[expose] public section

open Set MeasureTheory Filter MvPolynomial Metric
open scoped Topology ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- Construct independent constant shifts of actual base factors. Each shifted
cylinder is globally transverse to the unchanged smooth constraint fiber, and
all original sign-cell masses remain close. No good-parameter or Sard premise. -/
theorem exists_relative_regular_factor_shifts {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {d s : ℕ} (f : E → F) (value : F)
    (hf : ∀ x, f x=value → ContDiffAt ℝ ∞ f x)
    (hA : ∀ x, f x=value → (fderiv ℝ f x).range=⊤)
    (π : E →L[ℝ] EuclideanSpace ℝ (Fin d))
    (q : Fin s → MvPolynomial (Fin d) ℝ) (hq : ∀ i, q i ≠ 0)
    (w : EuclideanSpace ℝ (Fin d) → ℝ) (hw : Integrable w)
    (ε ζ : ℝ) (hε : 0 < ε) (hζ : 0 < ζ) :
    ∃ c : Fin s → ℝ,
      (∀ i, |c i| < ε) ∧
      (∀ i, q i+C (c i) ≠ 0) ∧
      (∀ i, (q i+C (c i)).totalDegree ≤ (q i).totalDegree) ∧
      (∀ b : Fin s → Bool,
        |(∫ x in polynomialSignCell (fun i => q i+C (c i)) b, w x) -
          (∫ x in polynomialSignCell q b, w x)| < ζ) ∧
      (∀ i x, f x=value → eval (π x) (q i+C (c i))=0 →
        (fderiv ℝ (fun y => (f y,eval (π y) (q i+C (c i)))) x).range=⊤) := by
  classical
  have hm := eventually_all_shiftedSignCell_masses_close q hq w hw ζ hζ
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hm
  let η := min ε r / 2
  have hη : 0 < η := half_pos (lt_min hε hr)
  have hηε : η < ε := (half_lt_self (lt_min hε hr)).trans_le (min_le_left _ _)
  have hηr : η < r := (half_lt_self (lt_min hε hr)).trans_le (min_le_right _ _)
  have hchoice : ∀ i : Fin s, ∃ t ∈ Ioo (-η) η, eval (0 : Fin d → ℝ) (q i) ≠ t ∧
      ∀ x, f x=value → eval (π x) (q i)=t →
        (fderiv ℝ (fun y => (f y,eval (π y) (q i)-t)) x).range=⊤ := by
    intro i
    have hg : ∀ x, f x=value → ContDiffAt ℝ ∞ (fun y => eval (π y) (q i)) x :=
      fun x _ => (finite_polynomial_eval_contDiff (q i) ∞).contDiffAt.comp x π.contDiff.contDiffAt
    by_cases hv : eval (0 : Fin d → ℝ) (q i) ≤ 0
    · obtain ⟨t,ht,hreg⟩ := smooth_fiber_exists_transverse_level f _ value hf hg hA
        (a := 0) (b := η) hη
      exact ⟨t,⟨by linarith [ht.1],ht.2⟩,ne_of_lt (lt_of_le_of_lt hv ht.1),hreg⟩
    · obtain ⟨t,ht,hreg⟩ := smooth_fiber_exists_transverse_level f _ value hf hg hA
        (a := -η) (b := 0) (by linarith)
      exact ⟨t,⟨ht.1,by linarith [ht.2]⟩,ne_of_gt (lt_trans ht.2 (lt_of_not_ge hv)),hreg⟩
  choose t ht hne hreg using hchoice
  let c : Fin s → ℝ := fun i => -t i
  have hcη : ∀ i, |c i| < η := by
    intro i
    simpa only [c,abs_neg,abs_lt,mem_Ioo] using ht i
  have hnorm : ‖c‖ ≤ η := (pi_norm_le_iff_of_nonneg hη.le).mpr (fun i =>
    by simpa only [Real.norm_eq_abs] using (hcη i).le)
  have hcb : c ∈ ball 0 r := by
    simpa only [mem_ball,dist_zero_right] using hnorm.trans_lt hηr
  refine ⟨c,fun i => (hcη i).trans hηε,?_,?_,hball hcb,?_⟩
  · intro i hz
    have he := congrArg (eval (0 : Fin d → ℝ)) hz
    have ht' : eval (0 : Fin d → ℝ) (q i) = t i := by
      simpa only [map_add,eval_C,map_zero,c,add_neg_eq_zero] using he
    exact hne i ht' 
  · intro i
    exact (totalDegree_add _ _).trans (by simp)
  · intro i x hx hzero
    have hval : eval (π x) (q i)=t i := by
      simpa only [map_add,eval_C,c,add_neg_eq_zero] using hzero
    simpa only [map_add,eval_C,c,sub_eq_add_neg] using hreg i x hx hval

/-- Actual polynomial complete-intersection specialization. Only the incoming
constraint rank is assumed; all new transverse constant shifts are constructed.
Every factor remains a polynomial of the SAME base coordinates. -/
theorem exists_polynomial_relative_regular_factor_shifts {b c s : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hP : ∀ x, rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤)
    (q : Fin s → MvPolynomial (Fin b) ℝ) (hq : ∀ i, q i ≠ 0)
    (w : EuclideanSpace ℝ (Fin b) → ℝ) (hw : Integrable w)
    (ε ζ : ℝ) (hε : 0 < ε) (hζ : 0 < ζ) :
    ∃ shift : Fin s → ℝ,
      (∀ i, |shift i| < ε) ∧
      (∀ i, q i+C (shift i) ≠ 0) ∧
      (∀ i, (q i+C (shift i)).totalDegree ≤ (q i).totalDegree) ∧
      (∀ sign : Fin s → Bool,
        |(∫ x in polynomialSignCell (fun i => q i+C (shift i)) sign, w x) -
          (∫ x in polynomialSignCell q sign, w x)| < ζ) ∧
      (∀ i x, rectangularPolynomialMap P x=0 →
        eval (coordinateBaseProjection x) (q i+C (shift i))=0 →
        (fderiv ℝ (fun y => (rectangularPolynomialMap P y,
          eval (coordinateBaseProjection y) (q i+C (shift i)))) x).range=⊤) := by
  exact exists_relative_regular_factor_shifts (rectangularPolynomialMap P) 0
    (fun _ _ => (rectangularPolynomialMap_contDiff P ∞).contDiffAt)
    hP coordinateBaseProjection q hq w hw ε ζ hε hζ

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_relative_regular_factor_shifts

#print axioms KakeyaTwoScale.exists_polynomial_relative_regular_factor_shifts
