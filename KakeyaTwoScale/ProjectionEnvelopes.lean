module
public import KakeyaTwoScale.ModelRateAlgebra

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology BigOperators

def projectionLogMax {R V F P} (S : IntegerModelSequence R V F P) (hR : R.Nonempty) (i : ℕ) : ℝ :=
  R.sup' hR (fun r => Real.log (((S.G i).image (integerProjection r)).card:ℝ)/(S.n i:ℝ))

def projectionEnvelope {R V F P} (S : IntegerModelSequence R V F P) (hR : R.Nonempty) (i : ℕ) : ℝ :=
  Real.exp ((S.n i:ℝ)*projectionLogMax S hR i)

theorem projectionEnvelope_bound {R V F P} (S : IntegerModelSequence R V F P) (hR : R.Nonempty)
    (i : ℕ) (r : ℚ) (hr : r ∈ R) :
    (((S.G i).image (integerProjection r)).card:ℝ) ≤ projectionEnvelope S hR i := by
  have hn : (0:ℝ) < S.n i := by exact_mod_cast S.length_pos i
  have hp : (0:ℝ) < ((S.G i).image (integerProjection r)).card := by
    exact_mod_cast Finset.card_pos.mpr ((S.nonempty i).image _)
  have h := (div_le_iff₀ hn).mp (Finset.le_sup'
    (fun r => Real.log (((S.G i).image (integerProjection r)).card:ℝ)/(S.n i:ℝ)) hr)
  have hh : Real.log (((S.G i).image (integerProjection r)).card:ℝ) ≤ (S.n i:ℝ)*projectionLogMax S hR i := by
    dsimp [projectionLogMax]
    nlinarith only [h]
  have he := Real.exp_le_exp.mpr hh
  rwa [Real.exp_log hp] at he

theorem projectionEnvelope_rate {R V F P} (S : IntegerModelSequence R V F P) (hR : R.Nonempty) :
    Tendsto (fun i => Real.log (projectionEnvelope S hR i)/(S.n i:ℝ)) atTop (𝓝 (R.sup' hR P)) := by
  have h := Tendsto.finset_sup'_nhds_apply hR (fun r hr => S.projection_rate r hr)
  apply h.congr'
  apply Eventually.of_forall
  intro i
  dsimp [projectionEnvelope,projectionLogMax]
  rw [Real.log_exp]
  have hn : (S.n i:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (S.length_pos i)
  field_simp

def modelProjectionConstant (R : Finset ℚ) : ℕ :=
  (∑ c ∈ R.image slopeCoefficients, (2*coefficientWidth c.1 c.2+1))*(R.sup modelingFactor)

theorem modelProjectionConstant_pos (R : Finset ℚ) (hR : R.Nonempty) : 0 < modelProjectionConstant R := by
  obtain ⟨r,hr⟩ := hR
  have hc : slopeCoefficients r ∈ R.image slopeCoefficients := Finset.mem_image.mpr ⟨r,hr,rfl⟩
  have hsum := Finset.single_le_sum (fun c (_ : c ∈ R.image slopeCoefficients) =>
    Nat.zero_le (2*coefficientWidth c.1 c.2+1)) hc
  have hd := Finset.le_sup (f := modelingFactor) hr
  have hp := modelingFactor_pos r
  exact Nat.mul_pos (by omega) (hp.trans_le hd)

theorem slopeRectificationBudget_pos (R : Finset ℚ) (hR : R.Nonempty) : 0 < slopeRectificationBudget R := by
  obtain ⟨r,hr⟩ := hR
  exact (rectificationFactor_pos r).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr)

def modelBudgetEnvelope {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (i : ℕ) : ℝ :=
  ((T.p i-1:ℕ):ℝ)*(modelLength S T i:ℝ)*(modelProjectionConstant R:ℝ)*projectionEnvelope S hR i

/-- A proved upper envelope for the ACTUAL modular projection budget.
No lower projection-growth hypothesis is used. -/
theorem modelBudgetEnvelope_bound {R V F P} {S : IntegerModelSequence R V F P}
    {T : ModelPrimeSequence S} (U : StableModelSequence S T) (hR : R.Nonempty) :
    ∀ᶠ i in atTop, (samplingProjectionBudget (T.p i) (modelLength S T i) (U.H i) (R.image slopeCoefficients):ℝ) ≤
      modelBudgetEnvelope S T hR i := by
  filter_upwards [U.projections] with i hi
  let E := projectionEnvelope S hR i
  let D := R.sup modelingFactor
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hpoint (c : ℤ × ℤ) (hc : c ∈ R.image slopeCoefficients) :
      (((U.H i).image (modularLinearForm (T.p i) c.1 c.2)).card:ℝ) ≤ (D:ℝ)*E := by
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
    calc
      _ ≤ (((S.G i).image (integerProjection r)).card:ℝ)*(modelingFactor r:ℝ) := by exact_mod_cast hi r hr
      _ ≤ E*(modelingFactor r:ℝ) := mul_le_mul_of_nonneg_right (projectionEnvelope_bound S hR i r hr) (Nat.cast_nonneg _)
      _ ≤ E*(D:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.le_sup (f := modelingFactor) hr) hE
      _ = _ := mul_comm _ _
  have hsum : (∑ c ∈ R.image slopeCoefficients,
      ((2*coefficientWidth c.1 c.2+1:ℕ):ℝ)*(((U.H i).image (modularLinearForm (T.p i) c.1 c.2)).card:ℝ)) ≤
      (modelProjectionConstant R:ℝ)*E := by
    calc
      _ ≤ ∑ c ∈ R.image slopeCoefficients, ((2*coefficientWidth c.1 c.2+1:ℕ):ℝ)*((D:ℝ)*E) :=
        Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_left (hpoint c hc) (Nat.cast_nonneg _))
      _ = _ := by
        rw [← Finset.sum_mul]
        dsimp [modelProjectionConstant,D]
        push_cast
        ring
  have h := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ ((T.p i-1:ℕ):ℝ)*(modelLength S T i:ℝ) by positivity)
  simpa only [samplingProjectionBudget,modelBudgetEnvelope,Nat.cast_mul,Nat.cast_sum,mul_assoc,E] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.projectionEnvelope_bound
#print axioms KakeyaTwoScale.projectionEnvelope_rate
#print axioms KakeyaTwoScale.modelProjectionConstant_pos
#print axioms KakeyaTwoScale.slopeRectificationBudget_pos
#print axioms KakeyaTwoScale.modelBudgetEnvelope_bound
