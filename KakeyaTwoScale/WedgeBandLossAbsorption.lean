module
public import KakeyaTwoScale.FiniteWedgeBands

@[expose] public section

open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The exact linear band count costs an arbitrarily small radius power.
The positive constant is fixed before q and the inequality includes q=0. -/
theorem dyadic_linear_band_loss_absorption (d : ℕ) (Ct Cband η : ℝ)
    (hCt : 0<Ct) (hCband : 0≤Cband) (hη : 0<η) :
    ∃ K : ℝ, 0<K ∧ ∀ q : ℕ,
      Ct+((d*q:ℕ):ℝ)*Cband ≤ K*(dyadicWeightCut q)^(-η) := by
  let a := η*Real.log 2
  have ha : 0<a := mul_pos hη (Real.log_pos (by norm_num))
  let L := (d:ℝ)*Cband/a
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨Ct+L,by positivity,?_⟩
  intro q
  have ht : 0≤a*(q:ℝ) := mul_nonneg ha.le (Nat.cast_nonneg _)
  have he : 1≤Real.exp (a*(q:ℝ)) := Real.one_le_exp ht
  have he' : a*(q:ℝ)≤Real.exp (a*(q:ℝ)) := by linarith [Real.add_one_le_exp (a*(q:ℝ))]
  have hp : (dyadicWeightCut q)^(-η)=Real.exp (a*(q:ℝ)) := by
    rw [Real.rpow_def_of_pos (by unfold dyadicWeightCut; positivity)]
    unfold dyadicWeightCut
    rw [Real.log_inv,Real.log_pow]
    congr 1
    dsimp [a]
    ring
  rw [hp]
  have h₁ := mul_le_mul_of_nonneg_left he hCt.le
  have h₂ := mul_le_mul_of_nonneg_left he' hL
  have hid : Ct+((d*q:ℕ):ℝ)*Cband=Ct+L*(a*(q:ℝ)) := by
    dsimp [L]
    push_cast
    field_simp
  rw [hid]
  nlinarith only [h₁,h₂]

/-- Absorb the exact band count into epsilon+eta at the target pth-power
radius exponent. K precedes q, the mass, and the integral being estimated. -/
theorem dyadic_band_integral_loss_absorption (d : ℕ) (Ct Cband p η : ℝ)
    (hCt : 0<Ct) (hCband : 0≤Cband) (hp : 0<p) (hη : 0<η) :
    ∃ K : ℝ, 0<K ∧ ∀ (q : ℕ) (A ε α V : ℝ) (F : ℝ≥0∞), 0≤V →
      F ≤ ENNReal.ofReal ((Ct+((d*q:ℕ):ℝ)*Cband)*(dyadicWeightCut q)^(p*(A-ε))*V^α) →
      F ≤ ENNReal.ofReal (K*(dyadicWeightCut q)^(p*(A-(ε+η)))*V^α) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_linear_band_loss_absorption d Ct Cband (p*η) hCt hCband (mul_pos hp hη)
  refine ⟨K,hK,?_⟩
  intro q A ε α V F hV hF
  apply hF.trans
  apply ENNReal.ofReal_le_ofReal
  have hδ : 0<dyadicWeightCut q := by unfold dyadicWeightCut; positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound q)
    (Real.rpow_nonneg hδ.le (p*(A-ε)))) (Real.rpow_nonneg hV α)
  have he : (dyadicWeightCut q)^(-(p*η))*(dyadicWeightCut q)^(p*(A-ε))=
      (dyadicWeightCut q)^(p*(A-(ε+η))) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  simpa only [mul_assoc,he] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadic_linear_band_loss_absorption

#print axioms KakeyaTwoScale.dyadic_band_integral_loss_absorption
