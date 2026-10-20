module
public import KakeyaTwoScale.ThickPolynomialIntersection

@[expose] public section

open Set Metric MeasureTheory
open OAI.Release061 OAI.Release061.SignElimination
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- A real positive uniform constant for the prescribed-cylinder Fat union. -/
theorem uniform_prescribedFat_volume {π : Type*} (d : ℕ)
    (S : Set ((π→ℝ) × (Fin d→ℝ)))
    (hS : PolynomialSignSet (fun z => Sum.elim z.1 z.2) S) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : π→ℝ) (a L w : ℝ), 1≤a → 0<L → 0<w →
      volume (prescribedCylinderFat a L w {x : EuclideanSpace ℝ (Fin d) | (p,x.ofLp)∈S}) ≤
        ENNReal.ofReal (C*a^d)*volume {x : EuclideanSpace ℝ (Fin d) | (p,x.ofLp)∈S} := by
  obtain ⟨C,hC,M,h⟩ := uniform_flatCylinderFatUnion_volume d S hS
  refine ⟨C*((M:ℝ)+1),by positivity,?_⟩
  intro p a L w ha hL hw
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  have hm : max 1 |(a+1)/2|≤a := by
    rw [abs_of_pos (by positivity : 0<(a+1)/2)]
    exact max_le ha (by linarith)
  have hfac : ENNReal.ofReal (C*(max 1 |(a+1)/2|)^d)*(M:ℝ≥0∞)≤
      ENNReal.ofReal (C*((M:ℝ)+1)*a^d) := by
    rw [← ENNReal.ofReal_natCast M,← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ C*a^d*(M:ℝ) := by gcongr
      _ ≤ _ := by nlinarith [pow_pos ha0 d]
  exact (measure_mono (prescribedCylinderFat_subset a L w _ hL hw)).trans
    ((h p a ha0).trans (mul_le_mul hfac le_rfl zero_le zero_le))

/-- One genuine recurrence step: both thickness and enlargement volume are
proved for the actual prescribed-cylinder union, before numerical scales. -/
theorem uniform_prescribedFat_polynomial_step {π : Type*} (d D : ℕ) [NeZero d]
    (S : Set ((π→ℝ) × (Fin d→ℝ)))
    (hS : PolynomialSignSet (fun z => Sum.elim z.1 z.2) S) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : π→ℝ) (s : ℕ), s≤d →
      ∀ P : Fin s→MvPolynomial (Fin d) ℝ, (∀ j, (P j).totalDegree≤D) →
      (∀ x, rectangularPolynomialMap P x=0 →
        (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) →
      ∀ (a L w rho : ℝ), 1≤a → 0<w → w≤L → 0<rho → rho≤2*(a*w) →
      volume {x : EuclideanSpace ℝ (Fin d) | (p,x.ofLp)∈S}≠⊤ →
      volume (thickening rho {x | rectangularPolynomialMap P x=0}∩
        prescribedCylinderFat a L w {x : EuclideanSpace ℝ (Fin d) | (p,x.ofLp)∈S}) ≤
      ENNReal.ofReal (C*(rho/(a*w))^s*a^d)*
        volume {x : EuclideanSpace ℝ (Fin d) | (p,x.ofLp)∈S} := by
  obtain ⟨K,hK,hthin⟩ := uniform_thick_polynomial_intersection d D
  obtain ⟨C,hC,hfat⟩ := uniform_prescribedFat_volume d S hS
  refine ⟨K*C,mul_pos hK hC,?_⟩
  intro p s hs P hP hreg a L w rho ha hw hwL hrho hscale hE
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  have hvol := hfat p a L w ha (hw.trans_le hwL) hw
  have hW : volume (prescribedCylinderFat a L w {x : EuclideanSpace ℝ (Fin d) | (p,x.ofLp)∈S})≠⊤ :=
    ne_top_of_le_ne_top (by finiteness) hvol
  have hh := hthin s hs P hP hreg _ rho (a*w) hrho (mul_pos ha0 hw) hscale hW
    (prescribedCylinderFat_inner_ball a L w _ ha0 hw hwL)
  refine hh.trans ?_
  calc
    _ ≤ ENNReal.ofReal (K*(rho/(a*w))^s)*(ENNReal.ofReal (C*a^d)*
        volume {x : EuclideanSpace ℝ (Fin d) | (p,x.ofLp)∈S}) :=
      mul_le_mul le_rfl hvol zero_le zero_le
    _ = _ := by rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity)]; congr 2; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_prescribedFat_volume
#print axioms KakeyaTwoScale.uniform_prescribedFat_polynomial_step
