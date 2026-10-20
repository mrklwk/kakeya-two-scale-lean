module
public import KakeyaTwoScale.CountedPolynomialPartition
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory Set
noncomputable section
namespace KakeyaTwoScale

/-- The actual fiber integral, including the Bochner zero convention on the
null exceptional fibers. Integrability is proved from the original density. -/
def projectionMarginal {k m : ℕ}
    (w : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ := ∫ y, w (x,y)

theorem integrable_projectionMarginal {k m : ℕ}
    (w : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) → ℝ)
    (hw : Integrable w) : Integrable (projectionMarginal w) := by
  exact hw.integral_prod_left

theorem projectionMarginal_nonneg {k m : ℕ}
    (w : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) → ℝ)
    (hw : ∀ z, 0 ≤ w z) : ∀ x, 0 ≤ projectionMarginal w x := by
  intro x
  exact integral_nonneg (fun y => hw (x,y))

theorem projectionMarginal_integral {k m : ℕ}
    (w : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) → ℝ)
    (hw : Integrable w) : (∫ x, projectionMarginal w x) = ∫ z, w z := by
  exact (integral_prod w hw).symm

/-- Every cylindrical region has exactly the corresponding marginal mass. -/
theorem projectionMarginal_setIntegral {k m : ℕ}
    (w : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) → ℝ)
    (hw : Integrable w) (S : Set (EuclideanSpace ℝ (Fin k))) :
    (∫ z in Prod.fst ⁻¹' S, w z) = ∫ x in S, projectionMarginal w x := by
  have he : Prod.fst ⁻¹' S = S ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := by
    ext z; simp
  rw [he]
  simpa only [projectionMarginal, ← Measure.volume_eq_prod, Measure.restrict_univ] using setIntegral_prod (s := S) (t := Set.univ) w hw.integrableOn

/-- Partition a genuine product density in the projected dimension k.
The output cells are actual cylinders over the base polynomial components.
No variety, regular-value, or off-wall retention premise is smuggled in. -/
theorem exists_projected_polynomial_partition (k m D : ℕ) (hk : 0 < k) (hD : 0 < D)
    (w : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) → ℝ)
    (hw : Integrable w) (hwn : ∀ z, 0 ≤ w z) :
    ∃ P : MvPolynomial (Fin k) ℝ, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      volume (ambientPolynomialZeroSet P) = 0 ∧
      (polynomialComplementComponents P).Finite ∧
      (polynomialComplementComponents P).ncard ≤ 3^k * D^k ∧
      ∀ S ∈ polynomialComplementComponents P,
        (∫ z in Prod.fst ⁻¹' S, w z) ≤ ((4*(k:ℝ)^2)/(D:ℝ))^k * (∫ z, w z) := by
  obtain ⟨P,hne,hdeg,hnull,hfin,hcard,hmass⟩ :=
    exists_counted_degree_budget_polynomial_partition k hk D hD
      (projectionMarginal w) (integrable_projectionMarginal w hw)
      (projectionMarginal_nonneg w hwn)
  refine ⟨P,hne,hdeg,hnull,hfin,hcard,?_⟩
  intro S hS
  rw [projectionMarginal_setIntegral w hw S]
  simpa [projectionMarginal_integral w hw] using hmass S hS

end KakeyaTwoScale
#print axioms KakeyaTwoScale.integrable_projectionMarginal
#print axioms KakeyaTwoScale.projectionMarginal_nonneg
#print axioms KakeyaTwoScale.projectionMarginal_integral
#print axioms KakeyaTwoScale.projectionMarginal_setIntegral
#print axioms KakeyaTwoScale.exists_projected_polynomial_partition
