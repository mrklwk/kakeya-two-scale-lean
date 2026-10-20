module
public import KakeyaTwoScale.CaptureRelationGeometry

@[expose] public section

open Set Metric MeasureTheory MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- All graph-format constants are fixed before coefficients, lengths and scale.
This applies constructed selection to the PROVED geometric formula, not to a
caller-supplied semialgebraicity or graph-complexity hypothesis. -/
theorem universal_capture_graph_format (n r e D : ℕ) (C : ℝ)
    (h : Fin (n+1)) (outer : Fin r) :
    ∃ s B : ℕ, ∃ F : (CaptureParameter n r e → ℝ) → (Fin n → ℝ) → (Fin n → ℝ),
      ∃ Q : (CaptureParameter n r e → ℝ) → Fin s → MvPolynomial (Fin n ⊕ Fin n) ℝ,
      ∃ accept : (Fin s → SignType) → Prop,
        (∀ p v, (∃ a, universalEligibleLine D C h outer p v a) →
          universalEligibleLine D C h outer p v (F p v)) ∧
        (∀ p j, (Q p j).totalDegree ≤ B) ∧
        (∀ p v a, a=F p v ↔ accept (fun j => SignType.sign (eval (Sum.elim a v) (Q p j)))) ∧
        ∀ p, ∃ U, IsOpen U ∧ volume Uᶜ=0 ∧ ContDiffOn ℝ 1 (F p) U := by
  exact uniform_semialgebraic_selection _ (universalEligibleLine_sign n r e D C h outer)

/-- Uniform one-scale bound for the ACTUAL polynomial capture universe. The
zero sets, point distances and fixed common slab are literal. The full nested
volume upper bound is deliberately not assumed or concluded here. -/
theorem universal_capture_sweep_volume (n r e D : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : Fin (n+1)) (outer : Fin r) :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ,
      ∀ (P : Fin r → Fin e → MvPolynomial (Fin (n+1)) ℝ),
      (∀ i j, (P i j).totalDegree ≤ D) →
      ∀ (center : EuclideanSpace ℝ (Fin (n+1))) (L : Fin r → ℝ),
      (∀ i, 0 < L i) → ∀ rho s ell : ℝ, 0 < rho → 0 < ell →
      volume {v | ∃ a, universalEligibleLine D C h outer (captureParameters P center L rho s ell) v a} *
        ENNReal.ofReal (ell^(n+1)) ≤
        (ENNReal.ofReal K * M) * (volume.prod volume)
          {z : (Fin n → ℝ) × ℝ | center+euclideanUnsplit h (z.2,z.1) ∈
            thickening rho (captureZeroSet (P outer) ∩ closedBall center ((C+4)*L outer))} := by
  obtain ⟨K,hK,M,hvol⟩ := uniform_semialgebraic_target_volume n _
    (universalEligibleLine_sign n r e D C h outer)
  refine ⟨K,hK,M,?_⟩
  intro P hP center L hL rho s ell hrho hell
  apply hvol (captureParameters P center L rho s ell) s ell hell
  intro v a ha t ht
  apply (universalCaptureNear_geometry D C h P hP center L rho s ell hrho outer
    (mul_nonneg (by linarith) (hL outer).le) v a t).mp
  exact ha.2.2.2.2.2.2 t ht

end KakeyaTwoScale
#print axioms KakeyaTwoScale.universal_capture_graph_format
#print axioms KakeyaTwoScale.universal_capture_sweep_volume
