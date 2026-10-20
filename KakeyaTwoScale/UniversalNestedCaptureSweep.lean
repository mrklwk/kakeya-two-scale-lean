module
public import KakeyaTwoScale.EligibleLineNestedCapture
public import KakeyaTwoScale.TranslatedChartVolume

@[expose] public section

open Set MeasureTheory
open OAI.Release061 OAI.Release061.SignElimination
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The generic selected sweep is reapplied to the actual smaller recursive
target. Its full fixed-slab containment is proved for every eligible line. -/
theorem universal_nested_capture_sweep_volume (n r e D : ℕ) (C : ℝ) (hC : 0≤C)
    (h : Fin (n+1)) (outer : Fin r) (rest : List (Fin r)) :
    ∃ K : ℝ, 0<K ∧ ∃ M : ℕ,
      ∀ (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ),
      (∀ i j, (P i j).totalDegree≤D) →
      ∀ (center : EuclideanSpace ℝ (Fin (n+1))) (L A : Fin r→ℝ) (rho s ell : ℝ), 0<ell →
      (∀ i∈outer::rest, 0<L i ∧ rho≤L i/4) →
      (outer::rest).IsChain (fun i j => L j≤L i ∧ A i=recursionDilation n (C+4)*L i/L j) →
      volume {v | ∃ a, universalEligibleLine D C h outer (captureParameters P center L rho s ell) v a}*
        ENNReal.ofReal (ell^(n+1)) ≤
      (ENNReal.ofReal K*M)*volume (nestedTubeSet D (C+4) (recursionKappa n) (recursionBeta n)
        (outer::rest) (nestedRecursionParameters P center L A rho)) := by
  obtain ⟨K,hK,M,hvol⟩ := uniform_semialgebraic_target_volume n _
    (universalEligibleLine_sign n r e D C h outer)
  refine ⟨K,hK,M,?_⟩
  intro P hP center L A rho s ell hell hscale hchain
  let E := nestedTubeSet D (C+4) (recursionKappa n) (recursionBeta n)
    (outer::rest) (nestedRecursionParameters P center L A rho)
  have hh := hvol (captureParameters P center L rho s ell) s ell hell
    {z : (Fin n→ℝ) × ℝ | center+euclideanUnsplit h (z.2,z.1)∈E}
    (fun v a ha t ht => eligibleLine_nested_slab D C hC h outer rest P hP center L A rho s ell
      hscale hchain v a ha t ht)
  rw [translated_chart_target_volume] at hh
  exact hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.universal_nested_capture_sweep_volume
