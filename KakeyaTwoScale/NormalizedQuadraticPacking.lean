module
public import KakeyaTwoScale.CompactBallPacking
public import KakeyaTwoScale.QuadraticFormComparison

@[expose] public section

open Set Metric
open scoped ENNReal NNReal
noncomputable section
namespace KakeyaTwoScale

/-- Fixed coercivity and bounded coefficients give a uniform cardinality bound
for a family whose distinct quadratic forms fail factor-two comparison.
The bound precedes the finite family; no eccentricity-dependent net size occurs. -/
theorem normalized_quadratic_packing_bound (N : ℕ) (a R : ℝ) (ha : 0<a) :
    ∃ M : ℕ, ∀ F : Finset (Fin N → Fin N → ℝ),
      (∀ Q ∈ F, ∀ i j, |Q i j| ≤ R) →
      (∀ Q ∈ F, ∀ x, a*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 ≤ matrixQuadraticValue Q x) →
      (∀ Q ∈ F, ∀ P ∈ F, Q ≠ P →
        ¬ ∀ x, matrixQuadraticValue Q x ≤ 2*matrixQuadraticValue P x ∧
          matrixQuadraticValue P x ≤ 2*matrixQuadraticValue Q x) →
      F.card ≤ M := by
  let S : Set (Fin N → Fin N → ℝ) := univ.pi (fun _ => univ.pi (fun _ => Icc (-R) R))
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  let δ : ℝ≥0 := ⟨a/((N:ℝ)^2+1),by positivity⟩
  have hδ : 0<δ := by change (0:ℝ)<a/((N:ℝ)^2+1); positivity
  obtain ⟨M,hM⟩ := compact_separated_card_bound S hS δ hδ
  refine ⟨M,?_⟩
  intro F hb hcoerce hseparate
  apply hM F
  · intro Q hQ i _ j _
    exact abs_le.mp (hb Q hQ i j)
  · intro Q hQ P hP hne
    change (δ:ℝ≥0∞) < edist Q P
    by_contra! he
    have hd : dist Q P ≤ a/((N:ℝ)^2+1) := by
      have he' : ENNReal.ofReal (dist Q P) ≤ ENNReal.ofReal (a/((N:ℝ)^2+1)) := by
        change ENNReal.ofReal (dist Q P) ≤ ENNReal.ofReal (δ:ℝ)
        simpa only [edist_dist,ENNReal.ofReal_coe_nnreal] using he
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he'
    exact hseparate Q hQ P hP hne
      (close_coercive_quadratic_forms a ha Q P (hcoerce Q hQ) (hcoerce P hP) hd)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalized_quadratic_packing_bound
