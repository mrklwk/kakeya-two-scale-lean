module
public import KakeyaTwoScale.LocalizedEligibleDirectionBall
public import KakeyaTwoScale.PolynomialChartCounting

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

theorem graphUnitDirection_chartSlope {n : ℕ} (h : Fin (n+1))
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1) (hh : 0<u h) :
    graphUnitDirection h (chartSlope h u)=u := by
  have he : euclideanUnsplit h (1,chartSlope h u)=(u h)⁻¹ • u := by
    apply PiLp.ext
    apply (Fin.forall_iff_succAbove h (P := fun i =>
      (euclideanUnsplit h (1,chartSlope h u)) i=((u h)⁻¹ • u) i)).mpr
    constructor
    · simp [unsplit_height,hh.ne']
    · intro j
      simp only [unsplit_horizontal,PiLp.smul_apply,smul_eq_mul,chartSlope,div_eq_inv_mul]
  unfold graphUnitDirection
  rw [he,NormedSpace.normalize_smul_of_pos (inv_pos.mpr hh),
    NormedSpace.normalize_eq_self_of_norm_eq_one hu]

/-- Counting mass belongs to distinct original identifiers, with chord-separated
unit directions. Descendant records are not assumed separated. -/
theorem original_slope_ball_volume_le {n : ℕ} {O : Type*}
    (F : Finset O) (h : Fin (n+1)) (u : O→EuclideanSpace ℝ (Fin (n+1)))
    (delta H : ℝ) (hd : 0<delta) (hH : 1≤H)
    (hu : ∀ o∈F, ‖u o‖=1) (hh : ∀ o∈F, 0<u o h)
    (hsep : ∀ o∈F, ∀ p∈F, o≠p → delta/2≤dist (u o) (u p))
    (E : Set (Fin n→ℝ))
    (hcover : ∀ o∈F, ball (chartSlope h (u o)) (delta/(16*(n+2:ℝ)*H))⊆E) :
    (F.card:ℝ≥0∞)*ENNReal.ofReal ((2*(delta/(16*(n+2:ℝ)*H)))^n)≤volume E := by
  classical
  have hdis : Set.PairwiseDisjoint (↑F : Set O)
      (fun o => ball (chartSlope h (u o)) (delta/(16*(n+2:ℝ)*H))) := by
    intro o ho p hp hop
    apply captured_slope_balls_disjoint h _ _ delta H hd hH
    rw [graphUnitDirection_chartSlope h (u o) (hu o ho) (hh o ho),
      graphUnitDirection_chartSlope h (u p) (hu p hp) (hh p hp)]
    exact hsep o ho p hp hop
  have hrad : 0<delta/(16*(n+2:ℝ)*H) := by
    have : 0<H := by linarith
    positivity
  have hball (o) : volume (ball (chartSlope h (u o)) (delta/(16*(n+2:ℝ)*H)))=
      ENNReal.ofReal ((2*(delta/(16*(n+2:ℝ)*H)))^n) := by
    rw [Real.volume_pi_ball _ hrad,Fintype.card_fin]
  calc
    _ = volume (⋃ o∈F, ball (chartSlope h (u o)) (delta/(16*(n+2:ℝ)*H))) := by
      rw [measure_biUnion_finset hdis (fun _ _ => measurableSet_ball)]
      simp [hball]
    _ ≤ volume E := measure_mono (iUnion₂_subset hcover)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.graphUnitDirection_chartSlope
#print axioms KakeyaTwoScale.original_slope_ball_volume_le
