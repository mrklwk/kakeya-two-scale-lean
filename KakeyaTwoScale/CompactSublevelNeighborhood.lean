module
public import KakeyaTwoScale.CompactComponentSeparation
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- A bounded simultaneous polynomial-sublevel approximation eventually lies
inside ANY open neighborhood of its compact zero set. Stated for a general
continuous nonnegative defect; the later counted polynomial stays polynomial. -/
theorem compact_zero_sublevels_shrink {X : Type*} [MetricSpace X] [ProperSpace X]
    (Q : X→ℝ) (hQ : Continuous Q) (hQ0 : ∀ x, 0≤Q x)
    (center : X) (R : ℝ) (hR : 0≤R)
    (O : Set X) (hO : IsOpen O) (hKO : {x | Q x=0} ∩ closedBall center R ⊆ O) :
    ∃ epsilon0 : ℝ, 0<epsilon0 ∧ ∀ epsilon : ℝ, 0<epsilon → epsilon≤epsilon0 →
      {x | Q x<epsilon ∧ dist x center^2<R^2+epsilon} ⊆ O := by
  let f : X→ℝ := fun x => Q x+max 0 (dist x center^2-R^2)
  have hf : Continuous f := hQ.add (continuous_const.max
    (((continuous_id.dist continuous_const).pow 2).sub continuous_const))
  let T : Set X := closedBall center (R+1) ∩ Oᶜ
  have hT : IsCompact T := (isCompact_closedBall center (R+1)).inter_right hO.isClosed_compl
  have hpos : ∀ x∈T, 0<f x := by
    intro x hx
    by_contra hh
    have hle : f x≤0 := le_of_not_gt hh
    have hq := hQ0 x
    have hm : 0≤max 0 (dist x center^2-R^2) := le_max_left _ _
    have hd : dist x center^2-R^2≤max 0 (dist x center^2-R^2) := le_max_right _ _
    have hzero : Q x=0 := by dsimp [f] at hle; linarith
    have hr : dist x center≤R := by
      dsimp [f] at hle
      nlinarith [dist_nonneg (x := x) (y := center)]
    exact hx.2 (hKO ⟨hzero,hr⟩)
  obtain ⟨m,hm,hmin⟩ := hT.exists_forall_le' hf.continuousOn hpos
  refine ⟨min 1 (m/4),lt_min (by norm_num) (by positivity),?_⟩
  intro epsilon he he0 x hx
  have he1 : epsilon≤1 := he0.trans (min_le_left _ _)
  have hem : epsilon≤m/4 := he0.trans (min_le_right _ _)
  by_contra hxO
  have hxR : dist x center≤R+1 := by
    have hdist := dist_nonneg (x := x) (y := center)
    nlinarith [hx.2]
  have hmx := hmin x ⟨hxR,hxO⟩
  have hmax : max 0 (dist x center^2-R^2)<epsilon := max_lt he (by linarith [hx.2])
  dsimp [f] at hmx
  linarith [hx.1]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.compact_zero_sublevels_shrink
