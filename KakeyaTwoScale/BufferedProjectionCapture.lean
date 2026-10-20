module
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Tactic

@[expose] public section

open Set Metric
open scoped NNReal
noncomputable section
namespace KakeyaTwoScale

/-- A bounded-distance endpoint is constructed by minimizing residual distance
plus half the distance from the start. Only genuine LOCAL sections are assumed;
no global lift, proper projection, or successful continuation is assumed. -/
theorem exists_projection_target_or_exit {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (W R : Set E) (hW : IsClosed W) (π : E → V) (hπ : Continuous π)
    (hlocal : ∀ y ∈ W, y ∈ R → ∃ (r : ℝ) (c : ℝ≥0) (σ : V → E),
      0 < r ∧ (c : ℝ) < 2 ∧ σ (π y) = y ∧
      LipschitzOnWith c σ (ball (π y) r) ∧
      ∀ a ∈ ball (π y) r, σ a ∈ W ∧ π (σ a) = a)
    (z : E) (hz : z ∈ W) (v : V) :
    ∃ y ∈ W, dist y z ≤ 2 * dist (π z) v ∧ (π y = v ∨ y ∉ R) := by
  let F : E → ℝ := fun y => dist (π y) v + dist y z / 2
  let L := dist (π z) v
  have hF : Continuous F := (hπ.dist continuous_const).add
    ((continuous_id.dist continuous_const).div_const 2)
  have hc : IsCompact (W ∩ closedBall z (2*L)) :=
    (isCompact_closedBall z (2*L)).inter_left hW
  have hzS : z ∈ W ∩ closedBall z (2*L) := by
    refine ⟨hz, ?_⟩
    simp only [mem_closedBall, dist_self]
    dsimp [L]
    positivity
  obtain ⟨y,hy,hmin⟩ := hc.exists_isMinOn ⟨z,hzS⟩ hF.continuousOn
  have hFy : F y ≤ L := by simpa [F, L] using hmin hzS
  have hglobal : ∀ x ∈ W, F y ≤ F x := by
    intro x hx
    by_cases hb : x ∈ closedBall z (2*L)
    · exact hmin ⟨hx,hb⟩
    · have hd : 2*L < dist x z := by simpa only [mem_closedBall, not_le] using hb
      dsimp [F] at hFy ⊢
      linarith [dist_nonneg (x := π x) (y := v)]
  refine ⟨y,hy.1,hy.2,?_⟩
  by_cases he : π y = v
  · exact Or.inl he
  right
  intro hyR
  obtain ⟨r,c,σ,hr,hc2,hσy,hσlip,hσsec⟩ := hlocal y hy.1 hyR
  have hd : 0 < dist (π y) v := dist_pos.mpr he
  have hsmall : 0 < min (1:ℝ) (r / dist (π y) v) :=
    lt_min zero_lt_one (div_pos hr hd)
  obtain ⟨t,ht,htsmall⟩ := exists_between hsmall
  have ht1 : t < 1 := (lt_min_iff.mp htsmall).1
  have htr : t * dist (π y) v < r :=
    (lt_div_iff₀ hd).mp (lt_min_iff.mp htsmall).2
  let a := AffineMap.lineMap (π y) v t
  have hay : dist a (π y) = t * dist (π y) v := by
    simp only [a, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht]
  have hav : dist a v = (1-t) * dist (π y) v := by
    simp only [a, dist_lineMap_right, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1)]
  have ha : a ∈ ball (π y) r := by simpa only [mem_ball, hay] using htr
  obtain ⟨hσW,hσa⟩ := hσsec a ha
  have hstep : dist (σ a) y ≤ (c : ℝ) * (t * dist (π y) v) := by
    simpa only [hσy, hay] using hσlip.dist_le_mul a ha (π y) (mem_ball_self hr)
  have htri := dist_triangle (σ a) y z
  have hmin' := hglobal (σ a) hσW
  dsimp only [F] at hmin'
  rw [hσa, hav] at hmin'
  have hgain : 0 < (2-(c:ℝ)) * (t * dist (π y) v) :=
    mul_pos (sub_pos.mpr hc2) (mul_pos ht hd)
  nlinarith

/-- Endpoint in the target fiber or on the actual Gauss boundary. Closedness
of Z and continuity of g replace any global properness/covering assumption. -/
theorem exists_projection_target_or_gauss_boundary {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Z : Set E) (hZ : IsClosed Z) (g : E → ℝ) (hg : Continuous g)
    (π : E → V) (hπ : Continuous π)
    (hlocal : ∀ y ∈ Z, 0 < g y → ∃ (r : ℝ) (c : ℝ≥0) (σ : V → E),
      0 < r ∧ (c : ℝ) < 2 ∧ σ (π y) = y ∧
      LipschitzOnWith c σ (ball (π y) r) ∧
      ∀ a ∈ ball (π y) r, σ a ∈ Z ∧ 0 ≤ g (σ a) ∧ π (σ a) = a)
    (z : E) (hz : z ∈ Z) (hgz : 0 ≤ g z) (v : V) :
    ∃ y ∈ Z, 0 ≤ g y ∧ dist y z ≤ 2 * dist (π z) v ∧
      (π y = v ∨ g y = 0) := by
  have hW : IsClosed (Z ∩ {y | 0 ≤ g y}) :=
    hZ.inter (isClosed_le continuous_const hg)
  obtain ⟨y,hy,hd,halt⟩ := exists_projection_target_or_exit
    (Z ∩ {y | 0 ≤ g y}) {y | 0 < g y} hW π hπ
    (fun y hy hypos => by
      obtain ⟨r,c,σ,hr,hc,hσ,hLip,hsec⟩ := hlocal y hy.1 hypos
      exact ⟨r,c,σ,hr,hc,hσ,hLip,fun a ha =>
        ⟨⟨(hsec a ha).1,(hsec a ha).2.1⟩,(hsec a ha).2.2⟩⟩)
    z ⟨hz,hgz⟩ v
  refine ⟨y,hy.1,hy.2,hd,halt.imp_right ?_⟩
  intro h
  exact le_antisymm (le_of_not_gt h) hy.2

/-- A single point of the whole set near the projected wall gives capture of
EVERY point of that set by the target successor or Gauss successor. This uses
actual local sections and the constructed endpoint, not a capture premise. -/
theorem whole_set_buffered_projection_capture {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Z : Set E) (hZ : IsClosed Z) (g : E → ℝ) (hg : Continuous g)
    (π : E → V) (hπ : LipschitzWith 1 π)
    (hlocal : ∀ y ∈ Z, 0 < g y → ∃ (r : ℝ) (c : ℝ≥0) (σ : V → E),
      0 < r ∧ (c : ℝ) < 2 ∧ σ (π y) = y ∧
      LipschitzOnWith c σ (ball (π y) r) ∧
      ∀ a ∈ ball (π y) r, σ a ∈ Z ∧ 0 ≤ g (σ a) ∧ π (σ a) = a)
    (Q : Set E) (T : Set V) (z : E) (hz : z ∈ Z) (hgz : 0 ≤ g z)
    (η r : ℝ) (hnear : ∀ x ∈ Q, dist x z < η)
    (hbad : ∃ x ∈ Q, π x ∈ thickening r T) :
    ∃ y ∈ (Z ∩ π ⁻¹' T) ∪ (Z ∩ {y | g y = 0}),
      ∀ x ∈ Q, dist x y < η + 2*(η+r) := by
  obtain ⟨x,hx,hbad⟩ := hbad
  obtain ⟨v,hv,hxv⟩ := mem_thickening_iff.mp hbad
  have hzv : dist (π z) v < η+r := by
    have hproj : dist (π z) (π x) ≤ dist z x := by
      simpa using hπ.dist_le_mul z x
    have hnx : dist z x < η := by simpa only [dist_comm] using hnear x hx
    have htri := dist_triangle (π z) (π x) v
    linarith
  obtain ⟨y,hy,_,hyz,halt⟩ := exists_projection_target_or_gauss_boundary
    Z hZ g hg π hπ.continuous hlocal z hz hgz v
  refine ⟨y,?_,?_⟩
  · rcases halt with ht | hg0
    · exact Or.inl ⟨hy, by simpa only [mem_preimage, ht] using hv⟩
    · exact Or.inr ⟨hy,hg0⟩
  · intro q hq
    have hnq := hnear q hq
    have htri := dist_triangle q z y
    rw [dist_comm z y] at htri
    linarith

/-- The preceding endpoint captures a whole cube in the neighborhood of ONE
successor, rather than only a neighborhood of their union. -/
theorem whole_set_buffered_projection_capture_alternative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Z : Set E) (hZ : IsClosed Z) (g : E → ℝ) (hg : Continuous g)
    (π : E → V) (hπ : LipschitzWith 1 π)
    (hlocal : ∀ y ∈ Z, 0 < g y → ∃ (r : ℝ) (c : ℝ≥0) (σ : V → E),
      0 < r ∧ (c : ℝ) < 2 ∧ σ (π y) = y ∧
      LipschitzOnWith c σ (ball (π y) r) ∧
      ∀ a ∈ ball (π y) r, σ a ∈ Z ∧ 0 ≤ g (σ a) ∧ π (σ a) = a)
    (Q : Set E) (T : Set V) (z : E) (hz : z ∈ Z) (hgz : 0 ≤ g z)
    (η r : ℝ) (hnear : ∀ x ∈ Q, dist x z < η)
    (hbad : ∃ x ∈ Q, π x ∈ thickening r T) :
    Q ⊆ thickening (η+2*(η+r)) (Z ∩ π ⁻¹' T) ∨
    Q ⊆ thickening (η+2*(η+r)) (Z ∩ {y | g y = 0}) := by
  obtain ⟨y,hy,hclose⟩ := whole_set_buffered_projection_capture
    Z hZ g hg π hπ hlocal Q T z hz hgz η r hnear hbad
  rcases hy with ht | hg0
  · exact Or.inl (fun x hx => mem_thickening_iff.mpr ⟨y,ht,hclose x hx⟩)
  · exact Or.inr (fun x hx => mem_thickening_iff.mpr ⟨y,hg0,hclose x hx⟩)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_projection_target_or_exit
#print axioms KakeyaTwoScale.exists_projection_target_or_gauss_boundary

#print axioms KakeyaTwoScale.whole_set_buffered_projection_capture
#print axioms KakeyaTwoScale.whole_set_buffered_projection_capture_alternative
