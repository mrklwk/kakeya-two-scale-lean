module
public import KakeyaTwoScale.SegmentGeometry
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A transverse affine axis has one full endpoint quarter uniformly away
from the zero plane. The same length 1/4 works at every scale. -/
theorem transverse_axis_quarter (c v : Y) (s : ℝ) (hs : 0 < s) (hv : s ≤ ‖v‖) :
    (∀ t ∈ Set.Icc (0:ℝ) (1/4), s/8 < ‖c+t • v‖) ∨
    (∀ t ∈ Set.Icc (3/4:ℝ) 1, s/8 < ‖c+t • v‖) := by
  by_contra h
  push Not at h
  obtain ⟨⟨t,ht,htn⟩,⟨u,hu,hun⟩⟩ := h
  have hdist : ‖(c+t • v)-(c+u • v)‖ ≤ s/4 := by
    have hh := norm_sub_le (c+t • v) (c+u • v)
    linarith
  have he : (c+t • v)-(c+u • v) = (t-u) • v := by rw [sub_smul]; abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [ht.2,hu.1])] at hdist
  have hsep : 1/2 ≤ u-t := by linarith [ht.2,hu.1]
  have hm := mul_le_mul_of_nonneg_right hsep (norm_nonneg v)
  nlinarith

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Tube thickness costs at most r in the normal component for a contraction.
Orthogonal projection onto the normal subspace supplies such a map. -/
theorem normal_component_of_tube_point (P : X →L[ℝ] Y) (hP : ‖P‖ ≤ 1)
    (p z x : X) (r d : ℝ) (hz : d < ‖P (z-p)‖) (hx : dist x z ≤ r) :
    d-r < ‖P (x-p)‖ := by
  have hdiff : ‖P (z-p) - P (x-p)‖ ≤ r := by
    rw [← map_sub, sub_sub_sub_cancel_right]
    have hh := P.le_opNorm (z-x)
    have hnorm : ‖z-x‖ ≤ r := by simpa [dist_eq_norm, norm_sub_rev] using hx
    have hp := mul_le_mul_of_nonneg_right hP (norm_nonneg (z-x))
    nlinarith
  have htriangle := norm_le_norm_add_norm_sub (P (x-p)) (P (z-p))
  rw [norm_sub_rev (P (x-p)) (P (z-p))] at htriangle
  linarith

/-- A genuinely shortened tube, not merely a positive-measure set of heights.
If normal speed is at least s and radius r≤s/16, one endpoint quarter stays
outside normal distance s/16, including every point of the thick tube. -/
theorem transverse_tube_shortening (P : X →L[ℝ] Y) (hP : ‖P‖ ≤ 1)
    (b v p : X) (s r : ℝ) (hs : 0 < s) (hv : s ≤ ‖P v‖) (hr : r ≤ s/16) :
    ∃ I : Set ℝ, (I = Set.Icc (0:ℝ) (1/4) ∨ I = Set.Icc (3/4:ℝ) 1) ∧
      ∀ t ∈ I, ∀ x : X, dist x (segmentPoint b v t) ≤ r → s/16 < ‖P (x-p)‖ := by
  have haxis := transverse_axis_quarter (P (b-p)) (P v) s hs hv
  have he (t : ℝ) : P (segmentPoint b v t-p) = P (b-p)+t • P v := by
    unfold segmentPoint
    rw [show b+t • v-p = (b-p)+t • v by abel, map_add, map_smul]
  have hstep (I : Set ℝ) (hh : ∀ t ∈ I, s/8 < ‖P (b-p)+t • P v‖) :
      ∀ t ∈ I, ∀ x : X, dist x (segmentPoint b v t) ≤ r → s/16 < ‖P (x-p)‖ := by
    intro t ht x hx
    have hn : s/8 < ‖P (segmentPoint b v t-p)‖ := by rw [he]; exact hh t ht
    have hb := normal_component_of_tube_point P hP p (segmentPoint b v t) x r (s/8) hn hx
    linarith
  rcases haxis with hl | hr'
  · exact ⟨_,Or.inl rfl,hstep _ hl⟩
  · exact ⟨_,Or.inr rfl,hstep _ hr'⟩
end KakeyaTwoScale
#print axioms KakeyaTwoScale.transverse_axis_quarter
#print axioms KakeyaTwoScale.normal_component_of_tube_point
#print axioms KakeyaTwoScale.transverse_tube_shortening
