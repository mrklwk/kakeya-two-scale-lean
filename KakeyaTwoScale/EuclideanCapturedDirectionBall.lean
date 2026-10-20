module
public import KakeyaTwoScale.GraphParentCapsule
public import KakeyaTwoScale.CommonLinePerturbation

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Capture along specified intervals in one translated coordinate chart.
The intercept is shared by every level. -/
def chartLineCaptured {n : ℕ} {I : Type*} (h : Fin (n+1))
    (center : EuclideanSpace ℝ (Fin (n+1)))
    (Z : I → Set (EuclideanSpace ℝ (Fin (n+1))))
    (J : I → Set ℝ) (rho : ℝ) (v b : Fin n → ℝ) : Prop :=
  ∀ i, ∀ t ∈ J i, center + euclideanUnsplit h (t,b+t • v) ∈ thickening rho (Z i)

/-- Whole sup-norm slope balls retain every capture interval and the same
intercept. The explicit dimension factor converts horizontal sup distance to
ambient Euclidean distance. Nearby variety points are reused unchanged. -/
theorem euclidean_captured_direction_ball {n : ℕ} {I : Type*}
    (h : Fin (n+1)) (center : EuclideanSpace ℝ (Fin (n+1)))
    (Z : I → Set (EuclideanSpace ℝ (Fin (n+1)))) (J : I → Set ℝ)
    (b v : Fin n → ℝ) (rho delta H : ℝ) (hdelta : 0 < delta) (hH : 0 < H)
    (htime : ∀ i, ∀ t ∈ J i, |t| ≤ H)
    (hcapture : chartLineCaptured h center Z J rho v b) :
    ball v (delta / (16*(n+2:ℝ)*H)) ⊆
      {w | chartLineCaptured h center Z J (rho+delta) w b} := by
  intro w hw i t ht
  obtain ⟨z,hz,hdz⟩ := mem_thickening_iff.mp (hcapture i t ht)
  refine mem_thickening_iff.mpr ⟨z,hz,?_⟩
  have hden : 0 < 16*(n+2:ℝ)*H := by positivity
  have hsmall : (16*(n+2:ℝ)*H)*dist w v < delta := by
    have hh := (lt_div_iff₀ hden).mp (show dist w v < delta/(16*(n+2:ℝ)*H) from hw)
    nlinarith
  have herr : dist (b+t • w) (b+t • v) ≤ H*dist w v := by
    rw [dist_add_left,dist_smul₀,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (htime i t ht) dist_nonneg
  have hamb := unsplit_same_height_dist h (b+t • w) (b+t • v) t
  have hmul := mul_le_mul_of_nonneg_left herr (show 0 ≤ (n+2:ℝ) by positivity)
  have hnonneg : 0 ≤ (n+2:ℝ)*H*dist w v := by positivity
  have hd : dist (center+euclideanUnsplit h (t,b+t • w))
      (center+euclideanUnsplit h (t,b+t • v)) < delta := by
    rw [dist_add_left]
    nlinarith
  exact (dist_triangle _ (center+euclideanUnsplit h (t,b+t • v)) z).trans_lt
    (add_lt_add hd hdz) |>.trans_le (by ring_nf; exact le_rfl)

/-- These are interior eligible slopes, so intersecting with a conull regular
selection domain loses none of the ball's measure. No regularity of individual
original directions is assumed. -/
theorem euclidean_direction_ball_interior {n : ℕ} {I : Type*}
    (h : Fin (n+1)) (center : EuclideanSpace ℝ (Fin (n+1)))
    (Z : I → Set (EuclideanSpace ℝ (Fin (n+1)))) (J : I → Set ℝ)
    (b v : Fin n → ℝ) (rho delta H : ℝ) (hdelta : 0 < delta) (hH : 0 < H)
    (htime : ∀ i, ∀ t ∈ J i, |t| ≤ H)
    (hcapture : chartLineCaptured h center Z J rho v b) :
    ball v (delta / (16*(n+2:ℝ)*H)) ⊆
      interior {w | ∃ b', chartLineCaptured h center Z J (rho+delta) w b'} := by
  apply interior_maximal _ isOpen_ball
  intro w hw
  exact ⟨b,euclidean_captured_direction_ball h center Z J b v rho delta H
    hdelta hH htime hcapture hw⟩

/-- Uniform Lipschitz control for the inverse slope chart, in its actual
sup-norm domain and Euclidean unit-direction codomain. -/
theorem graphUnitDirection_dist_le {n : ℕ} (h : Fin (n+1)) (v w : Fin n → ℝ) :
    dist (graphUnitDirection h v) (graphUnitDirection h w) ≤
      2*(n+2:ℝ)*dist v w := by
  have hnorm : 1 ≤ ‖euclideanUnsplit h (1,v)‖ := by
    simpa [Real.norm_eq_abs,graphVector_height] using PiLp.norm_apply_le (euclideanUnsplit h (1,v)) h
  have hn := normalize_dist_le (euclideanUnsplit h (1,v)) (euclideanUnsplit h (1,w))
    hnorm (norm_pos_iff.mpr (graphVector_ne_zero h _))
  have hd := unsplit_same_height_dist h v w 1
  change dist (graphUnitDirection h v) (graphUnitDirection h w) ≤ _ at hn
  linarith

/-- The captured slope balls are disjoint for chord-separated ORIGINAL
unit directions. No separation of descendant records is asserted. -/
theorem captured_slope_balls_disjoint {n : ℕ} (h : Fin (n+1)) (v w : Fin n → ℝ)
    (delta H : ℝ) (hdelta : 0 < delta) (hH : 1 ≤ H)
    (hsep : delta/2 ≤ dist (graphUnitDirection h v) (graphUnitDirection h w)) :
    Disjoint (ball v (delta/(16*(n+2:ℝ)*H)))
      (ball w (delta/(16*(n+2:ℝ)*H))) := by
  apply ball_disjoint_ball
  have hN : 0 < (n+2:ℝ) := by positivity
  have hHpos : 0 < H := by linarith
  have hden : 0 < 16*(n+2:ℝ)*H := by positivity
  have hsep' := graphUnitDirection_dist_le h v w
  have hr : delta/(16*(n+2:ℝ)*H) ≤ delta/(16*(n+2:ℝ)) := by
    apply div_le_div_of_nonneg_left hdelta.le (by positivity)
    nlinarith
  have he : delta/(16*(n+2:ℝ)) * (16*(n+2:ℝ)) = delta :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith [dist_nonneg (x := v) (y := w)]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclidean_captured_direction_ball
#print axioms KakeyaTwoScale.euclidean_direction_ball_interior

#print axioms KakeyaTwoScale.graphUnitDirection_dist_le
#print axioms KakeyaTwoScale.captured_slope_balls_disjoint
