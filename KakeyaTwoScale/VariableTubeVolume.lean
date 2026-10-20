module
public import KakeyaTwoScale.TubeCapture

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

theorem variable_tube_shear_coordinate_bound {n : ℕ} (i : Fin (n+1))
    (b u x : EuclideanSpace ℝ (Fin (n+1))) (ell : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hu : ‖u‖=1) (hi : 1/(n+2:ℝ) ≤ |u i|)
    (hx : x ∈ euclideanTube b (ell • u) r) (j : Fin n) :
    |x (i.succAbove j)-b (i.succAbove j)-(x i-b i)*chartSlope i u j| ≤ (n+3:ℝ)*r := by
  have hn : (0:ℝ)<n+2 := by positivity
  have hi0 : 0 < |u i| := lt_of_lt_of_le (by positivity) hi
  have hui : u i ≠ 0 := abs_pos.mp hi0
  have hjunit : |u (i.succAbove j)| ≤ 1 := by
    simpa [Real.norm_eq_abs,hu] using PiLp.norm_apply_le u (i.succAbove j)
  have hratio : |chartSlope i u j| ≤ n+2 := by
    rw [chartSlope,abs_div]
    apply (div_le_iff₀ hi0).mpr
    have hh := (div_le_iff₀ hn).mp hi
    nlinarith
  obtain ⟨t,ht,he⟩ := tube_coordinate_error b (ell • u) x hx
  simp only [PiLp.smul_apply,smul_eq_mul] at he
  have hid : x (i.succAbove j)-b (i.succAbove j)-(x i-b i)*chartSlope i u j =
      (x (i.succAbove j)-(b (i.succAbove j)+t*(ell*u (i.succAbove j))))-
      (x i-(b i+t*(ell*u i)))*chartSlope i u j := by
    unfold chartSlope; field_simp; ring
  rw [hid]
  have hh := norm_sub_le (x (i.succAbove j)-(b (i.succAbove j)+t*(ell*u (i.succAbove j))))
    ((x i-(b i+t*(ell*u i)))*chartSlope i u j)
  simp only [Real.norm_eq_abs,abs_mul] at hh
  have hm := mul_le_mul (he i) hratio (abs_nonneg _) hr
  linarith [he (i.succAbove j)]

theorem variable_tube_in_height_box {n : ℕ} (i : Fin (n+1))
    (b u x : EuclideanSpace ℝ (Fin (n+1))) (ell : ℝ) {r lo hi : ℝ} (hr : 0 ≤ r)
    (hu : ‖u‖=1) (hiu : 1/(n+2:ℝ) ≤ |u i|)
    (hx : x ∈ euclideanTube b (ell • u) r) (ht : x i ∈ Set.Icc lo hi) :
    x ∈ tubeSliceBox i b u lo hi ((n+3:ℝ)*r) := by
  refine ⟨ht,?_,?_⟩
  · intro j
    have hh := (abs_le.mp (variable_tube_shear_coordinate_bound i b u x ell hr hu hiu hx j)).1
    change -((n+3:ℝ)*r) ≤ x (i.succAbove j)-
      (b (i.succAbove j)-b i*chartSlope i u j+x i*chartSlope i u j)
    linarith
  · intro j
    have hh := (abs_le.mp (variable_tube_shear_coordinate_bound i b u x ell hr hu hiu hx j)).2
    change x (i.succAbove j)-
      (b (i.succAbove j)-b i*chartSlope i u j+x i*chartSlope i u j) ≤ (n+3:ℝ)*r
    linarith

/-- A capsule loses at most O(delta r^n) volume inside any ball of radius delta. -/
theorem variable_tube_inter_ball_volume {n : ℕ}
    (b u p : EuclideanSpace ℝ (Fin (n+1))) (ell : ℝ) {r delta : ℝ}
    (hr : 0 < r) (hd : 0 ≤ delta) (hu : ‖u‖=1) :
    volume.real (euclideanTube b (ell • u) r ∩ Metric.ball p delta) ≤
      2*delta*(2*(n+3:ℝ))^n*r^n := by
  obtain ⟨i,hi⟩ := unit_large_coordinate u hu
  have hs : euclideanTube b (ell • u) r ∩ Metric.ball p delta ⊆
      tubeSliceBox i b u (p i-delta) (p i+delta) ((n+3:ℝ)*r) := by
    intro x hx
    apply variable_tube_in_height_box i b u x ell hr.le hu hi hx.1
    have he := PiLp.norm_apply_le (x-p) i
    have hx' : ‖x-p‖ < delta := by simpa [Metric.mem_ball,dist_eq_norm] using hx.2
    have hcoord : |x i-p i| ≤ delta := by simpa [Real.norm_eq_abs] using he.trans hx'.le
    obtain ⟨hlo,hhi⟩ := abs_le.mp hcoord
    constructor <;> linarith
  have hh := measureReal_mono hs (tubeSliceBox_finite i b u _ _ _)
  rw [tubeSliceBox_volume i b u _ _ _ (by linarith) (by positivity)] at hh
  rw [show 2*((n+3:ℝ)*r)=(2*(n+3:ℝ))*r by ring,mul_pow] at hh
  convert hh using 1; ring

/-- A uniform upper cap on the full capsule volume, including both ends. -/
theorem variable_tube_volume_upper {n : ℕ}
    (b u : EuclideanSpace ℝ (Fin (n+1))) (ell L : ℝ) (hell : 0 ≤ ell) (hL : 1 ≤ L) (hellL : ell ≤ L) {r : ℝ}
    (hr : 0 < r) (hrone : r ≤ 1/2) (hu : ‖u‖=1) :
    volume.real (euclideanTube b (ell • u) r) ≤ 3*L*(2*(n+3:ℝ))^n*r^n := by
  obtain ⟨i,hi⟩ := unit_large_coordinate u hu
  have hs : euclideanTube b (ell • u) r ⊆
      tubeSliceBox i b u (b i-L-r) (b i+L+r) ((n+3:ℝ)*r) := by
    intro x hx
    apply variable_tube_in_height_box i b u x ell hr.le hu hi hx
    obtain ⟨t,ht,he⟩ := tube_coordinate_error b (ell • u) x hx
    simp only [PiLp.smul_apply,smul_eq_mul] at he
    have hui : |u i| ≤ 1 := by simpa [hu,Real.norm_eq_abs] using PiLp.norm_apply_le u i
    have htui : |t*(ell*u i)| ≤ L := by
      rw [abs_mul,abs_mul,abs_of_nonneg ht.1,abs_of_nonneg hell]
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hui hell) ht.1
      have hh2 := mul_le_mul_of_nonneg_right ht.2 hell
      nlinarith
    obtain ⟨ha,hb⟩ := abs_le.mp htui
    obtain ⟨hc,hd⟩ := abs_le.mp (he i)
    constructor <;> linarith
  have hh := measureReal_mono hs (tubeSliceBox_finite i b u _ _ _)
  rw [tubeSliceBox_volume i b u _ _ _ (by linarith) (by positivity)] at hh
  have hl : b i+L+r-(b i-L-r) ≤ 3*L := by linarith
  have hm := mul_le_mul_of_nonneg_right hl (show 0 ≤ (2*((n+3:ℝ)*r))^n by positivity)
  have hf := hh.trans hm
  rw [show 2*((n+3:ℝ)*r)=(2*(n+3:ℝ))*r by ring,mul_pow] at hf
  convert hf using 1; ring


/-- A capsule of length at least one contains the actual unit subcapsule,
including both endpoint caps. -/
theorem unit_tube_subset_variable {n : ℕ}
    (b u : EuclideanSpace ℝ (Fin (n+1))) (ell r : ℝ) (hell : 1 ≤ ell) :
    euclideanTube b u r ⊆ euclideanTube b (ell • u) r := by
  intro x hx
  obtain ⟨t,ht,hd⟩ := hx
  have hp : 0 < ell := by linarith
  refine ⟨t/ell,⟨div_nonneg ht.1 hp.le,(div_le_one hp).mpr (ht.2.trans hell)⟩,?_⟩
  rwa [smul_smul,div_mul_cancel₀ _ hp.ne']

/-- Lower volume is uniform in every length at least one; no maximum length
is needed for this bound. -/
theorem variable_tube_volume_lower (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ell : ℝ, 0 < r → 1 ≤ ell →
      ∀ b u : EuclideanSpace ℝ (Fin (n+1)), ‖b‖ ≤ R → ‖u‖=1 →
      c*r^n ≤ volume.real (euclideanTube b (ell • u) r) := by
  obtain ⟨c,hc,hvol⟩ := euclideanTube_volume_lower n R hR
  refine ⟨c,hc,?_⟩
  intro r ell hr hell b u hb hu
  exact (hvol r hr b u hb hu).trans
    (measureReal_mono (unit_tube_subset_variable b u ell r hell) (euclideanTube_finite b (ell • u) r))

/-- Removing a fixed-radius ball retains actual captured volume. All constants
precede the width, tube, captured set and ball center. E need not be an axis set
or even measurable for this outer-volume inequality. -/
theorem variable_tube_retained_capture (n : ℕ) (R lam : ℝ)
    (hR : 0 ≤ R) (hlam : 0 < lam) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ r ell : ℝ, 0 < r → 1 ≤ ell →
      ∀ b u p : EuclideanSpace ℝ (Fin (n+1)), ‖b‖ ≤ R → ‖u‖=1 →
      ∀ E : Set (EuclideanSpace ℝ (Fin (n+1))),
      lam*volume.real (euclideanTube b (ell • u) r) ≤ volume.real (euclideanTube b (ell • u) r ∩ E) →
      c*r^n ≤ volume.real ((euclideanTube b (ell • u) r ∩ E) \ Metric.ball p delta) := by
  obtain ⟨c0,hc0,hvol⟩ := variable_tube_volume_lower n R hR
  let A : ℝ := (2*(n+3:ℝ))^n
  have hA : 0 < A := by dsimp [A]; positivity
  let delta := lam*c0/(4*A)
  refine ⟨delta,lam*c0/2,by dsimp [delta]; positivity,by positivity,?_⟩
  intro r ell hr hell b u p hb hu E hcap
  have hfinite := euclideanTube_finite b (ell • u) r
  have hsplit := measureReal_inter_add_sdiff (μ:=volume)
    (s:=euclideanTube b (ell • u) r ∩ E) (t:=Metric.ball p delta) (Metric.isOpen_ball.measurableSet)
    (measure_ne_top_of_subset Set.inter_subset_left hfinite)
  have hsub : (euclideanTube b (ell • u) r ∩ E) ∩ Metric.ball p delta ⊆
      euclideanTube b (ell • u) r ∩ Metric.ball p delta := fun _ hx => ⟨hx.1.1,hx.2⟩
  have hsmall := (measureReal_mono hsub
    (measure_ne_top_of_subset Set.inter_subset_left hfinite)).trans
    (variable_tube_inter_ball_volume b u p ell hr (by dsimp [delta]; positivity) hu)
  have he : 2*delta*(2*(n+3:ℝ))^n=lam*c0/2 := by
    change 2*(lam*c0/(4*A))*A=lam*c0/2
    field_simp; ring
  rw [he] at hsmall
  have hlower := mul_le_mul_of_nonneg_left (hvol r ell hr hell b u hb hu) hlam.le
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.variable_tube_shear_coordinate_bound
#print axioms KakeyaTwoScale.variable_tube_in_height_box
#print axioms KakeyaTwoScale.variable_tube_inter_ball_volume
#print axioms KakeyaTwoScale.variable_tube_volume_upper

#print axioms KakeyaTwoScale.unit_tube_subset_variable
#print axioms KakeyaTwoScale.variable_tube_volume_lower
#print axioms KakeyaTwoScale.variable_tube_retained_capture
