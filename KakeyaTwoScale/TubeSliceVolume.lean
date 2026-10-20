module
public import KakeyaTwoScale.EuclideanTubeSource
public import KakeyaTwoScale.AffineGridVolume

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Coordinates of the actual tube error, including its endpoint caps. -/
theorem tube_coordinate_error {n : ℕ} (b u x : EuclideanSpace ℝ (Fin (n+1)))
    {r : ℝ} (hx : x ∈ euclideanTube b u r) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, ∀ j, |x j-(b j+t*u j)| ≤ r := by
  obtain ⟨t,ht,hd⟩ := hx
  refine ⟨t,ht,fun j => ?_⟩
  have hh := PiLp.norm_apply_le (x-(b+t • u)) j
  have he : ‖x-(b+t • u)‖ < r := by simpa [dist_eq_norm] using hd
  simpa [Real.norm_eq_abs] using hh.trans he.le

/-- A large coordinate gives a uniform shear-width bound without rotating space. -/
theorem tube_shear_coordinate_bound {n : ℕ} (i : Fin (n+1))
    (b u x : EuclideanSpace ℝ (Fin (n+1))) {r : ℝ} (hr : 0 ≤ r)
    (hu : ‖u‖=1) (hi : 1/(n+2:ℝ) ≤ |u i|)
    (hx : x ∈ euclideanTube b u r) (j : Fin n) :
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
  obtain ⟨t,ht,he⟩ := tube_coordinate_error b u x hx
  have hid : x (i.succAbove j)-b (i.succAbove j)-(x i-b i)*chartSlope i u j =
      (x (i.succAbove j)-(b (i.succAbove j)+t*u (i.succAbove j)))-
      (x i-(b i+t*u i))*chartSlope i u j := by
    unfold chartSlope; field_simp; ring
  rw [hid]
  have hh := norm_sub_le (x (i.succAbove j)-(b (i.succAbove j)+t*u (i.succAbove j)))
    ((x i-(b i+t*u i))*chartSlope i u j)
  simp only [Real.norm_eq_abs,abs_mul] at hh
  have hm := mul_le_mul (he i) hratio (abs_nonneg _) hr
  linarith [he (i.succAbove j)]

/-- The exact sheared coordinate box enclosing a tube in a height interval. -/
def tubeSliceBox {n : ℕ} (i : Fin (n+1))
    (b u : EuclideanSpace ℝ (Fin (n+1))) (lo hi D : ℝ) : Set (EuclideanSpace ℝ (Fin (n+1))) :=
  euclideanSplit i ⁻¹' gridShear
    (fun j => b (i.succAbove j)-b i*chartSlope i u j) (chartSlope i u) ⁻¹'
    (Set.Icc lo hi ×ˢ Set.Icc (fun _ : Fin n => -D) (fun _ => D))

theorem tubeSliceBox_volume {n : ℕ} (i : Fin (n+1))
    (b u : EuclideanSpace ℝ (Fin (n+1))) (lo hi D : ℝ)
    (hlh : lo ≤ hi) (hD : 0 ≤ D) :
    volume.real (tubeSliceBox i b u lo hi D)=(hi-lo)*(2*D)^n := by
  have hbox : MeasurableSet (Set.Icc lo hi ×ˢ Set.Icc (fun _ : Fin n => -D) (fun _ => D)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hs := hbox.preimage (measurable_gridShear
    (fun j => b (i.succAbove j)-b i*chartSlope i u j) (chartSlope i u))
  unfold tubeSliceBox Measure.real
  rw [(euclideanSplit_measurePreserving i).measure_preimage hs.nullMeasurableSet,
    volume_gridShear_preimage _ _ _ hbox,Measure.volume_eq_prod,Measure.prod_prod,
    ENNReal.toReal_mul,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hlh),
    Real.volume_Icc_pi_toReal (show (fun _ : Fin n => -D) ≤ (fun _ => D) by intro j; linarith)]
  simp [show D- -D=2*D by ring]

theorem tubeSliceBox_finite {n : ℕ} (i : Fin (n+1))
    (b u : EuclideanSpace ℝ (Fin (n+1))) (lo hi D : ℝ) :
    volume (tubeSliceBox i b u lo hi D) ≠ ⊤ := by
  have hbox : MeasurableSet (Set.Icc lo hi ×ˢ Set.Icc (fun _ : Fin n => -D) (fun _ => D)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hs := hbox.preimage (measurable_gridShear
    (fun j => b (i.succAbove j)-b i*chartSlope i u j) (chartSlope i u))
  unfold tubeSliceBox
  rw [(euclideanSplit_measurePreserving i).measure_preimage hs.nullMeasurableSet,
    volume_gridShear_preimage _ _ _ hbox]
  exact (isCompact_Icc.prod isCompact_Icc).measure_ne_top

theorem tube_in_height_box {n : ℕ} (i : Fin (n+1))
    (b u x : EuclideanSpace ℝ (Fin (n+1))) {r lo hi : ℝ} (hr : 0 ≤ r)
    (hu : ‖u‖=1) (hiu : 1/(n+2:ℝ) ≤ |u i|)
    (hx : x ∈ euclideanTube b u r) (ht : x i ∈ Set.Icc lo hi) :
    x ∈ tubeSliceBox i b u lo hi ((n+3:ℝ)*r) := by
  refine ⟨ht,?_,?_⟩
  · intro j
    have hh := (abs_le.mp (tube_shear_coordinate_bound i b u x hr hu hiu hx j)).1
    change -((n+3:ℝ)*r) ≤ x (i.succAbove j)-
      (b (i.succAbove j)-b i*chartSlope i u j+x i*chartSlope i u j)
    linarith
  · intro j
    have hh := (abs_le.mp (tube_shear_coordinate_bound i b u x hr hu hiu hx j)).2
    change x (i.succAbove j)-
      (b (i.succAbove j)-b i*chartSlope i u j+x i*chartSlope i u j) ≤ (n+3:ℝ)*r
    linarith

/-- A capsule loses at most O(delta r^n) volume inside any ball of radius delta. -/
theorem euclideanTube_inter_ball_volume {n : ℕ}
    (b u p : EuclideanSpace ℝ (Fin (n+1))) {r delta : ℝ}
    (hr : 0 < r) (hd : 0 ≤ delta) (hu : ‖u‖=1) :
    volume.real (euclideanTube b u r ∩ Metric.ball p delta) ≤
      2*delta*(2*(n+3:ℝ))^n*r^n := by
  obtain ⟨i,hi⟩ := unit_large_coordinate u hu
  have hs : euclideanTube b u r ∩ Metric.ball p delta ⊆
      tubeSliceBox i b u (p i-delta) (p i+delta) ((n+3:ℝ)*r) := by
    intro x hx
    apply tube_in_height_box i b u x hr.le hu hi hx.1
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
theorem euclideanTube_volume_upper {n : ℕ}
    (b u : EuclideanSpace ℝ (Fin (n+1))) {r : ℝ}
    (hr : 0 < r) (hrone : r ≤ 1/2) (hu : ‖u‖=1) :
    volume.real (euclideanTube b u r) ≤ 3*(2*(n+3:ℝ))^n*r^n := by
  obtain ⟨i,hi⟩ := unit_large_coordinate u hu
  have hs : euclideanTube b u r ⊆
      tubeSliceBox i b u (b i-1-r) (b i+1+r) ((n+3:ℝ)*r) := by
    intro x hx
    apply tube_in_height_box i b u x hr.le hu hi hx
    obtain ⟨t,ht,he⟩ := tube_coordinate_error b u x hx
    have hui : |u i| ≤ 1 := by simpa [hu,Real.norm_eq_abs] using PiLp.norm_apply_le u i
    have htui : |t*u i| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_left hui ht.1).trans (by simpa using ht.2)
    obtain ⟨ha,hb⟩ := abs_le.mp htui
    obtain ⟨hc,hd⟩ := abs_le.mp (he i)
    constructor <;> linarith
  have hh := measureReal_mono hs (tubeSliceBox_finite i b u _ _ _)
  rw [tubeSliceBox_volume i b u _ _ _ (by linarith) (by positivity)] at hh
  have hl : b i+1+r-(b i-1-r) ≤ 3 := by linarith
  have hm := mul_le_mul_of_nonneg_right hl (show 0 ≤ (2*((n+3:ℝ)*r))^n by positivity)
  have hf := hh.trans hm
  rw [show 2*((n+3:ℝ)*r)=(2*(n+3:ℝ))*r by ring,mul_pow] at hf
  convert hf using 1; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tube_coordinate_error
#print axioms KakeyaTwoScale.tube_shear_coordinate_bound
#print axioms KakeyaTwoScale.tubeSliceBox_volume
#print axioms KakeyaTwoScale.tubeSliceBox_finite
#print axioms KakeyaTwoScale.tube_in_height_box
#print axioms KakeyaTwoScale.euclideanTube_inter_ball_volume

#print axioms KakeyaTwoScale.euclideanTube_volume_upper
