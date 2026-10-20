module
public import KakeyaTwoScale.FlatCylinderCentralGeometry

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Move an axial parameter into a fixed interior margin at a bounded cost. -/
theorem cylinder_interior_parameter {r L t : ℝ} (hr : 0<r) (hrL : r≤L)
    (ht0 : 0<t) (htL : t<L) :
    ∃ q : ℝ, r/4≤q ∧ q≤L-r/4 ∧ |q-t|≤r/4 := by
  by_cases hlo : t<r/4
  · refine ⟨r/4,le_rfl,by linarith,?_⟩
    rw [abs_le]
    constructor <;> linarith
  · by_cases hhi : L-r/4<t
    · refine ⟨L-r/4,by linarith,le_rfl,?_⟩
      rw [abs_le]
      constructor <;> linarith
    · exact ⟨t,by linarith,by linarith,by simp; positivity⟩

/-- A quantitative interior ball in a unit-axis cylinder. -/
theorem flatCylinder_interior_ball {d : ℕ}
    (b u e : EuclideanSpace ℝ (Fin d)) (L r q : ℝ)
    (hu : ‖u‖=1) (hr : 0<r) (hq0 : r/4≤q) (hqL : q≤L-r/4)
    (he : inner ℝ u e=0) (her : ‖e‖≤3*r/4) :
    ball (b+q • u+e) (r/8) ⊆ flatCylinder b u L r := by
  intro z hz
  let w := z-(b+q • u+e)
  let a := inner ℝ u w
  have hw : ‖w‖<r/8 := by simpa only [w,mem_ball,dist_eq_norm] using hz
  have ha : |a|<r/8 := by
    have h := abs_real_inner_le_norm u w
    rw [hu,one_mul] at h
    exact h.trans_lt hw
  have heq : z-(b+(q+a) • u)=e+(w-a • u) := by dsimp [w]; module
  refine ⟨q+a,?_,?_,?_,?_⟩
  · have := (abs_lt.mp ha).1; linarith
  · have := (abs_lt.mp ha).2; linarith
  · rw [heq,inner_add_right,he,inner_sub_right,inner_smul_right,
      real_inner_self_eq_norm_sq,hu]
    dsimp [a]
    ring
  · rw [heq]
    have hh := norm_add_le e (w-a • u)
    have hp := unit_transverse_error u w hu
    change ‖w-a • u‖≤‖w‖ at hp
    linarith

/-- Every point of an actual cylinder with length at least its width has a
uniform inner ball nearby. The inner ball stays inside the original OPEN cylinder. -/
theorem flatCylinder_local_thickness {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (L r : ℝ)
    (hu : ‖u‖=1) (hr : 0<r) (hrL : r≤L)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x∈flatCylinder b u L r) :
    ∃ y, dist y x<r/2 ∧ ball y (r/8) ⊆ flatCylinder b u L r∩ball x r := by
  obtain ⟨t,ht0,htL,hi,hn⟩ := hx
  obtain ⟨q,hq0,hqL,hqt⟩ := cylinder_interior_parameter hr hrL ht0 htL
  let e := x-(b+t • u)
  let y := b+q • u+(3/4:ℝ) • e
  have hnear : dist y x<r/2 := by
    have heq : y-x=(q-t) • u-(1/4:ℝ) • e := by dsimp [y,e]; module
    rw [dist_eq_norm,heq]
    have h := norm_sub_le ((q-t) • u) ((1/4:ℝ) • e)
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one] at h
    norm_num at h
    change ‖e‖<r at hn
    linarith
  have hball : ball y (r/8) ⊆ flatCylinder b u L r := by
    apply flatCylinder_interior_ball b u ((3/4:ℝ) • e) L r q hu hr hq0 hqL
    · rw [inner_smul_right,hi,mul_zero]
    · rw [norm_smul,Real.norm_eq_abs]
      norm_num
      change ‖e‖<r at hn
      linarith
  refine ⟨y,hnear,fun z hz => ⟨hball hz,?_⟩⟩
  have hh := dist_triangle z y x
  change dist z y<r/8 at hz
  change dist z x<r
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cylinder_interior_parameter
#print axioms KakeyaTwoScale.flatCylinder_interior_ball
#print axioms KakeyaTwoScale.flatCylinder_local_thickness
