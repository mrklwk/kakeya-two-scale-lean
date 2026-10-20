module
public import KakeyaTwoScale.SpherePacking
public import KakeyaTwoScale.EuclideanCharts
public import KakeyaTwoScale.EuclideanTubeSource

@[expose] public section

open MeasureTheory Metric Module
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Packing in the actual horizontal parameter space. The exponent is its
linear dimension, and both radii remain explicit. -/
theorem sharp_ball_packing {X J : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (G : Finset J) (v : J → X) (center : X) (d R : ℝ)
    (hd : 0 < d) (hR : 0 ≤ R)
    (hbound : ∀ j ∈ G, dist (v j) center ≤ R)
    (hsep : ∀ j ∈ G, ∀ k ∈ G, j ≠ k → d ≤ dist (v j) (v k)) :
    (G.card:ℝ)*d^(finrank ℝ X) ≤ (3*R+d)^(finrank ℝ X) := by
  borelize X
  let mu : Measure X := Measure.addHaar
  let t := d/3
  have ht : 0 < t := by dsimp [t]; positivity
  have houter : 0 < R+t := by positivity
  let U := ⋃ j ∈ G, ball (v j) t
  have hdisjoint : Set.PairwiseDisjoint (↑G : Set J) (fun j => ball (v j) t) := by
    intro j hj k hk hne
    apply ball_disjoint_ball
    have hh := hsep j hj k hk hne
    dsimp [t]; linarith
  have hsub : U ⊆ ball center (R+t) := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    have hh := dist_triangle x (v j) center
    have hb := hbound j hj
    change dist x (v j) < t at hx
    change dist x center < R+t
    linarith
  have hvol (x : X) (s : ℝ) (hs : 0 < s) :
      mu.real (ball x s)=s^(finrank ℝ X)*mu.real (ball (0:X) 1) := by
    rw [Measure.real,mu.addHaar_ball_of_pos x hs,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hU : mu.real U=(G.card:ℝ)*t^(finrank ℝ X)*mu.real (ball (0:X) 1) := by
    rw [show U=⋃ j ∈ G, ball (v j) t from rfl,
      measureReal_biUnion_finset hdisjoint (fun _ _ => measurableSet_ball)]
    simp only [hvol _ t ht,Finset.sum_const,nsmul_eq_mul]
    ring
  have hunitpos : 0 < mu.real (ball (0:X) 1) :=
    ENNReal.toReal_pos (measure_ball_pos mu (0:X) (by norm_num)).ne' measure_ball_lt_top.ne
  have hm := measureReal_mono hsub (show mu (ball center (R+t)) ≠ ⊤ from measure_ball_lt_top.ne)
  rw [hU,hvol center (R+t) houter] at hm
  have hh := mul_le_mul_of_nonneg_right ((mul_le_mul_iff_left₀ hunitpos).mp hm)
    (show (0:ℝ) ≤ 3^(finrank ℝ X) by positivity)
  have he : t*3=d := by dsimp [t]; ring
  have he' : (R+t)*3=3*R+d := by dsimp [t]; ring
  simpa only [mul_assoc,← mul_pow,he,he'] using hh

/-- A radius-C rho cap of delta-separated horizontal slopes has the exact
rho/delta power needed by coarse parent weights. -/
theorem horizontal_cap_packing {n : ℕ} {J : Type*} (G : Finset J)
    (v : J → Fin n → ℝ) (center : Fin n → ℝ) (d r C : ℝ)
    (hd : 0 < d) (hdr : d ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ j ∈ G, dist (v j) center ≤ C*r)
    (hsep : ∀ j ∈ G, ∀ k ∈ G, j ≠ k → d ≤ dist (v j) (v k)) :
    (G.card:ℝ)*(d/r)^n ≤ (3*C+1)^n := by
  have hr : 0 < r := hd.trans_le hdr
  have hh := sharp_ball_packing G v center d (C*r) hd (by positivity) hbound hsep
  have hdim : finrank ℝ (Fin n → ℝ)=n := by simp
  rw [hdim] at hh
  have hup : (3*(C*r)+d)^n ≤ ((3*C+1)*r)^n := by
    gcongr
    nlinarith
  have hmain := hh.trans hup
  rw [mul_pow] at hmain
  rw [div_pow,← mul_div_assoc]
  exact (div_le_iff₀ (pow_pos hr n)).mpr hmain

/-- Inverse chart control on unit directions with height coordinate bounded
away from zero. Signs are allowed; the graph chart is projectively invariant. -/
theorem chartSlope_dist_le {n : ℕ} (i : Fin (n+1))
    (u v : EuclideanSpace ℝ (Fin (n+1))) (hv : ‖v‖=1)
    (h : ℝ) (hh : 0 < h) (huheight : h ≤ |u i|) (hvheight : h ≤ |v i|) :
    dist (chartSlope i u) (chartSlope i v) ≤ (1/h+1/(h*h))*dist u v := by
  have hui : u i ≠ 0 := abs_pos.mp (hh.trans_le huheight)
  have hvi : v i ≠ 0 := abs_pos.mp (hh.trans_le hvheight)
  apply (dist_pi_le_iff (by positivity)).mpr
  intro j
  have hcoord : |u (i.succAbove j)-v (i.succAbove j)| ≤ dist u v := by
    simpa [dist_eq_norm,Real.norm_eq_abs] using PiLp.norm_apply_le (u-v) (i.succAbove j)
  have hheight : |v i-u i| ≤ dist u v := by
    have hx := PiLp.norm_apply_le (u-v) i
    simpa [dist_eq_norm,Real.norm_eq_abs,abs_sub_comm] using hx
  have hvcoord : |v (i.succAbove j)| ≤ 1 := by
    simpa [hv,Real.norm_eq_abs] using PiLp.norm_apply_le v (i.succAbove j)
  rw [Real.dist_eq]
  change |u (i.succAbove j)/u i-v (i.succAbove j)/v i| ≤ _
  have he : u (i.succAbove j)/u i-v (i.succAbove j)/v i =
      (u (i.succAbove j)-v (i.succAbove j))/u i+
        v (i.succAbove j)*(v i-u i)/(u i*v i) := by field_simp; ring
  rw [he]
  calc
    _ ≤ |(u (i.succAbove j)-v (i.succAbove j))/u i|+
        |v (i.succAbove j)*(v i-u i)/(u i*v i)| := abs_add_le _ _
    _ = |u (i.succAbove j)-v (i.succAbove j)|/|u i|+
        |v (i.succAbove j)| *|v i-u i|/(|u i| *|v i|) := by rw [abs_div,abs_div,abs_mul,abs_mul]
    _ ≤ dist u v/h+1*dist u v/(h*h) := by
      gcongr
    _ = _ := by ring

theorem chartSlope_neg {n : ℕ} (i : Fin (n+1))
    (u : EuclideanSpace ℝ (Fin (n+1))) : chartSlope i (-u)=chartSlope i u := by
  ext j
  simp [chartSlope]

theorem source_cap_chord_choice {n : ℕ}
    (u e : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1) (he : ‖e‖=1)
    (r : ℝ) (hcap : Real.arccos |inner ℝ u e| ≤ r) :
    dist u e ≤ r ∨ dist u (-e) ≤ r := by
  rw [arccos_abs_eq_min,min_le_iff] at hcap
  have hangle : InnerProductGeometry.angle u e ≤ r ∨ InnerProductGeometry.angle u (-e) ≤ r := by
    simpa [InnerProductGeometry.angle,hu,he,inner_neg_right] using hcap
  exact hangle.imp ((unit_direction_angle_bounds u e hu he).1.trans)
    ((unit_direction_angle_bounds u (-e) hu (by simpa using he)).1.trans)

/-- Two directions in one unoriented cap have close graph slopes when their
height coordinates are bounded away from zero. No assumption on cap-center
height is needed, and antipodal signs are explicitly handled. -/
theorem source_cap_chart_diameter {n : ℕ} (i : Fin (n+1))
    (u v e : EuclideanSpace ℝ (Fin (n+1)))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (he : ‖e‖=1)
    (h r : ℝ) (hh : 0 < h) (huheight : h ≤ |u i|) (hvheight : h ≤ |v i|)
    (hucap : Real.arccos |inner ℝ u e| ≤ r)
    (hvcap : Real.arccos |inner ℝ v e| ≤ r) :
    dist (chartSlope i u) (chartSlope i v) ≤ 2*(1/h+1/(h*h))*r := by
  have hpair : dist u v ≤ 2*r ∨ dist u (-v) ≤ 2*r := by
    rcases source_cap_chord_choice u e hu he r hucap with hup | hun <;>
      rcases source_cap_chord_choice v e hv he r hvcap with hvp | hvn
    · left
      have hh := dist_triangle u e v
      rw [dist_comm e v] at hh
      linarith
    · right
      have hh := dist_triangle u e (-v)
      have heq : dist e (-v) = dist v (-e) := by simpa [dist_comm] using (dist_neg_neg (-e) v)
      rw [heq] at hh
      linarith
    · right
      have hh := dist_triangle u (-e) (-v)
      rw [dist_neg_neg,dist_comm e v] at hh
      linarith
    · left
      have hh := dist_triangle u (-e) v
      rw [dist_comm (-e) v] at hh
      linarith
  rcases hpair with hp | hn
  · have hi := chartSlope_dist_le i u v hv h hh huheight hvheight
    have hx := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1/h+1/(h*h) by positivity)
    nlinarith
  · have hi := chartSlope_dist_le i u (-v) (by simpa using hv) h hh huheight (by simpa using hvheight)
    rw [chartSlope_neg] at hi
    have hx := mul_le_mul_of_nonneg_left hn (show 0 ≤ 1/h+1/(h*h) by positivity)
    nlinarith

/-- The literal source coarse angular weight bound. Every original child
is counted once under its fixed parent assignment. Packing is in the m-
dimensional horizontal slope space, so the normalization has power m.
The direction family here must already be realized as unit chart directions;
this does not identify horizontal tubes with Euclidean unit capsules. -/
theorem assigned_coarse_angular_cap {n : ℕ} {J P : Type*}
    (G : Finset J) (parents : Finset P) (assign : J → P)
    (v : J → Fin n → ℝ) (u : P → EuclideanSpace ℝ (Fin (n+1)))
    (i : Fin (n+1)) (d r h : ℝ) (hd : 0 < d) (hdr : d ≤ r) (hh : 0 < h)
    (hu : ∀ p ∈ parents, ‖u p‖=1)
    (hheight : ∀ p ∈ parents, h ≤ |u p i|)
    (hclose : ∀ j ∈ G, dist (v j) (chartSlope i (u (assign j))) ≤ r)
    (hsep : ∀ j ∈ G, ∀ k ∈ G, j ≠ k → d ≤ dist (v j) (v k))
    (e : EuclideanSpace ℝ (Fin (n+1))) (he : ‖e‖=1) :
    (∑ p ∈ parents.filter (fun p => Real.arccos |inner ℝ (u p) e| ≤ r),
      ((G.filter (fun j => assign j=p)).card:ℝ)*(d/r)^n) ≤
      (3*(1+2*(1/h+1/(h*h)))+1)^n := by
  let Q := parents.filter (fun p => Real.arccos |inner ℝ (u p) e| ≤ r)
  let S := G.filter (fun j => assign j ∈ Q)
  have hmap : ∀ j ∈ S, assign j ∈ Q := fun j hj => (Finset.mem_filter.mp hj).2
  have hfiber (p) (hp : p ∈ Q) : S.filter (fun j => assign j=p)=G.filter (fun j => assign j=p) := by
    ext j
    simp only [S,Finset.mem_filter]
    by_cases hj : assign j=p <;> simp [hj,hp]
  have hsum : (∑ p ∈ Q, ((G.filter (fun j => assign j=p)).card:ℝ))=(S.card:ℝ) := by
    have hcard := Finset.card_eq_sum_card_fiberwise hmap
    have hrw : (∑ p ∈ Q, (S.filter (fun j => assign j=p)).card)=
        ∑ p ∈ Q, (G.filter (fun j => assign j=p)).card :=
      Finset.sum_congr rfl (fun p hp => congrArg Finset.card (hfiber p hp))
    rw [hrw] at hcard
    exact_mod_cast hcard.symm
  change (∑ p ∈ Q, ((G.filter (fun j => assign j=p)).card:ℝ)*(d/r)^n) ≤ _
  rw [← Finset.sum_mul,hsum]
  by_cases hS : S.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hS
    have hp₀ := Finset.mem_filter.mp (hmap j₀ hj₀)
    apply horizontal_cap_packing S v (chartSlope i (u (assign j₀))) d r
      (1+2*(1/h+1/(h*h))) hd hdr (by positivity) ?_ ?_
    · intro j hj
      have hp := Finset.mem_filter.mp (hmap j hj)
      have hdiam := source_cap_chart_diameter i (u (assign j)) (u (assign j₀)) e
        (hu _ hp.1) (hu _ hp₀.1) he h r hh (hheight _ hp.1) (hheight _ hp₀.1) hp.2 hp₀.2
      have hdist := dist_triangle (v j) (chartSlope i (u (assign j))) (chartSlope i (u (assign j₀)))
      have hnear := hclose j (Finset.mem_filter.mp hj).1
      nlinarith
    · intro j hj k hk hjk
      exact hsep j (Finset.mem_filter.mp hj).1 k (Finset.mem_filter.mp hk).1 hjk
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sharp_ball_packing
#print axioms KakeyaTwoScale.horizontal_cap_packing
#print axioms KakeyaTwoScale.chartSlope_dist_le
#print axioms KakeyaTwoScale.chartSlope_neg
#print axioms KakeyaTwoScale.source_cap_chord_choice
#print axioms KakeyaTwoScale.source_cap_chart_diameter
#print axioms KakeyaTwoScale.assigned_coarse_angular_cap
