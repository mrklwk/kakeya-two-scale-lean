module
public import KakeyaTwoScale.VisibilityLowerDirection

@[expose] public section

open MvPolynomial Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Projection of a translated Euclidean ball has a bound independent of its
center. The transverse box is translated with the center. -/
theorem translated_orthogonal_projection {n : ℕ} (r : ℝ) (hr : 0≤r)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (b x : Fin (n+1) → ℝ)
    (hx : ‖(WithLp.toLp 2 (x-b) : EuclideanSpace ℝ (Fin (n+1)))‖≤r) :
    transverseProjection n ((orthogonalCoordinates R).symm x) ∈
      closedBall (transverseProjection n ((orthogonalCoordinates R).symm b)) r := by
  have hh := bounded_orthogonal_projection r hr R (x-b) hx
  simpa only [map_sub,mem_closedBall,dist_eq_norm,sub_zero] using hh

/-- Actual polynomial area on a translated bounded region. The budget pays
only the radius and original degree, never the distance of the region from zero. -/
theorem polynomial_translated_unit_area {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (A : DisjointChartAtlas n {x | eval x P=0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (b : Fin (n+1) → ℝ) (r : ℝ) (hr : 0≤r)
    (hb : ∀x∈K, ‖(WithLp.toLp 2 (x-b) : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1) :
    (A.restrict K hK).directionalArea (WithLp.ofLp u) ≤
      (P.totalDegree : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) r) := by
  obtain ⟨R,hR⟩ := exists_axis_isometry (0 : Fin (n+1)) u hu
  have hh := polynomial_framed_region_budget P hP A R K hK
    (closedBall (transverseProjection n ((orthogonalCoordinates R).symm b)) r)
    measurableSet_closedBall (fun x hx => translated_orthogonal_projection r hr R b x (hb x hx.2))
  rw [orthogonalCoordinates_first_axis,hR] at hh
  simpa only [Real.volume_pi_closedBall _ hr] using hh

/-- Uniform norm bound for every direction on an arbitrary translated region. -/
theorem polynomial_translated_area_norm_le {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (A : DisjointChartAtlas n {x | eval x P=0})
    (K : Set (Fin (n+1) → ℝ)) (hK : MeasurableSet K)
    (b : Fin (n+1) → ℝ) (r : ℝ) (hr : 0≤r)
    (hb : ∀x∈K, ‖(WithLp.toLp 2 (x-b) : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (v : Fin (n+1) → ℝ) :
    (A.restrict K hK).directionalArea v ≤
      ENNReal.ofReal ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (n+1)))‖ *
        ((P.totalDegree : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) r)) := by
  by_cases hv : v=0
  · simp [hv,DisjointChartAtlas.directionalArea_zero]
  obtain ⟨u,hu,he⟩ := coordinate_euclidean_normalization v hv
  have hs := (A.restrict K hK).directionalArea_smul
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (n+1)))‖ (WithLp.ofLp u)
  rw [he,abs_of_nonneg (norm_nonneg _)] at hs
  rw [hs]
  exact mul_le_mul le_rfl (polynomial_translated_unit_area P hP A K hK b r hr hb u hu) zero_le zero_le

/-- A centered unit cube has a uniform Euclidean radius, independent of its
lattice center. A coarse l1 estimate is sufficient for dimension-only constants. -/
theorem visibilityCube_euclidean_radius {N : ℕ} (z x : Fin N → ℝ)
    (hx : x∈visibilityCube z) :
    ‖(WithLp.toLp 2 (x-z) : EuclideanSpace ℝ (Fin N))‖≤(N:ℝ)/2 := by
  have hc (i) : |x i-z i|≤(1:ℝ)/2 := by
    have hh := (dist_pi_le_iff (by norm_num : (0:ℝ)≤1/2)).mp hx i
    simpa only [Real.dist_eq] using hh
  calc
    _ ≤ ∑i, |(x-z) i| := coordinate_norm_le_l1 _
    _ ≤ ∑_i : Fin N, (1:ℝ)/2 := Finset.sum_le_sum (fun i _ => hc i)
    _ = _ := by simp; ring

/-- The local cube budget has no dependence on the family enclosure radius. -/
theorem polynomial_visibilityCube_area_bound {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0)
    (A : DisjointChartAtlas n {x | eval x P=0}) (z : Fin (n+1) → ℝ)
    (v : Fin (n+1) → ℝ) :
    (A.restrict (visibilityCube z) measurableSet_closedBall).directionalArea v ≤
      ENNReal.ofReal ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (n+1)))‖ *
        ((P.totalDegree : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (((n+1:ℕ):ℝ)/2))) :=
  polynomial_translated_area_norm_le P hP A _ measurableSet_closedBall z _ (by positivity)
    (fun x hx => visibilityCube_euclidean_radius z x hx) v

/-- A dimension-only norm budget for every actual coefficient sample, even
when its defining finiteness certificate uses a larger enclosing radius. -/
theorem coefficient_cube_area_bound {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀i, (m i).sum (fun _ e => e)≤D)
    (z : Fin (n+1) → ℝ) (r : ℝ) (hr : 0≤r)
    (hb : ∀x∈visibilityCube z, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (c : CoefficientSphere (Fin d)) (v : EuclideanSpace ℝ (Fin (n+1))) :
    coefficientAreaSeminorm m hm (visibilityCube z) measurableSet_closedBall r hr hb c v ≤
      ((D : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (((n+1:ℕ):ℝ)/2))).toReal * ‖v‖ := by
  have hh := polynomial_visibilityCube_area_bound (coefficientPolynomial m c.val)
    (coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero c))
    (coefficientSphereAtlas m hm c) z (WithLp.ofLp v)
  have hd : ((coefficientPolynomial m c.val).totalDegree : ℝ≥0∞)≤D := by
    exact_mod_cast coefficientPolynomial_degree m hdegree c.val
  have hraw : coefficientSphereArea m hm (visibilityCube z) measurableSet_closedBall c (WithLp.ofLp v) ≤
      ENNReal.ofReal ‖v‖ * ((D : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (((n+1:ℕ):ℝ)/2))) := by
    apply hh.trans
    gcongr
  have ht : ENNReal.ofReal ‖v‖ * ((D : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (((n+1:ℕ):ℝ)/2)))≠∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (by simp) measure_closedBall_lt_top)).ne
  have hh' := ENNReal.toReal_mono ht hraw
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg _)] at hh'
  change (coefficientSphereArea m hm (visibilityCube z) measurableSet_closedBall c (WithLp.ofLp v)).toReal ≤ _
  simpa only [mul_comm] using hh'

/-- The local, center-independent bound survives the literal full-sphere cap
average with no inverse-cap-mass factor. -/
theorem mollified_cube_area_bound {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀i, (m i).sum (fun _ e => e)≤D)
    (z : Fin (n+1) → ℝ) (r : ℝ) (hr : 0≤r)
    (hb : ∀x∈visibilityCube z, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (ε : ℝ) (hε : 0<ε) (c : sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    mollifiedAreaSeminorm m hm hdegree (visibilityCube z) measurableSet_closedBall
      (Or.inr isClosed_closedBall) r hr hb ε c v ≤
      ((D : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (((n+1:ℕ):ℝ)/2))).toReal * ‖v‖ := by
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have hmass : 0<(μ.restrict (ball c ε)).real univ := by
    rw [Measure.real,Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos (isOpen_ball.measure_ne_zero μ (nonempty_ball.mpr hε)) (measure_ne_top μ _)
  apply finiteSeminormAverage_le _ hmass
  intro q w
  exact coefficient_cube_area_bound m hm hdegree z r hr hb (metricCoefficient q) w

end KakeyaTwoScale
#print axioms KakeyaTwoScale.translated_orthogonal_projection
#print axioms KakeyaTwoScale.polynomial_translated_unit_area
#print axioms KakeyaTwoScale.polynomial_translated_area_norm_le
#print axioms KakeyaTwoScale.visibilityCube_euclidean_radius
#print axioms KakeyaTwoScale.polynomial_visibilityCube_area_bound

#print axioms KakeyaTwoScale.coefficient_cube_area_bound
#print axioms KakeyaTwoScale.mollified_cube_area_bound
