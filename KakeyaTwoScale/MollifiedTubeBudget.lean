module
public import KakeyaTwoScale.LatticeTubeBudget

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- A finite sum upper budget survives the same positive cap average exactly. -/
theorem sphereCapAverage_sum_upper {ι : Type*} [Fintype ι] {d : ℕ}
    (ε : ℝ) (hε : 0<ε) (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
    (F : ι → sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ)
    (hi : ∀j, Integrable (F j)
      (((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).restrict (ball p ε)))
    (a : ℝ) (h : ∀q∈ball p ε, ∑j, F j q≤a) :
    (∑j, sphereCapAverage ε (F j) p)≤a := by
  classical
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have hm : 0<μ.real (ball p ε) :=
    ENNReal.toReal_pos (isOpen_ball.measure_ne_zero μ (nonempty_ball.mpr hε)) (measure_ne_top μ _)
  change (∑j, (∫q in ball p ε, F j q ∂μ)/μ.real (ball p ε))≤a
  rw [← Finset.sum_div,← integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply (div_le_iff₀ hm).mpr
  calc
    _ ≤ ∫_q in ball p ε, a ∂μ := integral_mono_ae
      (integrable_finsetSum _ (fun j _ => hi j)) (integrable_const a) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
        exact h q hq)
    _ = _ := by simp [mul_comm]

/-- Uniform real tube budget on each actual coefficient sample. -/
theorem coefficient_lattice_tube_budget {ι : Type*} [Fintype ι] {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀i, (m i).sum (fun _ e => e)≤D)
    (z : ι → Fin (n+1) → ℤ) (hz : Function.Injective z)
    (R : ℝ) (hR : 0≤R)
    (hbound : ∀i x, x∈visibilityCube (fun j => (z i j:ℝ)) →
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤R)
    (b : Fin (n+1) → ℝ) (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1)
    (r : ℝ) (hr : 0≤r)
    (hinc : ∀i, (visibilityCube (fun j => (z i j:ℝ)) ∩ infiniteLineTube b (WithLp.ofLp u) r).Nonempty)
    (c : CoefficientSphere (Fin d)) :
    (∑i, coefficientAreaSeminorm m hm (visibilityCube (fun j => (z i j:ℝ)))
      measurableSet_closedBall R hR (hbound i) c u) ≤
      ((2:ℝ≥0∞)^(n+1)*((D : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (r+((n+1:ℕ):ℝ))))).toReal := by
  have hraw := polynomial_lattice_tube_budget (coefficientPolynomial m c.val)
    (coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero c))
    (coefficientSphereAtlas m hm c) z hz b u hu r hr hinc
  have hd : ((coefficientPolynomial m c.val).totalDegree : ℝ≥0∞)≤D := by
    exact_mod_cast coefficientPolynomial_degree m hdegree c.val
  have hb : (∑i, coefficientSphereArea m hm (visibilityCube (fun j => (z i j:ℝ)))
      measurableSet_closedBall c (WithLp.ofLp u)) ≤
      (2:ℝ≥0∞)^(n+1)*((D : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (r+((n+1:ℕ):ℝ)))) := by
    apply hraw.trans
    gcongr
  have ht : (2:ℝ≥0∞)^(n+1)*((D : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (r+((n+1:ℕ):ℝ))))≠∞ := by
    exact ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne)
  have hh := ENNReal.toReal_mono ht hb
  have hfinite (i : ι) : coefficientSphereArea m hm
      (visibilityCube (fun j => (z i j:ℝ))) measurableSet_closedBall c (WithLp.ofLp u)≠∞ :=
    (coefficientSphereArea_lt_top m hm (visibilityCube (fun j => (z i j:ℝ)))
      measurableSet_closedBall R hR (hbound i) c (WithLp.ofLp u)).ne
  rw [ENNReal.toReal_sum (fun i _ => hfinite i)] at hh
  exact hh

/-- Actual averaged tube budget: the enclosing radius only certifies
integrability and does not enter the conclusion. No limit in epsilon is taken. -/
theorem mollified_lattice_tube_budget {ι : Type*} [Fintype ι] {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀i, (m i).sum (fun _ e => e)≤D)
    (z : ι → Fin (n+1) → ℤ) (hz : Function.Injective z)
    (R : ℝ) (hR : 0≤R)
    (hbound : ∀i x, x∈visibilityCube (fun j => (z i j:ℝ)) →
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤R)
    (b : Fin (n+1) → ℝ) (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1)
    (r : ℝ) (hr : 0≤r)
    (hinc : ∀i, (visibilityCube (fun j => (z i j:ℝ)) ∩ infiniteLineTube b (WithLp.ofLp u) r).Nonempty)
    (ε : ℝ) (hε : 0<ε) (c : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    (∑i, mollifiedCoefficientArea m hm (visibilityCube (fun j => (z i j:ℝ)))
      measurableSet_closedBall R hR (hbound i) ε c u) ≤
      ((2:ℝ≥0∞)^(n+1)*((D : ℝ≥0∞)*volume (closedBall (0 : Fin n → ℝ) (r+((n+1:ℕ):ℝ))))).toReal := by
  apply sphereCapAverage_sum_upper ε hε c
    (fun i q => coefficientAreaSeminorm m hm (visibilityCube (fun j => (z i j:ℝ)))
      measurableSet_closedBall R hR (hbound i) (metricCoefficient q) u)
    (fun i => integrable_metricCoefficientArea m hm hdegree _ measurableSet_closedBall
      (Or.inr isClosed_closedBall) R hR (hbound i) _ u)
  intro q _
  exact coefficient_lattice_tube_budget m hm hdegree z hz R hR hbound b u hu r hr hinc (metricCoefficient q)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sphereCapAverage_sum_upper
#print axioms KakeyaTwoScale.coefficient_lattice_tube_budget
#print axioms KakeyaTwoScale.mollified_lattice_tube_budget
