module
public import KakeyaTwoScale.SphericalAntipodalAverage
public import KakeyaTwoScale.OddSphereZero
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- The existing checked odd-zero theorem on the literal metric coefficient sphere. -/
theorem metric_coefficient_odd_zero {d M : ℕ} (hd : M < d)
    (f : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → EuclideanSpace ℝ (Fin M))
    (hf : Continuous f) (ho : ∀ p, f (metricSphereAntipode d p) = -f p) :
    ∃ p, f p=0 := by
  let a : CoefficientSphere (Fin d) → sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    fun c => ⟨c.val,mem_sphere_zero_iff_norm.mpr c.property⟩
  have ha : Continuous a := continuous_subtype_val.subtype_mk _
  obtain ⟨c,hc⟩ := coefficient_odd_sphere_zero M (by simpa using hd)
    (f ∘ a) (hf.comp ha) (fun c => ho (a c))
  exact ⟨a c,hc⟩

/-- M separated antipodal pairs cannot cover a coefficient sphere with d>M
coefficients. No closedness or measurability of the paired sets is assumed. -/
theorem separated_antipodal_pairs_not_cover {d M : ℕ} (hd : M < d)
    (A : Fin M → Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hsep : ∀ i p, p ∈ A i → metricSphereAntipode d p ∉ closure (A i)) :
    ∃ p, ∀ i, p ∉ A i ∧ metricSphereAntipode d p ∉ A i := by
  let T := metricSphereAntipode d
  have hTT (p) : T (T p) = p := by apply Subtype.ext; exact neg_neg p.val
  let f (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) : EuclideanSpace ℝ (Fin M) :=
    WithLp.toLp 2 (fun i => infDist p (A i) - infDist (T p) (A i))
  have hf : Continuous f := (PiLp.continuous_toLp 2 (fun _ : Fin M => ℝ)).comp
    (continuous_pi (fun i => (continuous_infDist_pt _).sub ((continuous_infDist_pt _).comp T.continuous)))
  have ho (p) : f (T p) = -f p := by
    ext i
    change infDist (T p) (A i) - infDist (T (T p)) (A i) =
      -(infDist p (A i) - infDist (T p) (A i))
    rw [hTT]
    ring
  obtain ⟨p,hp⟩ := metric_coefficient_odd_zero hd f hf ho
  refine ⟨p,?_⟩
  intro i
  have he : infDist p (A i) = infDist (T p) (A i) := by
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin M) => v i) hp
    change infDist p (A i) - infDist (T p) (A i) = 0 at hh
    exact sub_eq_zero.mp hh
  constructor
  · intro hm
    apply hsep i p hm
    exact (mem_closure_iff_infDist_zero ⟨p,hm⟩).mpr (he.symm.trans (infDist_zero_of_mem hm))
  · intro hm
    apply hsep i (T p) hm
    rw [hTT]
    exact (mem_closure_iff_infDist_zero ⟨T p,hm⟩).mpr (he.trans (infDist_zero_of_mem hm))

/-- Source-facing cross-closure separation, not merely disjoint antipodal pairs. -/
theorem cross_closure_antipodal_pairs_not_cover {d M : ℕ} (hd : M < d)
    (A : Fin M → Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hsep : ∀ i, Disjoint (A i) (closure (metricSphereAntipode d ⁻¹' A i))) :
    ∃ p, ∀ i, p ∉ A i ∧ metricSphereAntipode d p ∉ A i := by
  apply separated_antipodal_pairs_not_cover hd A
  intro i p hp ht
  apply Set.disjoint_left.mp (hsep i) hp
  rw [← (metricSphereAntipode d).preimage_closure]
  exact ht

end KakeyaTwoScale
#print axioms KakeyaTwoScale.metric_coefficient_odd_zero
#print axioms KakeyaTwoScale.separated_antipodal_pairs_not_cover
#print axioms KakeyaTwoScale.cross_closure_antipodal_pairs_not_cover
