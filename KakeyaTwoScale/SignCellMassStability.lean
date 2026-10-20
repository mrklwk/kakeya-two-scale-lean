module
public import KakeyaTwoScale.PolynomialSignCells
public import Mathlib.Analysis.Normed.Group.Indicator

@[expose] public section

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace KakeyaTwoScale

/-- Constant shifts leave each strict sign unchanged near zero at nonzero values. -/
theorem eventually_shift_signSide (a : ℝ) (ha : a ≠ 0) (b : Bool) :
    ∀ᶠ t : ℝ in 𝓝 0, (if b then 0 < a + t else a + t < 0) ↔
      (if b then 0 < a else a < 0) := by
  have hc : ContinuousAt (fun t : ℝ => a + t) 0 := continuousAt_const.add continuousAt_id
  rcases lt_or_gt_of_ne ha with hn | hp
  · have he := hc.eventually_lt continuousAt_const (by simpa using hn)
    filter_upwards [he] with t ht
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact iff_of_true ht hn
    · exact iff_of_false (not_lt_of_ge (le_of_lt ht)) (not_lt_of_ge (le_of_lt hn))
  · have he := continuousAt_const.eventually_lt hc (by simpa using hp)
    filter_upwards [he] with t ht
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact iff_of_false (not_lt_of_ge (le_of_lt ht)) (not_lt_of_ge (le_of_lt hp))
    · exact iff_of_true ht hp

/-- Every sign-cell mass is continuous under independent constant shifts.
Only the original factors must be nonzero; their null zero sets supply the
almost-everywhere local constancy needed for dominated convergence. -/
theorem continuousAt_shiftedSignCell_mass {n s : ℕ}
    (p : Fin s → MvPolynomial (Fin n) ℝ) (hp : ∀ i, p i ≠ 0)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w)
    (b : Fin s → Bool) :
    ContinuousAt (fun c : Fin s → ℝ =>
      ∫ x in polynomialSignCell (fun i => p i + MvPolynomial.C (c i)) b, w x) 0 := by
  classical
  let S := fun c : Fin s → ℝ => polynomialSignCell (fun i => p i + MvPolynomial.C (c i)) b
  have hm : ∀ c, MeasurableSet (S c) := fun c => (isOpen_polynomialSignCell _ _).measurableSet
  have hz : ∀ᵐ x : EuclideanSpace ℝ (Fin n), ∀ i,
      MvPolynomial.eval (fun j => x j) (p i) ≠ 0 := by
    rw [ae_all_iff]
    intro i
    apply ae_iff.mpr
    simpa only [not_not] using polynomial_zero_volume_euclidean (p i) (hp i)
  have hcont : ContinuousAt (fun c => ∫ x, (S c).indicator w x) 0 := by
    apply continuousAt_of_dominated (bound := fun x => ‖w x‖)
    · exact Eventually.of_forall (fun c => (hw.indicator (hm c)).aestronglyMeasurable)
    · exact Eventually.of_forall (fun c => Eventually.of_forall (fun x =>
        norm_indicator_le_norm_self _ _))
    · exact hw.norm
    · filter_upwards [hz] with x hx
      have he : ∀ᶠ c : Fin s → ℝ in 𝓝 0, ∀ i,
          (if b i then 0 < MvPolynomial.eval (fun j => x j) (p i) + c i
           else MvPolynomial.eval (fun j => x j) (p i) + c i < 0) ↔
          (if b i then 0 < MvPolynomial.eval (fun j => x j) (p i)
           else MvPolynomial.eval (fun j => x j) (p i) < 0) := by
        apply Filter.eventually_all.mpr
        intro i
        exact ((continuous_apply i).continuousAt (x := (0 : Fin s → ℝ))).tendsto.eventually
          (eventually_shift_signSide _ (hx i) (b i))
      apply (continuousAt_const (y := (S 0).indicator w x)).congr_of_eventuallyEq
      filter_upwards [he] with c hc
      have hmem : x ∈ S c ↔ x ∈ S 0 := by
        change (∀ i, x ∈ polynomialSignSide (p i + MvPolynomial.C (c i)) (b i)) ↔
          (∀ i, x ∈ polynomialSignSide (p i + MvPolynomial.C (0 : ℝ)) (b i))
        apply forall_congr'
        intro i
        have hi := hc i
        cases hb : b i <;> simpa [polynomialSignSide, hb] using hi
      by_cases hx : x ∈ S c
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx)]
      · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.mpr hx)]
  simpa only [integral_indicator (hm _)] using hcont

/-- A single neighborhood works for all sign patterns, so the independently
shifted factors can subsequently be chosen in any dense set of parameters. -/
theorem eventually_all_shiftedSignCell_masses_close {n s : ℕ}
    (p : Fin s → MvPolynomial (Fin n) ℝ) (hp : ∀ i, p i ≠ 0)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ c : Fin s → ℝ in 𝓝 0, ∀ b : Fin s → Bool,
      |(∫ x in polynomialSignCell (fun i => p i + MvPolynomial.C (c i)) b, w x) -
       (∫ x in polynomialSignCell p b, w x)| < ε := by
  apply Filter.eventually_all.mpr
  intro b
  have h := (continuousAt_shiftedSignCell_mass p hp w hw b).tendsto.eventually
    (Metric.ball_mem_nhds _ hε)
  simpa [Metric.mem_ball, Real.dist_eq] using h

/-- The factor-two relaxation in the partition proof survives all sufficiently
small independent shifts when all initial sign cells have mass m>0. -/
theorem eventually_shiftedSignCell_mass_bounds {n s : ℕ}
    (p : Fin s → MvPolynomial (Fin n) ℝ) (hp : ∀ i, p i ≠ 0)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w)
    (m : ℝ) (hm : 0 < m)
    (hbalanced : ∀ b, (∫ x in polynomialSignCell p b, w x) = m) :
    ∀ᶠ c : Fin s → ℝ in 𝓝 0, ∀ b : Fin s → Bool,
      m / 2 < (∫ x in polynomialSignCell (fun i => p i + MvPolynomial.C (c i)) b, w x) ∧
      (∫ x in polynomialSignCell (fun i => p i + MvPolynomial.C (c i)) b, w x) < 2*m := by
  filter_upwards [eventually_all_shiftedSignCell_masses_close p hp w hw (m/2)
    (half_pos hm)] with c hc
  intro b
  have h := hc b
  rw [hbalanced b, abs_lt] at h
  constructor <;> linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_shift_signSide
#print axioms KakeyaTwoScale.continuousAt_shiftedSignCell_mass
#print axioms KakeyaTwoScale.eventually_all_shiftedSignCell_masses_close
#print axioms KakeyaTwoScale.eventually_shiftedSignCell_mass_bounds
