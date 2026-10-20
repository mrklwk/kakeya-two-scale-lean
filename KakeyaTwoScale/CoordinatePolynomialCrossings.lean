module
public import KakeyaTwoScale.PolynomialZeroNull
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Set.Card

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Literal coordinate-line zero fiber. Whole zero lines are retained. -/
def coordinateZeroFiber {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (y : Fin n→ℝ) : Set ℝ := {t | MvPolynomial.eval (Fin.cons t y) P=0}

/-- Extended cardinality preserves infinite exceptional fibers. -/
def coordinateCrossingCount {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (y : Fin n→ℝ) : ℝ≥0∞ := (coordinateZeroFiber P y).encard.toENNReal

/-- The genuine univariate restriction has degree bounded by total degree;
no degree bound for a specialization is supplied as a hypothesis. -/
theorem coordinate_restriction_degree {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (y : Fin n→ℝ) :
    (Polynomial.map (MvPolynomial.eval y) (MvPolynomial.finSuccEquiv ℝ n P)).natDegree ≤ P.totalDegree := by
  apply Polynomial.natDegree_map_le.trans
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact MvPolynomial.degreeOf_le_totalDegree P 0

/-- Nonzero coefficient polynomial excludes identically zero fibers almost
 everywhere, including the zero-dimensional base. -/
theorem ae_coordinate_restriction_ne_zero {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0) :
    ∀ᵐ y : Fin n→ℝ, Polynomial.map (MvPolynomial.eval y) (MvPolynomial.finSuccEquiv ℝ n P)≠0 := by
  classical
  let q := MvPolynomial.finSuccEquiv ℝ n P
  have hq : q≠0 := by
    intro h
    exact hP ((MvPolynomial.finSuccEquiv ℝ n).injective (h.trans (map_zero _).symm))
  obtain ⟨j,hj⟩ : ∃ j, q.coeff j≠0 := by
    by_contra! h
    exact hq (Polynomial.ext fun j => by simpa using h j)
  have ha : ∀ᵐ y : Fin n→ℝ, MvPolynomial.eval y (q.coeff j)≠0 := by
    apply ae_iff.mpr
    simpa only [not_not] using polynomial_zero_volume (q.coeff j) hj
  filter_upwards [ha] with y hy
  intro h
  have hc := congrArg (fun f : Polynomial ℝ => f.coeff j) h
  exact hy (by simpa [q] using hc)

/-- Distinct roots, not roots with multiplicity; infinity is allowed only on
an exceptional null base set. Repeated factors cause no false regularity premise. -/
theorem ae_coordinate_zero_fiber_encard_le {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0) :
    ∀ᵐ y : Fin n→ℝ, (coordinateZeroFiber P y).encard ≤ (P.totalDegree:ℕ∞) := by
  classical
  filter_upwards [ae_coordinate_restriction_ne_zero P hP] with y hy
  let q := Polynomial.map (MvPolynomial.eval y) (MvPolynomial.finSuccEquiv ℝ n P)
  have hq : q≠0 := hy
  have he : coordinateZeroFiber P y=(q.roots.toFinset : Set ℝ) := by
    ext t
    simp only [coordinateZeroFiber,Set.mem_ofPred_eq,Finset.mem_coe,Multiset.mem_toFinset,
      Polynomial.mem_roots hq,Polynomial.IsRoot]
    rw [MvPolynomial.eval_eq_eval_mv_eval']
  rw [he,Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast (q.roots.toFinset_card_le.trans (q.card_roots')).trans
    (coordinate_restriction_degree P y)

/-- The extended-real projection count is bounded almost everywhere. -/
theorem ae_coordinate_crossing_count_le {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0) :
    ∀ᵐ y : Fin n→ℝ, coordinateCrossingCount P y ≤ (P.totalDegree:ℝ≥0∞) := by
  filter_upwards [ae_coordinate_zero_fiber_encard_le P hP] with y hy
  simpa [coordinateCrossingCount] using ENat.toENNReal_mono hy

/-- Projection-count budget over any base set, with its intrinsic coordinate
Lebesgue measure. This does not assert a hypersurface area formula. -/
theorem coordinate_crossing_integral_le {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P≠0) (D : Set (Fin n→ℝ)) :
    (∫⁻ y in D, coordinateCrossingCount P y) ≤ (P.totalDegree:ℝ≥0∞)*volume D := by
  have h := lintegral_mono_ae (ae_restrict_of_ae (s:=D) (ae_coordinate_crossing_count_le P hP))
  simpa only [lintegral_const,Measure.restrict_apply_univ] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinate_restriction_degree
#print axioms KakeyaTwoScale.ae_coordinate_restriction_ne_zero
#print axioms KakeyaTwoScale.ae_coordinate_zero_fiber_encard_le
#print axioms KakeyaTwoScale.ae_coordinate_crossing_count_le
#print axioms KakeyaTwoScale.coordinate_crossing_integral_le
