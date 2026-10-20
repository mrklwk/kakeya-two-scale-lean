module
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open MeasureTheory MvPolynomial

namespace KakeyaTwoScale

/-- A nonzero real polynomial has a Lebesgue-null zero set in every finite dimension. -/
theorem polynomial_zero_volume {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  classical
  induction n with
  | zero =>
    have hc : p.coeff 0 ≠ 0 := by
      intro h
      apply hp
      rw [p.eq_C_of_isEmpty, h, map_zero]
    have he : {x : Fin 0 → ℝ | MvPolynomial.eval x p = 0} = ∅ := by
      ext x
      change (MvPolynomial.eval x p = 0) ↔ False
      rw [p.eq_C_of_isEmpty, MvPolynomial.eval_C]
      exact iff_false_intro hc
    rw [he, measure_empty]
  | succ n ih =>
    let q := MvPolynomial.finSuccEquiv ℝ n p
    have hq : q ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.finSuccEquiv ℝ n).injective (h.trans (map_zero _).symm)
    obtain ⟨k, hk⟩ : ∃ k, q.coeff k ≠ 0 := by
      by_contra! h
      exact hq (Polynomial.ext fun k => by simpa using h k)
    have ha : ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x (q.coeff k) ≠ 0 := by
      apply ae_iff.mpr
      simpa only [not_not] using ih (q.coeff k) hk
    let Z := {x : Fin (n+1) → ℝ | MvPolynomial.eval x p = 0}
    have hZ : MeasurableSet Z := (isClosed_eq p.continuous_eval continuous_const).measurableSet
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have hmp : MeasurePreserving e.symm :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm e
    rw [← hmp.measure_preimage hZ.nullMeasurableSet]
    change (volume.prod volume) (e.symm ⁻¹' Z) = 0
    rw [Measure.prod_apply_symm (hZ.preimage e.symm.measurable)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ha] with x hx
    have hmap : Polynomial.map (MvPolynomial.eval x) q ≠ 0 := by
      intro h
      have hcoeff := congrArg (fun f : Polynomial ℝ => f.coeff k) h
      simpa using hx (by simpa using hcoeff)
    have hfinite := Polynomial.finite_setOfPred_isRoot hmap
    have he : (fun t : ℝ => (t,x)) ⁻¹' (e.symm ⁻¹' Z) =
        {t : ℝ | (Polynomial.map (MvPolynomial.eval x) q).IsRoot t} := by
      ext t
      change (MvPolynomial.eval (e.symm (t,x)) p = 0) ↔ _
      simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero,
        Polynomial.IsRoot, q] using
        congrArg (fun y : ℝ => y = 0) (MvPolynomial.eval_eq_eval_mv_eval' x t p)
    rw [he]
    exact hfinite.measure_zero volume

/-- The same nullity theorem in the Euclidean norm model, including dimension zero. -/
theorem polynomial_zero_volume_euclidean {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p ≠ 0) :
    volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (WithLp.ofLp x) p = 0} = 0 := by
  have hZ : MeasurableSet {x : Fin n → ℝ | MvPolynomial.eval x p = 0} :=
    (isClosed_eq p.continuous_eval continuous_const).measurableSet
  change volume ((WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) ⁻¹'
    {x | MvPolynomial.eval x p = 0}) = 0
  rw [(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    hZ.nullMeasurableSet]
  exact polynomial_zero_volume p hp

#print axioms polynomial_zero_volume
#print axioms polynomial_zero_volume_euclidean
end KakeyaTwoScale
