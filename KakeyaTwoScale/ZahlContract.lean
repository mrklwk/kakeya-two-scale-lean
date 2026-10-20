module
public import KakeyaTwoScale.ZahlExponents
public import KakeyaTwoScale.EuclideanTubeSource
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Euclidean k-volume of the parallelotope, in its Gram-determinant model. -/
def tupleWedgeVolume {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (Matrix.gram ℝ v).det

theorem tupleWedgeVolume_nonneg {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    0 ≤ tupleWedgeVolume v := Real.sqrt_nonneg _

theorem tupleWedgeVolume_eq_zero_of_repeat {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) {i j : Fin k} (hij : i ≠ j) (hv : v i=v j) :
    tupleWedgeVolume v=0 := by
  have hrow : (Matrix.gram ℝ v) i=(Matrix.gram ℝ v) j := by
    funext l
    simp only [Matrix.gram_apply,hv]
  simp [tupleWedgeVolume,Matrix.det_zero_of_row_eq hij hrow]

/-- Ordered tuples, including repetitions as in the paper. No transversality
condition on the full direction family is built into this function. -/
def multilinearKakeyaFunction {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ f : Fin k → Fin N, (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B) *
    ∏ i : Fin k, (T (f i)).indicator (fun _ => (1:ℝ)) x)^((1:ℝ)/k)

theorem multilinearKakeyaFunction_nonneg {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ) (x) :
    0 ≤ multilinearKakeyaFunction k u T B x := by
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg
  intro f _
  apply mul_nonneg (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
  exact Finset.prod_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)

theorem measurable_multilinearKakeyaFunction {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ)
    (hT : ∀ j, MeasurableSet (T j)) :
    Measurable (multilinearKakeyaFunction k u T B) := by
  unfold multilinearKakeyaFunction
  apply Measurable.pow_const
  apply Finset.measurable_sum
  intro f _
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.indicator (hT (f i))

/-- Exact remaining analytic obligation, not an asserted theorem. The norm
is ENNReal-valued, so a divergent norm cannot disappear under toReal.
Constants precede radius and the finite family; angular separation is the
literal unoriented source convention. Intended use has 2<=k<=n. -/
def ZahlCapsuleEstimate (n k : ℕ) : Prop :=
  2 ≤ k ∧ k ≤ n ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r < 1/2 →
    ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin n)),
    (∀ j, ‖u j‖=1) →
    (∀ i j, i ≠ j → r ≤ Real.arccos |inner ℝ (u i) (u j)|) →
    eLpNorm (multilinearKakeyaFunction k u (fun j => euclideanTube (b j) (u j) r) (zahlB n k))
      (ENNReal.ofReal (zahlB n k/(zahlB n k-1))) volume ≤
      ENNReal.ofReal (C*r^(1-(n:ℝ)/zahlB n k-ε)*
        (∑ j, volume.real (euclideanTube (b j) (u j) r))^
          ((n:ℝ)*(zahlB n k-1)/(((n:ℝ)-1)*zahlB n k)))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tupleWedgeVolume_nonneg
#print axioms KakeyaTwoScale.tupleWedgeVolume_eq_zero_of_repeat
#print axioms KakeyaTwoScale.multilinearKakeyaFunction_nonneg
#print axioms KakeyaTwoScale.ZahlCapsuleEstimate

#print axioms KakeyaTwoScale.measurable_multilinearKakeyaFunction
