module
public import KakeyaTwoScale.PartitionDegreeBudget

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem preconnected_polynomial_sign_constant {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : IsPreconnected S) (hne : ∀ x ∈ S, MvPolynomial.eval (fun i => x i) p ≠ 0)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (hy : y ∈ S) :
    (0 < MvPolynomial.eval (fun i => x i) p) ↔
      (0 < MvPolynomial.eval (fun i => y i) p) := by
  have hc : ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) p) S :=
    (p.continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))).continuousOn
  have step : ∀ a ∈ S, ∀ b ∈ S,
      0 < MvPolynomial.eval (fun i => a i) p → 0 < MvPolynomial.eval (fun i => b i) p := by
    intro a ha b hb hpos
    by_contra h
    obtain ⟨z,hz,hzero⟩ := hS.intermediate_value hb ha hc
      (show (0:ℝ) ∈ Set.Icc (MvPolynomial.eval (fun i => b i) p)
        (MvPolynomial.eval (fun i => a i) p) from ⟨le_of_not_gt h, hpos.le⟩)
    exact hne z hz hzero
  exact ⟨step x hx y hy, step y hy x hx⟩

/-- Every nonempty connected subset of the product complement lies inside
one sign region; disconnected sign regions are never mistaken for cells. -/
theorem preconnected_subset_polynomialSignCell {n s : ℕ}
    (p : Fin s → MvPolynomial (Fin n) ℝ) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : IsPreconnected S) (hSn : S.Nonempty)
    (havoid : ∀ x ∈ S, MvPolynomial.eval (fun i => x i) (∏ j, p j) ≠ 0) :
    ∃ b, S ⊆ polynomialSignCell p b := by
  classical
  obtain ⟨x,hx⟩ := hSn
  have hn : ∀ y ∈ S, ∀ i, MvPolynomial.eval (fun j => y j) (p i) ≠ 0 := by
    intro y hy i
    have h := havoid y hy
    rw [map_prod] at h
    exact Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ _)
  refine ⟨fun i => decide (0 < MvPolynomial.eval (fun j => x j) (p i)), ?_⟩
  intro y hy i
  have hi := preconnected_polynomial_sign_constant (p i) S hS (fun y hy => hn y hy i) hx hy
  by_cases hp : 0 < MvPolynomial.eval (fun j => x j) (p i)
  · simpa [polynomialSignSide, hp] using hi.mp hp
  · simp only [polynomialSignSide, hp, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact lt_of_le_of_ne (le_of_not_gt (fun h => hp (hi.mpr h))) (hn y hy i)

/-- Nonnegative density gives the desired mass upper bound on each actual
connected component, once the sign-region masses have been established. -/
theorem polynomial_component_mass_le {n s : ℕ}
    (p : Fin s → MvPolynomial (Fin n) ℝ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) (hwn : ∀ x, 0 ≤ w x)
    (hmass : ∀ b, (∫ x in polynomialSignCell p b, w x) = (∫ x, w x)/(2:ℝ)^s)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : MvPolynomial.eval (fun i => x i) (∏ j, p j) ≠ 0) :
    (∫ y in connectedComponentIn {y | MvPolynomial.eval (fun i => y i) (∏ j, p j) ≠ 0} x, w y)
      ≤ (∫ y, w y)/(2:ℝ)^s := by
  let U := {y : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => y i) (∏ j, p j) ≠ 0}
  obtain ⟨b,hb⟩ := preconnected_subset_polynomialSignCell p (connectedComponentIn U x)
    isPreconnected_connectedComponentIn ⟨x, mem_connectedComponentIn hx⟩
    (fun y hy => connectedComponentIn_subset U x hy)
  rw [← hmass b]
  exact setIntegral_mono_set hw.integrableOn (Filter.Eventually.of_forall (fun y => hwn y))
    (Filter.Eventually.of_forall hb)

/-- Actual complementary components have the small-mass bound, and the
omitted algebraic set is null. There is no asserted component-count bound. -/
theorem exists_componentwise_polynomial_partition (n s : ℕ) (D : ℕ → ℕ)
    (hzero : ∀ j < s, BoxOddSphereZero n (D j) (2^j))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) (hwn : ∀ x, 0 ≤ w x) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      P.totalDegree ≤ n * ∑ j ∈ Finset.range s, D j ∧
      volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) P = 0} = 0 ∧
      ∀ x, MvPolynomial.eval (fun i => x i) P ≠ 0 →
        (∫ y in connectedComponentIn {y | MvPolynomial.eval (fun i => y i) P ≠ 0} x, w y)
          ≤ (∫ y, w y)/(2:ℝ)^s := by
  classical
  obtain ⟨p,hp,hd,hm⟩ := exists_iterated_polynomial_partition n s D hzero w hw
  have hP : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  refine ⟨∏ i, p i, hP, (MvPolynomial.totalDegree_finsetProd _ _).trans hd,
    polynomial_zero_volume_euclidean _ hP, ?_⟩
  exact fun x hx => polynomial_component_mass_le p w hw hwn hm x hx

/-- The topological premise of this reusable helper is displayed literally:
each continuous odd map from a coefficient sphere to a strictly smaller
Euclidean space has a zero. Under it the dyadic component-mass theorem is
fully constructed, with no additional partition hypothesis. -/
theorem exists_dyadic_component_partition_of_oddSphereZero
    (n : ℕ) (hn : 0 < n) (t : ℕ)
    (hBU : ∀ D M, M < (D+1)^n → BoxOddSphereZero n D M)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) (hwn : ∀ x, 0 ≤ w x) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ 2*n^2*2^t ∧
      volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) P = 0} = 0 ∧
      ∀ x, MvPolynomial.eval (fun i => x i) P ≠ 0 →
        (∫ y in connectedComponentIn {y | MvPolynomial.eval (fun i => y i) P ≠ 0} x, w y)
          ≤ (∫ y, w y)/(2:ℝ)^(n*t) := by
  obtain ⟨P,hP,hd,hnull,hm⟩ := exists_componentwise_polynomial_partition n (n*t)
    (partitionBoxDegree n)
    (fun j _ => hBU _ _ (partitionBoxDegree_dimension n hn j)) w hw hwn
  refine ⟨P,hP,?_,hnull,hm⟩
  have hsum := partitionBoxDegree_sum n hn t
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.preconnected_polynomial_sign_constant
#print axioms KakeyaTwoScale.preconnected_subset_polynomialSignCell
#print axioms KakeyaTwoScale.polynomial_component_mass_le
#print axioms KakeyaTwoScale.exists_componentwise_polynomial_partition
#print axioms KakeyaTwoScale.exists_dyadic_component_partition_of_oddSphereZero
