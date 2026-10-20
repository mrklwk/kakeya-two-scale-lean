module
public import KakeyaTwoScale.ProjectedPolynomialPartition
public import KakeyaTwoScale.WholeCubeTupleSelection

@[expose] public section

open MeasureTheory Set
noncomputable section
namespace KakeyaTwoScale

/-- Labelled whole-set density. Overlaps are counted with their multiplicities. -/
def weightedWholeCubeDensity {E C : Type*} [MeasurableSpace E]
    (μ : Measure E) (cubes : Finset C) (Q : C → Set E) (weight : C → ℝ) : E → ℝ :=
  fun x => ∑ q ∈ cubes, (Q q).indicator (fun _ => weight q / μ.real (Q q)) x

theorem integrable_weightedWholeCubeDensity {E C : Type*} [MeasurableSpace E]
    (μ : Measure E) (cubes : Finset C) (Q : C → Set E) (weight : C → ℝ)
    (hQ : ∀ q ∈ cubes, MeasurableSet (Q q))
    (hfinite : ∀ q ∈ cubes, μ (Q q) ≠ ⊤) :
    Integrable (weightedWholeCubeDensity μ cubes Q weight) μ := by
  apply integrable_finsetSum
  intro q hq
  exact (integrableOn_const (hfinite q hq)).integrable_indicator (hQ q hq)

theorem weightedWholeCubeDensity_nonneg {E C : Type*} [MeasurableSpace E]
    (μ : Measure E) (cubes : Finset C) (Q : C → Set E) (weight : C → ℝ)
    (hw : ∀ q ∈ cubes, 0 ≤ weight q) (x : E) :
    0 ≤ weightedWholeCubeDensity μ cubes Q weight x := by
  apply Finset.sum_nonneg
  intro q hq
  exact Set.indicator_nonneg (fun _ _ => div_nonneg (hw q hq) ENNReal.toReal_nonneg) x

theorem integral_weightedWholeCubeDensity {E C : Type*} [MeasurableSpace E]
    (μ : Measure E) (cubes : Finset C) (Q : C → Set E) (weight : C → ℝ)
    (hQ : ∀ q ∈ cubes, MeasurableSet (Q q))
    (hfinite : ∀ q ∈ cubes, μ (Q q) ≠ ⊤)
    (hpositive : ∀ q ∈ cubes, 0 < μ.real (Q q)) :
    (∫ x, weightedWholeCubeDensity μ cubes Q weight x ∂μ) = ∑ q ∈ cubes, weight q := by
  unfold weightedWholeCubeDensity
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [integral_indicator (hQ q hq), setIntegral_const]
    change μ.real (Q q) * (weight q / μ.real (Q q)) = weight q
    exact mul_div_cancel₀ _ (ne_of_gt (hpositive q hq))
  · intro q hq
    exact (integrableOn_const (hfinite q hq)).integrable_indicator (hQ q hq)

/-- Every contained whole cube contributes its full weight to an untrimmed
region. Partial cubes only add nonnegative mass. -/
theorem wholeCubeWeight_le_setIntegral {E C : Type*} [MeasurableSpace E]
    (μ : Measure E) (cubes selected : Finset C) (Q : C → Set E) (weight : C → ℝ)
    (hsel : selected ⊆ cubes)
    (hQ : ∀ q ∈ cubes, MeasurableSet (Q q))
    (hfinite : ∀ q ∈ cubes, μ (Q q) ≠ ⊤)
    (hpositive : ∀ q ∈ cubes, 0 < μ.real (Q q))
    (hw : ∀ q ∈ cubes, 0 ≤ weight q)
    (S : Set E) (hS : MeasurableSet S) (hcontain : ∀ q ∈ selected, Q q ⊆ S) :
    (∑ q ∈ selected, weight q) ≤ ∫ x in S, weightedWholeCubeDensity μ cubes Q weight x ∂μ := by
  classical
  rw [← integral_weightedWholeCubeDensity μ selected Q weight
    (fun q hq => hQ q (hsel hq)) (fun q hq => hfinite q (hsel hq))
    (fun q hq => hpositive q (hsel hq)), ← integral_indicator hS]
  apply integral_mono
    (integrable_weightedWholeCubeDensity μ selected Q weight
      (fun q hq => hQ q (hsel hq)) (fun q hq => hfinite q (hsel hq)))
    ((integrable_weightedWholeCubeDensity μ cubes Q weight hQ hfinite).indicator hS)
  intro x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsel
    intro q hq _
    exact Set.indicator_nonneg (fun _ _ => div_nonneg (hw q hq) ENNReal.toReal_nonneg) x
  · rw [Set.indicator_of_notMem hx]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro q hq
    exact Set.indicator_of_notMem (fun h => hx (hcontain q hq h)) _

/-- A real polynomial partition obtained by projecting the constructed density.
The cell bound controls arbitrary labelled whole cubes contained in that cell,
without a disjointness or pre-assumed density-partition hypothesis. -/
theorem exists_weightedWholeCube_projected_partition {C : Type*}
    (k m D : ℕ) (hk : 0 < k) (hD : 0 < D)
    (cubes : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)))
    (weight : C → ℝ)
    (hQ : ∀ q ∈ cubes, MeasurableSet (Q q))
    (hfinite : ∀ q ∈ cubes, volume (Q q) ≠ ⊤)
    (hpositive : ∀ q ∈ cubes, 0 < volume.real (Q q))
    (hw : ∀ q ∈ cubes, 0 ≤ weight q) :
    ∃ P : MvPolynomial (Fin k) ℝ, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      volume (ambientPolynomialZeroSet P) = 0 ∧
      (polynomialComplementComponents P).Finite ∧
      (polynomialComplementComponents P).ncard ≤ 3^k * D^k ∧
      ∀ S ∈ polynomialComplementComponents P, ∀ selected : Finset C,
        selected ⊆ cubes → (∀ q ∈ selected, Q q ⊆ Prod.fst ⁻¹' S) →
        (∑ q ∈ selected, weight q) ≤ ((4*(k:ℝ)^2)/(D:ℝ))^k * ∑ q ∈ cubes, weight q := by
  let w := weightedWholeCubeDensity volume cubes Q weight
  have hi := integrable_weightedWholeCubeDensity volume cubes Q weight hQ hfinite
  obtain ⟨P,hne,hdeg,hnull,hfin,hcard,hcap⟩ :=
    exists_projected_polynomial_partition k m D hk hD w hi
      (weightedWholeCubeDensity_nonneg volume cubes Q weight hw)
  refine ⟨P,hne,hdeg,hnull,hfin,hcard,?_⟩
  intro S hS selected hsel hcontain
  have hmS : MeasurableSet S := by
    obtain ⟨x,hx,rfl⟩ := hS
    have hc : IsClosed (ambientPolynomialZeroSet P) :=
      isClosed_eq (P.continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin k => ℝ))) continuous_const
    exact hc.isOpen_compl.connectedComponentIn.measurableSet
  have hle := wholeCubeWeight_le_setIntegral volume cubes selected Q weight hsel
    hQ hfinite hpositive hw (Prod.fst ⁻¹' S) (hmS.preimage measurable_fst) hcontain
  exact hle.trans (by simpa [w, integral_weightedWholeCubeDensity volume cubes Q weight hQ hfinite hpositive] using hcap S hS)

/-- The weight transfer applies to the original nonlinear tuple-fiber mass.
Selection is by whole cube, so every retained fiber is literally unchanged. -/
theorem exists_tupleWholeCube_projected_partition {C T : Type*} [DecidableEq C]
    (k m D : ℕ) (hk : 0 < k) (hD : 0 < D)
    (Y : Finset T) (cube : T → C) (cubes : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)))
    (hQ : ∀ q ∈ cubes, MeasurableSet (Q q))
    (hfinite : ∀ q ∈ cubes, volume (Q q) ≠ ⊤)
    (hpositive : ∀ q ∈ cubes, 0 < volume.real (Q q))
    (p : ℝ) (hp : 0 < p) :
    ∃ P : MvPolynomial (Fin k) ℝ, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      volume (ambientPolynomialZeroSet P) = 0 ∧
      (polynomialComplementComponents P).Finite ∧
      (polynomialComplementComponents P).ncard ≤ 3^k * D^k ∧
      ∀ S ∈ polynomialComplementComponents P, ∀ selected : Finset C,
        selected ⊆ cubes → (∀ q ∈ selected, Q q ⊆ Prod.fst ⁻¹' S) →
        (∀ q ∈ selected,
          (Y.filter (fun y => cube y ∈ selected)).filter (fun y => cube y = q) =
            Y.filter (fun y => cube y = q)) ∧
        tupleCubeMass (Y.filter (fun y => cube y ∈ selected)) cube cubes p ≤
          ((4*(k:ℝ)^2)/(D:ℝ))^k * tupleCubeMass Y cube cubes p := by
  obtain ⟨P,hne,hdeg,hnull,hfin,hcard,hcap⟩ :=
    exists_weightedWholeCube_projected_partition k m D hk hD cubes Q
      (fun q => (ParentLevel.capacity Y cube q : ℝ)^p) hQ hfinite hpositive
      (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨P,hne,hdeg,hnull,hfin,hcard,?_⟩
  intro S hS selected hsel hcontain
  refine ⟨fun q hq => cube_selection_full_fiber Y cube selected hq, ?_⟩
  rw [whole_cube_selection_mass Y cube cubes selected hsel hp]
  exact hcap S hS selected hsel hcontain

end KakeyaTwoScale
#print axioms KakeyaTwoScale.integrable_weightedWholeCubeDensity
#print axioms KakeyaTwoScale.integral_weightedWholeCubeDensity
#print axioms KakeyaTwoScale.wholeCubeWeight_le_setIntegral
#print axioms KakeyaTwoScale.exists_weightedWholeCube_projected_partition

#print axioms KakeyaTwoScale.exists_tupleWholeCube_projected_partition
