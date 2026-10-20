module
public import KakeyaTwoScale.EllipsoidTranslatePacking
public import KakeyaTwoScale.MollifiedFiniteEllipsoidBisection

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal Function
noncomputable section
namespace KakeyaTwoScale

/-- Retain the upper count-volume bound for exactly the same packing used
in the uniform smoothing argument. Construct the test packing and a uniform smoothing radius, then obtain an
actual nonzero sign mass whenever the common-direction mollified area budget
is too small to bisect all tests. Dimension chooses c before all other data. -/
theorem counted_packed_ellipsoid_nonbisection (n : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ (d D : ℕ)
      (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
      (_hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
      (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ))
      (C U : Set (Fin (n+1) → ℝ)) (_hC : IsCompact C)
      (hU : MeasurableSet U) (_hreg : IsOpen U ∨ IsClosed U)
      (r : ℝ) (hr : 0≤r)
      (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r),
      (∀ b ∈ C, affineEllipsoid B b ⊆ U) →
      ∃ F : Finset (Fin (n+1) → ℝ), (↑F : Set _) ⊆ C ∧
        (↑F : Set _).PairwiseDisjoint (affineEllipsoid B) ∧
        (∀ b ∈ F, affineEllipsoid B b ⊆ U) ∧
        (F.card : ℝ≥0∞)*volume (affineEllipsoid B 0) ≤ volume U ∧
        ∃ δ > 0, δ < 2 ∧ ∀ ε : ℝ, 0<ε → ε≤δ →
          ∀ p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          (3:ℝ)^(n+1) * (∑ j : Fin (n+1),
            mollifiedCoefficientArea m hm U hU r hr hbound ε p
              (WithLp.toLp 2 (B (Pi.single j 1)))) < c*volume.real C →
          ∃ b ∈ F, polynomialRegionSignMass (coefficientPolynomial m p.val)
            (affineEllipsoid B b) ≠ 0 := by
  classical
  obtain ⟨c,hc,hbis⟩ := mollified_finite_ellipsoid_bisection n
  refine ⟨c,hc,?_⟩
  intro d D m hm hdegree B C U hC hU hreg r hr hbound hCU
  obtain ⟨F,hF,hd,hi,hu,hl⟩ := exists_ellipsoid_translate_packing B C U hC hCU
  have hE : volume (affineEllipsoid B 0) ≠ ∞ := (affineEllipsoid_finite B 0).ne
  have hlreal := ENNReal.toReal_mono (show
      (F.card : ℝ≥0∞)*ENNReal.ofReal ((3:ℝ)^(n+1))*volume (affineEllipsoid B 0) ≠ ∞ by finiteness) hl
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0≤(3:ℝ)^(n+1))] at hlreal
  have hsum : (∑ i : F, volume.real (affineEllipsoid B (i : Fin (n+1) → ℝ))) =
      (F.card:ℝ)*volume.real (affineEllipsoid B 0) := by
    simp [Measure.real,affineEllipsoid_volume]
  obtain ⟨δ,hδ,hδ2,hδbis⟩ := hbis F d D m hm hdegree B
    (fun i : F => (i : Fin (n+1) → ℝ)) U hU hreg r hr hbound
    (fun i j hij => hd i.property j.property (fun h => hij (Subtype.ext h)))
    (fun i => hi i i.property)
  refine ⟨F,hF,hd,hi,hu,δ,hδ,hδ2,?_⟩
  intro ε hε hεδ p hsmall
  by_contra! hzero
  have hb := hδbis ε hε hεδ p Finset.univ
    (fun i _ => hzero i i.property)
  rw [hsum] at hb
  have h1 := mul_le_mul_of_nonneg_left hlreal hc.le
  have h2 := mul_le_mul_of_nonneg_left hb (by positivity : 0≤(3:ℝ)^(n+1))
  change c*(volume C).toReal ≤ _ at h1
  change (3:ℝ)^(n+1)*_ < c*(volume C).toReal at hsmall
  change c*((F.card:ℝ)*(volume (affineEllipsoid B 0)).toReal) ≤ _ at hb
  simp only [Measure.real] at h2
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.counted_packed_ellipsoid_nonbisection
