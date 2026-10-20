module
public import KakeyaTwoScale.VisibilityCubeGeometry
public import KakeyaTwoScale.CountedPackedNonbisection

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Dimension fixes the test scale and cardinality coefficient before degree,
shape, spatial cube, target, smoothing radius and polynomial center. The packing
and one smoothing threshold are outputs; the area/sign conclusion is actual. -/
theorem cube_visibility_test_packing (n : ℕ) :
    ∃ η : ℝ, ∃ hη : 0<η, ∃ C : ℝ, 0<C ∧
    ∀ (d D : ℕ) (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
      (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
      (q : ℝ) (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)),
      B ∈ boundedEllipsoidClass (n+1) (1/4) q →
      ∀ (z : Fin (n+1) → ℝ) (r : ℝ) (hr : 0≤r)
      (hbound : ∀ x ∈ visibilityCube z,
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
      (M : ℝ), 0<M →
      1 ≤ M*((4*((n+1:ℕ):ℝ)^2)^(n+1))*volume.real (affineEllipsoid B 0) →
      ∃ F : Finset (Fin (n+1) → ℝ),
        (F.card:ℝ)≤C*M ∧
        (∀ b ∈ F, affineEllipsoid (scaledEllipsoidMap B η hη) b ⊆ visibilityCube z) ∧
        ∃ δ>0, δ<2 ∧ ∀ ε : ℝ, 0<ε → ε≤δ →
          ∀ p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          visibilityShapeLabel (mollifiedAreaSeminorm m hm hdegree (visibilityCube z)
            isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr hbound ε p) B →
          ∃ b ∈ F, polynomialRegionSignMass (coefficientPolynomial m p.val)
            (affineEllipsoid (scaledEllipsoidMap B η hη) b) ≠ 0 := by
  classical
  obtain ⟨c,hc,hpack⟩ := counted_packed_ellipsoid_nonbisection n
  have hN : (0:ℝ)<(n+1:ℕ) := by positivity
  have hden : 0<8*((n+1:ℕ):ℝ)*3^(n+1) := by positivity
  obtain ⟨η,hη,hηtop⟩ := exists_between (show (0 : ℝ) < min (1/16)
    (c*(1/4)^(n+1)/(8*((n+1:ℕ):ℝ)*3^(n+1))) from by positivity)
  have hηsmall : η≤1/16 := (hηtop.trans_le (min_le_left _ _)).le
  have hgap : (3:ℝ)^(n+1)*(4*((n+1:ℕ):ℝ)*η) < c*(1/4)^(n+1) := by
    have hh := (lt_div_iff₀ hden).mp (hηtop.trans_le (min_le_right _ _))
    have hp : 0 < (3:ℝ)^(n+1)*(4*((n+1:ℕ):ℝ)*η) := by positivity
    nlinarith
  let A : ℝ := (4*((n+1:ℕ):ℝ)^2)^(n+1)
  let C := A/η^(n+1)
  have hC : 0<C := by dsimp [C,A]; positivity
  refine ⟨η,hη,C,hC,?_⟩
  intro d D m hm hdegree q B hB z r hr hbound M hM helig
  let S := scaledEllipsoidMap B η hη
  obtain ⟨F,_,_,hi,hu,δ,hδ,hδ2,hδall⟩ := hpack d D m hm hdegree S
    (visibilityCenters z) (visibilityCube z) (isCompact_closedBall _ _)
    isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr hbound
    (fun b hb => scaled_bank_test_in_cube B q hB η hη hηsmall z b hb)
  have hv : 0<volume.real (affineEllipsoid B 0) :=
    ENNReal.toReal_pos (ne_of_gt (affineEllipsoid_positive B 0)) (affineEllipsoid_finite B 0).ne
  have hu' := ENNReal.toReal_mono (show volume (visibilityCube z)≠∞ by rw [visibilityCube_volume]; simp) hu
  rw [visibilityCube_volume,ENNReal.toReal_one] at hu'
  simp only [S,scaledEllipsoidMap_volume,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0≤η^(n+1))] at hu'
  have hcard : (F.card:ℝ)≤C*M := by
    change 1≤M*A*volume.real (affineEllipsoid B 0) at helig
    have hh : (F.card:ℝ)*η^(n+1) ≤ M*A := by
      change (F.card:ℝ)*(η^(n+1)*volume.real (affineEllipsoid B 0))≤1 at hu'
      nlinarith
    have hηpow : 0<η^(n+1) := by positivity
    calc
      (F.card:ℝ) ≤ M*A/η^(n+1) := (le_div_iff₀ hηpow).mpr hh
      _ = C*M := by dsimp [C]; ring
  refine ⟨F,hcard,hi,δ,hδ,hδ2,?_⟩
  intro ε hε hεδ p hp
  apply hδall ε hε hεδ p
  have hbudget := visibilityShapeLabel_scaled_budget
    (mollifiedAreaSeminorm m hm hdegree (visibilityCube z)
      isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr hbound ε p) B hp η hη
  have hmul := mul_le_mul_of_nonneg_left hbudget (by positivity : 0≤(3:ℝ)^(n+1))
  have hvol : volume.real (visibilityCenters z)=(1/4:ℝ)^(n+1) := by
    rw [Measure.real,visibilityCenters_volume,ENNReal.toReal_ofReal (by positivity)]
  rw [hvol]
  simp_rw [mollifiedAreaSeminorm_apply m hm hdegree (visibilityCube z)
    isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr hbound ε p] at hmul
  exact hmul.trans_lt hgap

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cube_visibility_test_packing
