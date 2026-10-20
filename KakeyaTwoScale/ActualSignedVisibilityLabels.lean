module
public import KakeyaTwoScale.CoordinateVisibilityLabels
public import KakeyaTwoScale.AntipodalMollifiedVisibility
public import KakeyaTwoScale.SeparatedAntipodalCover

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
section Labels
variable {d n D : ℕ} {ι : Type*}
variable (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
variable (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
variable (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
variable (r : ℝ) (hr : 0≤r)
variable (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
variable (ε : ℝ)
variable (F : Finset ((Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)))
variable (color : ((Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) → ℕ)
variable (E : ((Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) → ι → Set (Fin (n+1) → ℝ))
variable (valid : ((Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) → ι → Prop)
variable (bad : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → Prop)

/-- An actual signed label: the witness bank shape and physical test are fixed
before the coefficient center. Missing test slots are excluded by `valid`. -/
def actualPositiveVisibilityLabel (a : ℕ) (k : ι) :
    Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  {p | bad p ∧ ∃ B ∈ F, color B=a ∧ valid B k ∧
    visibilityShapeLabel (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p) B ∧
    0 < polynomialRegionSignMass (coefficientPolynomial m p.val) (E B k)}

/-- The required cross-closure separation for actual polynomial sign labels.
The only coloring input is the already proved geometric conflict rule; no
continuity or stability of a chosen label function is assumed. -/
theorem actualPositiveVisibilityLabel_cross_closure (hε : 0<ε) (hε2 : ε<2)
    (hEf : ∀ B ∈ F, ∀ k, volume (E B k) < ∞)
    (hcolor : ∀ B ∈ F, ∀ C ∈ F, B ≠ C →
      ellipsoidFormComparable (1024*((n+1:ℕ):ℝ)^4) B C → color B ≠ color C)
    (a : ℕ) (k : ι) :
    Disjoint (actualPositiveVisibilityLabel m hm hdegree U hU hreg r hr hbound ε F color E valid bad a k)
      (closure (metricSphereAntipode d ⁻¹'
        actualPositiveVisibilityLabel m hm hdegree U hU hreg r hr hbound ε F color E valid bad a k)) := by
  let s := mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε
  have hc : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
      EuclideanSpace ℝ (Fin (n+1)) => s z.1 z.2) :=
    continuous_mollifiedArea_joint m hm hdegree U hU hreg r hr hbound ε hε hε2
  obtain ⟨τ,hτ,hτall⟩ := uniform_seminorm_family_error s hc 1 zero_lt_one
  apply Set.disjoint_left.mpr
  intro p hp hpclosure
  obtain ⟨_,B,hBF,hBa,_,hBp,hpos⟩ := hp
  have hscont := continuous_metric_polynomialRegionSignMass m hm (E B k) (hEf B hBF k)
  obtain ⟨δ,hδ,hδall⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hscont) p hpos
  obtain ⟨q,hq,hpq⟩ := Metric.mem_closure_iff.mp hpclosure (min τ δ) (lt_min hτ hδ)
  obtain ⟨_,C,hCF,hCa,_,hCq,hneg⟩ := hq
  have heven : s (metricSphereAntipode d q)=s q :=
    mollifiedAreaSeminorm_antipodal m hm hdegree U hU hreg r hr hbound ε q
  change visibilityShapeLabel (s (metricSphereAntipode d q)) C at hCq
  rw [heven] at hCq
  have hpqτ : dist p q < τ := by
    exact hpq.trans_le (min_le_left _ _)
  have herr : ∀ v, |s p v-s q v| ≤ ‖v‖ := by simpa only [one_mul] using hτall p q hpqτ
  have hcomp := visibilityShapeLabel_conflict (s p) (s q) B C hBp hCq herr
  have hBC : B=C := by
    by_contra hne
    apply hcolor B hBF C hCF hne
      (ellipsoidFormComparable_mono (by nlinarith [pow_nonneg (Nat.cast_nonneg (n+1) : (0:ℝ)≤(n+1:ℕ)) 4]) hcomp)
    exact hBa.trans hCa.symm
  subst C
  have hqpos := hδall (show q ∈ ball p δ from by
    simpa only [mem_ball,dist_comm] using hpq.trans_le (min_le_right τ δ))
  change 0 < polynomialRegionSignMass (coefficientPolynomial m q.val) (E B k) at hqpos
  rw [polynomialRegionSignMass_antipodal] at hneg
  linarith

end Labels
end KakeyaTwoScale
#print axioms KakeyaTwoScale.actualPositiveVisibilityLabel_cross_closure
