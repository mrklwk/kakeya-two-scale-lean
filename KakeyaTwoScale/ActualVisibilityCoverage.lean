module
public import KakeyaTwoScale.VisibilityFiniteBookkeeping
public import KakeyaTwoScale.VisibilityCubeGeometry

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Assembly of actual coverage and cross-closure separation. All bank, test
and count premises here are discharged by the quantitative cube constructor. -/
theorem actual_visibility_coverage {d n D J P : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e)≤D)
    (z : Fin J → Fin (n+1) → ℝ) (r : ℝ) (hr : 0≤r)
    (hb : ∀ j x, x∈visibilityCube (z j) → ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (M : Fin J → ℝ) (hM : ∀ j, 0≤M j) (L : Fin J → ℕ)
    (hd : P*(∑ j, L j)<d)
    (F : Finset ((Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)))
    (color : ((Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) → ℕ)
    (hcolorBound : ∀ B∈F, color B<P)
    (hcolor : ∀ B∈F, ∀ C∈F, B≠C →
      ellipsoidFormComparable (1024*((n+1:ℕ):ℝ)^4) B C → color B≠color C)
    (η : ℝ) (hη : 0<η)
    (T : Fin J → ((Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) → Finset (Fin (n+1) → ℝ))
    (hcount : ∀ j B, B∈F → 1<M j*visibilityBaseline (n+1) →
      1≤M j*((4*((n+1:ℕ):ℝ)^2)^(n+1))*volume.real (affineEllipsoid B 0) →
      (T j B).card≤L j)
    (ε : ℝ) (hε : 0<ε) (hε2 : ε<2)
    (hbank : ∀ j p, ∃ B∈F, visibilityShapeLabel
      (mollifiedAreaSeminorm m hm hdegree (visibilityCube (z j))
        isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr (hb j) ε p) B)
    (htest : ∀ j B, B∈F → ∀ p,
      visibilityShapeLabel (mollifiedAreaSeminorm m hm hdegree (visibilityCube (z j))
        isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr (hb j) ε p) B →
      ∃ b∈T j B, polynomialRegionSignMass (coefficientPolynomial m p.val)
        (affineEllipsoid (scaledEllipsoidMap B η hη) b)≠0) :
    ∃ p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, ∀ j,
      M j*volume.real (coordinateVisibilityBody
        (mollifiedAreaSeminorm m hm hdegree (visibilityCube (z j))
          isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr (hb j) ε p))≤1 := by
  classical
  let s j := mollifiedAreaSeminorm m hm hdegree (visibilityCube (z j))
    isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr (hb j) ε
  let bad j p := 1<M j*volume.real (coordinateVisibilityBody (s j p))
  let E j B (k : Fin (L j)) := affineEllipsoid (scaledEllipsoidMap B η hη)
    (finsetVisibilitySlot (T j B) k)
  let valid j B (k : Fin (L j)) :=
    1≤M j*((4*((n+1:ℕ):ℝ)^2)^(n+1))*volume.real (affineEllipsoid B 0) ∧ k.val<(T j B).card
  let A (j : Fin J) (a : Fin P) (k : Fin (L j)) :=
    actualPositiveVisibilityLabel m hm hdegree (visibilityCube (z j))
      isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr (hb j) ε
      F color (E j) (valid j) (bad j) a.val k
  let I := (j : Fin J) × (Fin P × Fin (L j))
  have hI : Fintype.card I=P*(∑ j,L j) := by simp [I,Finset.mul_sum]
  have hsep : ∀ i : I, Disjoint (A i.1 i.2.1 i.2.2)
      (closure (metricSphereAntipode d ⁻¹' A i.1 i.2.1 i.2.2)) := by
    intro i
    exact actualPositiveVisibilityLabel_cross_closure m hm hdegree (visibilityCube (z i.1))
      isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr (hb i.1) ε
      F color (E i.1) (valid i.1) (bad i.1) hε hε2
      (fun B _ k => affineEllipsoid_finite _ _) hcolor i.2.1.val i.2.2
  obtain ⟨p,hp⟩ := finite_cross_closure_not_cover (hI.trans_lt hd)
    (fun i : I => A i.1 i.2.1 i.2.2) hsep
  refine ⟨p,?_⟩
  intro j
  by_contra! hbad
  obtain ⟨B,hBF,hlabel⟩ := hbank j p
  have helig := visibilityShapeLabel_eligible (by omega : 0<n+1) (s j p) B hlabel (M j) (hM j) hbad
  have hactive : 1<M j*visibilityBaseline (n+1) :=
    hbad.trans_le (mul_le_mul_of_nonneg_left (coordinateVisibilityBody_baseline (s j p)) (hM j))
  obtain ⟨b,hbT,hbmass⟩ := htest j B hBF p hlabel
  obtain ⟨k,hk,hkb⟩ := finsetVisibilitySlot_surjective (T j B)
    (hcount j B hBF hactive helig) ⟨b,hbT⟩
  let a : Fin P := ⟨color B,hcolorBound B hBF⟩
  have heven : s j (metricSphereAntipode d p)=s j p :=
    mollifiedAreaSeminorm_antipodal m hm hdegree (visibilityCube (z j))
      isClosed_closedBall.measurableSet (Or.inr isClosed_closedBall) r hr (hb j) ε p
  have hE : E j B k=affineEllipsoid (scaledEllipsoidMap B η hη) b := by
    dsimp [E]; rw [hkb]
  rcases lt_or_gt_of_ne hbmass with hneg|hpos
  · apply (hp ⟨j,a,k⟩).2
    change bad j (metricSphereAntipode d p) ∧ _
    refine ⟨?_,B,hBF,rfl,⟨helig,hk⟩,?_,?_⟩
    · dsimp [bad]; rw [heven]; exact hbad
    · change visibilityShapeLabel (s j (metricSphereAntipode d p)) B
      rw [heven]; exact hlabel
    · rw [polynomialRegionSignMass_antipodal,hE]
      linarith
  · apply (hp ⟨j,a,k⟩).1
    refine ⟨hbad,B,hBF,rfl,⟨helig,hk⟩,hlabel,?_⟩
    rw [hE]
    exact hpos

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_visibility_coverage
