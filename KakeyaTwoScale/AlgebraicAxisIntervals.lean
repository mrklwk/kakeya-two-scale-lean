module
public import KakeyaTwoScale.ClosedProjectionIntervals
public import KakeyaTwoScale.AlgebraicTubeSlack

@[expose] public section

open Set Metric MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Proper-space nearest-point attainment proves closedness of the ACTUAL
existential distance condition, including the empty-set case. -/
theorem isClosed_axis_neighborhood {n : ℕ} (W : Set (EuclideanSpace ℝ (Fin n)))
    (hW : IsClosed W) (b u : EuclideanSpace ℝ (Fin n)) (rho : ℝ) :
    IsClosed {t : ℝ | ∃ z ∈ W, dist (b+t•u) z ≤ rho} := by
  by_cases hne : W.Nonempty
  · have he : {t : ℝ | ∃ z ∈ W, dist (b+t•u) z ≤ rho} =
        {t : ℝ | infDist (b+t•u) W ≤ rho} := by
      ext t
      constructor
      · rintro ⟨z,hz,hd⟩
        exact (infDist_le_dist_of_mem hz).trans hd
      · intro ht
        obtain ⟨z,hz,he⟩ := hW.exists_infDist_eq_dist hne (b+t•u)
        exact ⟨z,hz,he ▸ ht⟩
    rw [he]
    exact isClosed_le ((continuous_infDist_pt W).comp
      (continuous_const.add (continuous_id.smul continuous_const))) continuous_const
  · have he : {t : ℝ | ∃ z ∈ W, dist (b+t•u) z ≤ rho} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨z,hz,_⟩
      exact hne ⟨z,hz⟩
    rw [he]
    exact isClosed_empty

/-- Application-specific quantitative elimination, fully constructed without
RCF QE: exact closed axis-neighborhood intervals for an arbitrary algebraic
variety. Degree and dimension alone bound their number. -/
theorem exists_algebraic_axis_intervals {n m D : ℕ}
    (f : Fin m → MvPolynomial (Fin n) ℝ) (hf : ∀ j, (f j).totalDegree ≤ D)
    (b u : EuclideanSpace ℝ (Fin n)) {rho L : ℝ} (hrho : 0 ≤ rho) (hL : 0 < L) :
    ∃ C : Finset (ℝ × ℝ), C.card ≤ (2*(max (2*D) 4)+1)^(n+2) ∧
      (∀ a ∈ C, 0 ≤ a.1 ∧ a.1 ≤ a.2 ∧ a.2 ≤ L) ∧
      ∀ t : ℝ, (t ∈ Icc (0:ℝ) L ∧
        ∃ z : EuclideanSpace ℝ (Fin n), (∀ j, eval (fun i => z i) (f j)=0) ∧
          dist (b+t•u) z ≤ rho) ↔ ∃ a ∈ C, t ∈ Icc a.1 a.2 := by
  classical
  let W : Set (EuclideanSpace ℝ (Fin n)) := {z | ∀ j, eval (fun i => z i) (f j)=0}
  have hW : IsClosed W := by
    have he : W = ⋂ j, {z : EuclideanSpace ℝ (Fin n) | eval (fun i => z i) (f j)=0} := by
      ext z
      simp [W]
    rw [he]
    apply isClosed_iInter
    intro j
    exact isClosed_eq ((f j).continuous_eval.comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))) continuous_const
  let S : Set ℝ := {t | ∃ z ∈ W, dist (b+t•u) z ≤ rho}
  let G := algebraicTubeSlack f b u rho
  have hprojection : ∀ t, t ∈ S ↔ ∃ x : EuclideanSpace ℝ (Fin (n+2)),
      x 0=t ∧ eval (fun i => x i) G=0 := by
    intro t
    have hslack := algebraicTubeSlack_projection_iff f b u rho t hrho
    constructor
    · intro ht
      obtain ⟨z,v,hzero⟩ := hslack.mpr ht
      exact ⟨WithLp.toLp 2 (tubeSlackPoint t v z),rfl,hzero⟩
    · rintro ⟨x,hxt,hzero⟩
      apply hslack.mp
      let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x i.succ.succ)
      have he : tubeSlackPoint (x 0) (x 1) z = fun i => x i := by
        funext i
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
      refine ⟨z,x 1,?_⟩
      rw [← hxt,he]
      exact hzero
  have hnonneg : ∀ x : EuclideanSpace ℝ (Fin (n+2)), 0 ≤ eval (fun i => x i) G := by
    intro x
    dsimp [G,algebraicTubeSlack]
    simp only [map_add,map_sum,map_pow]
    positivity
  obtain ⟨C,hC,hb,he⟩ := exists_closed_algebraic_projection_intervals G 0 S
    (isClosed_axis_neighborhood W hW b u rho) hprojection
    (algebraicTubeSlack_degree f hf b u rho) hnonneg hL
  refine ⟨C,?_,hb,he⟩
  have hh : max (max (2*D) 4) 2=max (2*D) 4 := max_eq_left (by omega)
  simpa only [hh] using hC

end KakeyaTwoScale
#print axioms KakeyaTwoScale.isClosed_axis_neighborhood
#print axioms KakeyaTwoScale.exists_algebraic_axis_intervals
