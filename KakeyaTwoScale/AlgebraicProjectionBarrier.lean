module
public import KakeyaTwoScale.GeneralComponentCount
public import KakeyaTwoScale.PartitionComponentMass
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

open Set Metric MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def coordinateNormSquare (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ i, X i ^ 2

theorem coordinateNormSquare_eval {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    eval (fun i => x i) (coordinateNormSquare n) = ‖x‖^2 := by
  simp [coordinateNormSquare,EuclideanSpace.real_norm_sq_eq]

theorem coordinateNormSquare_degree (n : ℕ) : (coordinateNormSquare n).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_pow (X i : MvPolynomial (Fin n) ℝ) 2).trans (by simp)

/-- A genuine polynomial separator for finitely many zero-free projection
fibers. Compactness supplies epsilon; no elimination, fiber minimum or
component-count premise is assumed. Its degree is max(D,2), independent of
the number of fibers, the coefficients, radius and epsilon. -/
theorem exists_algebraic_projection_barrier {n D : ℕ}
    (G : MvPolynomial (Fin n) ℝ) (coordinate : Fin n) (cuts : Finset ℝ)
    {R : ℝ} (hR : 0 < R) (hdegree : G.totalDegree ≤ D)
    (hnonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ eval (fun i => x i) G)
    (hcuts : ∀ x : EuclideanSpace ℝ (Fin n), x coordinate ∈ cuts →
      0 < eval (fun i => x i) G) :
    ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ max D 2 ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ < R → eval (fun i => x i) G = 0 →
        0 < eval (fun i => x i) Q) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), x coordinate ∈ cuts →
        eval (fun i => x i) Q < 0) := by
  classical
  let f (x : EuclideanSpace ℝ (Fin n)) := eval (fun i => x i) G
  have hf : Continuous f := G.continuous_eval.comp
    (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
  let T : Set (EuclideanSpace ℝ (Fin n)) := closedBall 0 R ∩ {x | x coordinate ∈ cuts}
  have hT : IsCompact T := by
    apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).inter_right
    exact cuts.finite_toSet.isClosed.preimage (EuclideanSpace.proj coordinate).continuous
  obtain ⟨a,ha,hlower⟩ := hT.exists_forall_le' hf.continuousOn
    (fun x hx => hcuts x hx.2)
  let epsilon := a/(R^2+1)
  have heps : 0 < epsilon := div_pos ha (by positivity)
  have heq : epsilon*(R^2+1)=a := by dsimp [epsilon]; field_simp
  have hsmall : epsilon*R^2 < a := by nlinarith
  let Q := C epsilon * (C (R^2)-coordinateNormSquare n)-G
  have hQeval (x : EuclideanSpace ℝ (Fin n)) :
      eval (fun i => x i) Q = epsilon*(R^2-‖x‖^2)-f x := by
    simp [Q,f,coordinateNormSquare_eval]
  refine ⟨Q,?_,?_,?_⟩
  · have hnorm := coordinateNormSquare_degree n
    have hsub : (C (R^2)-coordinateNormSquare n).totalDegree ≤ 2 :=
      (totalDegree_sub _ _).trans (by simpa only [totalDegree_C, Nat.zero_max] using hnorm)
    have hmul : (C epsilon*(C (R^2)-coordinateNormSquare n)).totalDegree ≤ 2 :=
      (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hsub)
    exact (totalDegree_sub _ _).trans (max_le (hmul.trans (le_max_right _ _))
      (hdegree.trans (le_max_left _ _)))
  · intro x hx hz
    rw [hQeval]
    have hfz : f x=0 := hz
    rw [hfz,sub_zero]
    apply mul_pos heps
    nlinarith [norm_nonneg x]
  · intro x hx
    rw [hQeval]
    by_cases hnorm : ‖x‖ ≤ R
    · have hlow : a ≤ f x := hlower x ⟨by simpa using hnorm,hx⟩
      have hnon : 0 ≤ epsilon*‖x‖^2 := by positivity
      nlinarith
    · have hbig : R < ‖x‖ := lt_of_not_ge hnorm
      have hneg : R^2-‖x‖^2 < 0 := by nlinarith
      have hh := mul_neg_of_pos_of_neg heps hneg
      have hg := hnonneg x
      change 0 ≤ f x at hg
      linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateNormSquare_eval
#print axioms KakeyaTwoScale.coordinateNormSquare_degree
#print axioms KakeyaTwoScale.exists_algebraic_projection_barrier
