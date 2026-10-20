module
public import KakeyaTwoScale.CompactSublevelComponents
public import KakeyaTwoScale.GeneralComponentCount
public import KakeyaTwoScale.PreconnectedPolynomialCells

@[expose] public section

open Set Metric MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- The actual squared Euclidean distance polynomial. -/
def squaredBallPolynomial {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial (Fin n) ℝ := ∑ i, (X i-C (c i))^2

theorem squaredBallPolynomial_eval {n : ℕ} (c x : EuclideanSpace ℝ (Fin n)) :
    eval x.ofLp (squaredBallPolynomial c)=dist x c^2 := by
  simp only [squaredBallPolynomial,eval_sum,eval_pow,eval_sub,eval_X,eval_C]
  rw [dist_eq_norm,EuclideanSpace.real_norm_sq_eq]
  rfl

theorem squaredBallPolynomial_degree {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) :
    (squaredBallPolynomial c).totalDegree≤2 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_pow _ _).trans
  have h : (X i-C (c i)).totalDegree≤1 :=
    (totalDegree_sub _ _).trans (max_le (totalDegree_X i).le (by simp))
  exact (Nat.mul_le_mul_left 2 h)

/-- Uniform finite-family bound for the actual components of a nonnegative
polynomial zero set truncated by a closed Euclidean ball. The perturbation
parameter may depend on the finite family; the degree bound does not. -/
theorem finite_compact_polynomial_components_card_le {n D : ℕ}
    (Q : MvPolynomial (Fin n) ℝ) (hD : Q.totalDegree≤D)
    (hQ0 : ∀ x : EuclideanSpace ℝ (Fin n), 0≤eval x.ofLp Q)
    (center : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0≤R)
    {I : Type*} [Fintype I] (x : I→EuclideanSpace ℝ (Fin n))
    (hx : ∀ j, x j ∈ {z | eval z.ofLp Q=0} ∩ closedBall center R)
    (hd : ∀ j k, j≠k → x k ∉ connectedComponentIn
      ({z | eval z.ofLp Q=0} ∩ closedBall center R) (x j)) :
    Fintype.card I≤(2*D+5)^n := by
  classical
  let q : EuclideanSpace ℝ (Fin n)→ℝ := fun z => eval z.ofLp Q
  have hq : Continuous q := Q.continuous_eval.comp (PiLp.continuous_ofLp 2 _)
  obtain ⟨e,he,hsep⟩ := compact_sublevel_finite_component_separation
    q hq hQ0 center R hR x hx hd
  let B := squaredBallPolynomial center
  let P := (Q-C e)*(B-C (R^2+e))
  have hPdeg : P.totalDegree≤D+2 := by
    apply (totalDegree_mul _ _).trans
    apply Nat.add_le_add
    · exact (totalDegree_sub _ _).trans (max_le hD (by simp))
    · exact (totalDegree_sub _ _).trans (max_le (squaredBallPolynomial_degree _) (by rw [totalDegree_C]; omega))
  have hev (z : EuclideanSpace ℝ (Fin n)) :
      eval z.ofLp P=(q z-e)*(dist z center^2-(R^2+e)) := by
    simp only [P,B,eval_mul,eval_sub,eval_C,squaredBallPolynomial_eval,q]
  have hxq (j) : q (x j)<e := by change eval (x j).ofLp Q<e; rw [(hx j).1]; exact he
  have hxr (j) : dist (x j) center^2<R^2+e := by
    have ha : dist (x j) center≤R := (hx j).2
    have hb := dist_nonneg (x := x j) (y := center)
    nlinarith
  have hxnz (j) : x j ∉ ambientPolynomialZeroSet P := by
    change eval (x j).ofLp P≠0
    rw [hev]
    exact mul_ne_zero (sub_ne_zero.mpr (ne_of_lt (hxq j)))
      (sub_ne_zero.mpr (ne_of_lt (hxr j)))
  let component (j : I) := connectedComponentIn (ambientPolynomialZeroSet P)ᶜ (x j)
  have hxc (j) : x j∈component j := mem_connectedComponentIn (hxnz j)
  have hcp (j) : IsPreconnected (component j) := isPreconnected_connectedComponentIn
  have hsub (j) : component j⊆{z | q z<e ∧ dist z center^2<R^2+e} := by
    have hnz (z) (hz : z∈component j) :
        (q z-e)*(dist z center^2-(R^2+e))≠0 := by
      rw [← hev]
      exact connectedComponentIn_subset _ _ hz
    have ha := preconnected_strict_sign (component j) (hcp j)
      (fun z => q z-e) (hq.sub continuous_const).continuousOn
      (fun z hz => (mul_ne_zero_iff.mp (hnz z hz)).1)
    have hb := preconnected_strict_sign (component j) (hcp j)
      (fun z => dist z center^2-(R^2+e))
      (((continuous_id.dist continuous_const).pow 2).sub continuous_const).continuousOn
      (fun z hz => (mul_ne_zero_iff.mp (hnz z hz)).2)
    have ha' : ∀ z∈component j, q z-e<0 := ha.resolve_left (by
      intro hh; have := hh (x j) (hxc j); linarith [hxq j])
    have hb' : ∀ z∈component j, dist z center^2-(R^2+e)<0 := hb.resolve_left (by
      intro hh; have := hh (x j) (hxc j); linarith [hxr j])
    intro z hz
    exact ⟨sub_neg.mp (ha' z hz),sub_neg.mp (hb' z hz)⟩
  have hinj : Function.Injective component := by
    intro j k hjk
    exact hsep (component j) (hcp j) (hsub j) j k (hxc j) (hjk ▸ hxc k)
  let A := Finset.univ.image component
  have hA : (A : Set (Set (EuclideanSpace ℝ (Fin n)))) ⊆ polynomialComplementComponents P := by
    intro S hS
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hS
    exact ⟨x j,hxnz j,rfl⟩
  have hcard := finite_polynomial_complement_components_card_le P hPdeg A hA
  have hAc : A.card=Fintype.card I := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
  rw [hAc] at hcard
  convert hcard using 1

end KakeyaTwoScale
#print axioms KakeyaTwoScale.squaredBallPolynomial_eval
#print axioms KakeyaTwoScale.squaredBallPolynomial_degree
#print axioms KakeyaTwoScale.finite_compact_polynomial_components_card_le
