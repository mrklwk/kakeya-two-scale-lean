module
public import KakeyaTwoScale.CompactPolynomialComponents

@[expose] public section

open Set Metric MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- Nonempty actual connected components of a specified set. -/
def actualSetComponents {X : Type*} [TopologicalSpace X] (K : Set X) : Set (Set X) :=
  {S | ∃ x∈K, connectedComponentIn K x=S}

theorem compact_nonnegative_polynomial_components_bound {n D : ℕ}
    (Q : MvPolynomial (Fin n) ℝ) (hD : Q.totalDegree≤D)
    (hQ0 : ∀ x : EuclideanSpace ℝ (Fin n), 0≤eval x.ofLp Q)
    (center : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0≤R) :
    let K := {z : EuclideanSpace ℝ (Fin n) | eval z.ofLp Q=0} ∩ closedBall center R
    (actualSetComponents K).Finite ∧ (actualSetComponents K).ncard≤(2*D+5)^n := by
  classical
  dsimp only
  let K := {z : EuclideanSpace ℝ (Fin n) | eval z.ofLp Q=0} ∩ closedBall center R
  apply finite_ncard_le_of_finset_bound
  intro A hA
  have hr (S : A) : ∃ x∈K, connectedComponentIn K x=S.val := hA S.property
  choose x hx hc using hr
  have hd (j k : A) (hjk : j≠k) : x k∉connectedComponentIn K (x j) := by
    intro hh
    apply hjk
    apply Subtype.ext
    rw [←hc j,connectedComponentIn_eq hh,hc k]
  have hb := finite_compact_polynomial_components_card_le Q hD hQ0 center R hR x hx hd
  simpa using hb

/-- Uniform bound for actual components of any common real polynomial zero
set in a closed ball. It derives finiteness; there is no smoothness, coefficient,
component-finiteness, rank or nondegeneracy hypothesis. -/
theorem compact_algebraic_components_bound {n e D : ℕ}
    (P : Fin e→MvPolynomial (Fin n) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (center : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0≤R) :
    let K := {z : EuclideanSpace ℝ (Fin n) | ∀ j, eval z.ofLp (P j)=0} ∩ closedBall center R
    (actualSetComponents K).Finite ∧ (actualSetComponents K).ncard≤(4*D+5)^n := by
  classical
  let Q : MvPolynomial (Fin n) ℝ := ∑ j, (P j)^2
  have hev (x : EuclideanSpace ℝ (Fin n)) : eval x.ofLp Q=∑ j, (eval x.ofLp (P j))^2 := by
    simp [Q]
  have hQ0 (x : EuclideanSpace ℝ (Fin n)) : 0≤eval x.ofLp Q := by
    rw [hev]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQdeg : Q.totalDegree≤2*D := by
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hP j))
  have heq : {z : EuclideanSpace ℝ (Fin n) | eval z.ofLp Q=0}=
      {z | ∀ j, eval z.ofLp (P j)=0} := by
    ext z
    simp only [mem_ofPred_eq,hev]
    constructor
    · intro hz j
      have hj := Finset.single_le_sum
        (fun i (_ : i∈Finset.univ) => sq_nonneg (eval z.ofLp (P i))) (Finset.mem_univ j)
      rw [hz] at hj
      nlinarith [sq_nonneg (eval z.ofLp (P j))]
    · intro hz
      simp [hz]
  have hb := compact_nonnegative_polynomial_components_bound Q hQdeg hQ0 center R hR
  dsimp only at hb ⊢
  rw [heq] at hb
  simpa only [show 2*(2*D)+5=4*D+5 by omega] using hb

end KakeyaTwoScale
#print axioms KakeyaTwoScale.compact_nonnegative_polynomial_components_bound
#print axioms KakeyaTwoScale.compact_algebraic_components_bound
