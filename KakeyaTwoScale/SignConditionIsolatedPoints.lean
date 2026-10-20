module
public import KakeyaTwoScale.IsolatedPolynomialZeros
public import Mathlib.Topology.Instances.Sign

@[expose] public section

open Set Metric MvPolynomial Filter
open scoped BigOperators Topology
noncomputable section
namespace KakeyaTwoScale

/-- Arbitrary Boolean acceptance of the signs of a fixed polynomial family. -/
def polynomialSignSet {n s : ℕ} (P : Fin s → MvPolynomial (Fin n) ℝ)
    (accept : (Fin s → SignType) → Prop) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | accept (fun j => SignType.sign (eval (fun a => x a) (P j)))}

def zeroPatternSquares {n s : ℕ} (P : Fin s → MvPolynomial (Fin n) ℝ)
    (Z : Finset (Fin s)) : MvPolynomial (Fin n) ℝ := ∑ j ∈ Z, (P j)^2

theorem zeroPatternSquares_degree {n s D : ℕ}
    (P : Fin s → MvPolynomial (Fin n) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (Z : Finset (Fin s)) : (zeroPatternSquares P Z).totalDegree≤2*D := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_pow _ _).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 (hP j))

theorem zeroPatternSquares_nonneg {n s : ℕ}
    (P : Fin s → MvPolynomial (Fin n) ℝ) (Z : Finset (Fin s))
    (x : Fin n → ℝ) : 0≤eval x (zeroPatternSquares P Z) := by
  simp only [zeroPatternSquares,map_sum,map_pow]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem zeroPatternSquares_eq_zero {n s : ℕ}
    (P : Fin s → MvPolynomial (Fin n) ℝ) (Z : Finset (Fin s)) (x : Fin n → ℝ) :
    eval x (zeroPatternSquares P Z)=0 ↔ ∀ j∈Z, eval x (P j)=0 := by
  simp only [zeroPatternSquares,map_sum,map_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp

/-- An isolated accepted point is isolated in the zero locus of exactly the
atoms vanishing there. Nonzero signs persist locally, independently of coefficients. -/
theorem sign_condition_isolates_zero_pattern {n s : ℕ}
    (P : Fin s → MvPolynomial (Fin n) ℝ) (accept : (Fin s → SignType) → Prop)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x∈polynomialSignSet P accept)
    (hiso : ∃ r : ℝ, 0<r ∧ ∀ z, dist z x≤r → z∈polynomialSignSet P accept → z=x) :
    ∃ r : ℝ, 0<r ∧ ∀ z : EuclideanSpace ℝ (Fin n), dist z x≤r →
      eval (fun a => z a) (zeroPatternSquares P (Finset.univ.filter
        (fun j => eval (fun a => x a) (P j)=0)))=0 → z=x := by
  classical
  have hevent : ∀ j, ∀ᶠ z : EuclideanSpace ℝ (Fin n) in 𝓝 x,
      eval (fun a => x a) (P j)≠0 →
      SignType.sign (eval (fun a => z a) (P j))=SignType.sign (eval (fun a => x a) (P j)) := by
    intro j
    by_cases hj : eval (fun a => x a) (P j)=0
    · exact Eventually.of_forall fun _ h => (h hj).elim
    · have hc : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) =>
          SignType.sign (eval (fun a => z a) (P j))) x :=
        ContinuousAt.comp (f := fun z : EuclideanSpace ℝ (Fin n) => eval (fun a => z a) (P j))
          (continuousAt_sign_of_ne_zero hj)
          ((P j).continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))).continuousAt
      have hh := hc.eventually ((isOpen_discrete _).mem_nhds (show
        SignType.sign (eval (fun a => x a) (P j))∈
          {SignType.sign (eval (fun a => x a) (P j))} from rfl))
      filter_upwards [hh] with z hz
      exact fun _ => hz
  have hall := Filter.eventually_all.mpr hevent
  obtain ⟨e,he,hball⟩ := Metric.eventually_nhds_iff.mp hall
  obtain ⟨r,hr,hiso⟩ := hiso
  refine ⟨min r (e/2),lt_min hr (by positivity),?_⟩
  intro z hz hz0
  apply hiso z (hz.trans (min_le_left _ _))
  have hnear : dist z x<e := (hz.trans (min_le_right _ _)).trans_lt (by linarith)
  have heq : (fun j => SignType.sign (eval (fun a => z a) (P j)))=
      (fun j => SignType.sign (eval (fun a => x a) (P j))) := by
    funext j
    by_cases hj : eval (fun a => x a) (P j)=0
    · have hzj := (zeroPatternSquares_eq_zero P _ _).mp hz0 j (by simp [hj])
      simp [hzj,hj]
    · exact hball hnear j hj
  change accept _
  rw [heq]
  exact hx

/-- Uniform isolated-point count for every Boolean polynomial sign condition.
No connected-component count or semialgebraic decomposition is assumed. -/
theorem sign_condition_isolated_points_card_le {n s D : ℕ} {I : Type*} [Fintype I]
    (P : Fin s → MvPolynomial (Fin n) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (accept : (Fin s → SignType) → Prop)
    (x : I → EuclideanSpace ℝ (Fin n)) (hinj : Function.Injective x)
    (hx : ∀ i, x i∈polynomialSignSet P accept)
    (hiso : ∀ i, ∃ r : ℝ, 0<r ∧ ∀ z, dist z (x i)≤r →
      z∈polynomialSignSet P accept → z=x i) :
    Fintype.card I≤2^s*(4*D+1)^n := by
  classical
  let pat (i : I) : Finset (Fin s) := Finset.univ.filter
    (fun j => eval (fun a => x i a) (P j)=0)
  have hbound (Z : Finset (Fin s)) :
      (Finset.univ.filter (fun i => pat i=Z)).card≤(4*D+1)^n := by
    let F := Finset.univ.filter (fun i => pat i=Z)
    have he (i : F) : pat i.val=Z := (Finset.mem_filter.mp i.property).2
    have hz (i : F) : eval (fun a => x i.val a) (zeroPatternSquares P Z)=0 := by
      rw [zeroPatternSquares_eq_zero]
      intro j hj
      rw [← he i] at hj
      exact (Finset.mem_filter.mp hj).2
    have hi (i : F) := sign_condition_isolates_zero_pattern P accept (x i.val) (hx i.val) (hiso i.val)
    have hi' (i : F) : ∃ r : ℝ, 0<r ∧ ∀ z : EuclideanSpace ℝ (Fin n),
        dist z (x i.val)≤r → eval (fun a => z a) (zeroPatternSquares P Z)=0 → z=x i.val := by
      have hh := hi i
      change ∃ r : ℝ, 0<r ∧ ∀ z : EuclideanSpace ℝ (Fin n),
        dist z (x i.val)≤r → eval (fun a => z a) (zeroPatternSquares P (pat i.val))=0 → z=x i.val at hh
      rwa [he i] at hh
    have hh := isolated_nonnegative_polynomial_zeros_card_le (zeroPatternSquares P Z)
      (zeroPatternSquares_degree P hP Z) (fun z => zeroPatternSquares_nonneg P Z (fun a => z a))
      (fun i : F => x i.val) (hinj.comp Subtype.val_injective) hz hi'
    simpa only [Fintype.card_coe,show 2*(2*D)+1=4*D+1 by omega] using hh
  have he : Fintype.card I=∑ Z : Finset (Fin s), (Finset.univ.filter (fun i => pat i=Z)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise (f := pat) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _))
  rw [he]
  calc
    _ ≤ ∑ _Z : Finset (Fin s), (4*D+1)^n := Finset.sum_le_sum (fun Z _ => hbound Z)
    _ = _ := by simp

/-- Actual finiteness is established before using ncard. -/
theorem sign_condition_isolated_points_finite_ncard_le {n s D : ℕ}
    (P : Fin s → MvPolynomial (Fin n) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (accept : (Fin s → SignType) → Prop) :
    let A := {x : EuclideanSpace ℝ (Fin n) | x∈polynomialSignSet P accept ∧
      ∃ r : ℝ, 0<r ∧ ∀ z, dist z x≤r → z∈polynomialSignSet P accept → z=x}
    A.Finite ∧ A.ncard≤2^s*(4*D+1)^n := by
  dsimp only
  apply finite_ncard_le_of_finset_bound
  intro F hF
  have hh := sign_condition_isolated_points_card_le P hP accept (fun x : F => x.val)
    Subtype.val_injective (fun x => (hF x.property).1) (fun x => (hF x.property).2)
  simpa using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sign_condition_isolates_zero_pattern

#print axioms KakeyaTwoScale.sign_condition_isolated_points_card_le
#print axioms KakeyaTwoScale.sign_condition_isolated_points_finite_ncard_le
