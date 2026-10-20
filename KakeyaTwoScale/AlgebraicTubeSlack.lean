module
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

open MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def tubeSlackPoint {n : ℕ} (t v : ℝ) (z : EuclideanSpace ℝ (Fin n)) : Fin (n+2) → ℝ :=
  Fin.cons t (Fin.cons v (fun i => z i))

def tubeAxisCoordinate {n : ℕ} (b u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    MvPolynomial (Fin (n+2)) ℝ := C (b i) + C (u i) * X 0 - X i.succ.succ

def tubeSlackResidual {n : ℕ} (b u : EuclideanSpace ℝ (Fin n)) (rho : ℝ) :
    MvPolynomial (Fin (n+2)) ℝ :=
  (∑ i, tubeAxisCoordinate b u i ^ 2) + X (1 : Fin (n+2)) ^ 2 - C (rho^2)

/-- An actual single polynomial encoding the variety and a distance slack. -/
def algebraicTubeSlack {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (rho : ℝ) : MvPolynomial (Fin (n+2)) ℝ :=
  (∑ j, (rename (fun i : Fin n => i.succ.succ) (f j))^2) + tubeSlackResidual b u rho ^ 2

theorem tubeSlackResidual_eval {n : ℕ} (b u z : EuclideanSpace ℝ (Fin n)) (rho t v : ℝ) :
    eval (tubeSlackPoint t v z) (tubeSlackResidual b u rho) =
      dist (b+t•u) z ^ 2 + v^2-rho^2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [tubeSlackResidual, tubeAxisCoordinate, tubeSlackPoint, mul_comm]

theorem algebraicTubeSlack_zero_iff {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) ℝ)
    (b u z : EuclideanSpace ℝ (Fin n)) (rho t v : ℝ) :
    eval (tubeSlackPoint t v z) (algebraicTubeSlack f b u rho) = 0 ↔
      (∀ j, eval (fun i => z i) (f j)=0) ∧ dist (b+t•u) z ^ 2+v^2=rho^2 := by
  have he : eval (tubeSlackPoint t v z) (algebraicTubeSlack f b u rho) =
      (∑ j, (eval (fun i => z i) (f j))^2) + (dist (b+t•u) z ^ 2+v^2-rho^2)^2 := by
    simp only [algebraicTubeSlack, map_add, map_sum, map_pow]
    rw [tubeSlackResidual_eval]
    simp [eval_rename, tubeSlackPoint, Function.comp_def]
  rw [he]
  constructor
  · intro h
    have hs : 0 ≤ ∑ j, (eval (fun i => z i) (f j))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hr : dist (b+t•u) z ^ 2+v^2-rho^2=0 := by nlinarith [sq_nonneg (dist (b+t•u) z ^ 2+v^2-rho^2)]
    refine ⟨fun j => ?_, by linarith⟩
    have hj := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => sq_nonneg (eval (fun i => z i) (f i))) (Finset.mem_univ j)
    nlinarith [sq_nonneg (eval (fun i => z i) (f j))]
  · rintro ⟨hf,hd⟩
    simp [hf,hd]

theorem algebraicTubeSlack_exists_iff {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) ℝ)
    (b u z : EuclideanSpace ℝ (Fin n)) (rho t : ℝ) (hrho : 0 ≤ rho) :
    (∃ v : ℝ, eval (tubeSlackPoint t v z) (algebraicTubeSlack f b u rho)=0) ↔
      (∀ j, eval (fun i => z i) (f j)=0) ∧ dist (b+t•u) z ≤ rho := by
  simp_rw [algebraicTubeSlack_zero_iff]
  constructor
  · rintro ⟨v,hf,hv⟩
    exact ⟨hf, by nlinarith [dist_nonneg (x:=b+t•u) (y:=z),sq_nonneg v]⟩
  · rintro ⟨hf,hd⟩
    have hs : 0 ≤ rho^2-dist (b+t•u) z ^2 := by nlinarith [dist_nonneg (x:=b+t•u) (y:=z)]
    refine ⟨Real.sqrt (rho^2-dist (b+t•u) z ^2),hf,?_⟩
    rw [Real.sq_sqrt hs]
    ring

/-- The exact axis-neighborhood condition is the projection of this zero set.
No elimination, compactness, or nearest-point theorem is assumed. -/
theorem algebraicTubeSlack_projection_iff {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (rho t : ℝ) (hrho : 0 ≤ rho) :
    (∃ z : EuclideanSpace ℝ (Fin n), ∃ v : ℝ,
      eval (tubeSlackPoint t v z) (algebraicTubeSlack f b u rho)=0) ↔
    ∃ z : EuclideanSpace ℝ (Fin n),
      (∀ j, eval (fun i => z i) (f j)=0) ∧ dist (b+t•u) z ≤ rho := by
  exact exists_congr (fun z => algebraicTubeSlack_exists_iff f b u z rho t hrho)

theorem tubeAxisCoordinate_degree {n : ℕ} (b u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (tubeAxisCoordinate b u i).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  · simp

theorem tubeSlackResidual_degree {n : ℕ} (b u : EuclideanSpace ℝ (Fin n)) (rho : ℝ) :
    (tubeSlackResidual b u rho).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (tubeAxisCoordinate_degree b u i))
    · exact (totalDegree_pow _ _).trans (by simp)
  · change (C (rho^2) : MvPolynomial (Fin (n+2)) ℝ).totalDegree ≤ 2
    rw [totalDegree_C]
    omega

theorem algebraicTubeSlack_degree {n m D : ℕ} (f : Fin m → MvPolynomial (Fin n) ℝ)
    (hf : ∀ j, (f j).totalDegree ≤ D) (b u : EuclideanSpace ℝ (Fin n)) (rho : ℝ) :
    (algebraicTubeSlack f b u rho).totalDegree ≤ max (2*D) 4 := by
  apply (totalDegree_add _ _).trans
  apply max_le_max
  · apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 ((totalDegree_rename_le _ _).trans (hf j)))
  · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (tubeSlackResidual_degree b u rho))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.algebraicTubeSlack_zero_iff
#print axioms KakeyaTwoScale.algebraicTubeSlack_exists_iff
#print axioms KakeyaTwoScale.algebraicTubeSlack_degree
#print axioms KakeyaTwoScale.algebraicTubeSlack_projection_iff
