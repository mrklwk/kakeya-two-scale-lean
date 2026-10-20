module
public import KakeyaTwoScale.PolynomialCoordinateRename

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- The wall is one new equation; the original c equations follow it. -/
def polynomialSuccessorSystem {σ : Type*} {c : ℕ}
    (P : Fin c → MvPolynomial σ ℝ) (B : MvPolynomial σ ℝ) :
    Fin (c+1) → MvPolynomial σ ℝ := Fin.cons B P

/-- Actual output-coordinate equivalence, with product order (parents, wall). -/
def successorOutputEquiv (c : ℕ) :
    (EuclideanSpace ℝ (Fin c) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (c+1)) :=
  (show (EuclideanSpace ℝ (Fin c) × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (c+1)) from
    { toFun := fun x => WithLp.toLp 2 (Fin.cons x.2 x.1)
      invFun := fun y => (WithLp.toLp 2 (fun i => y i.succ),y 0)
      left_inv := by intro x; apply Prod.ext <;> rfl
      right_inv := by
        intro y
        apply PiLp.ext
        intro i
        cases i using Fin.cases <;> rfl
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        cases i using Fin.cases <;> rfl
      map_smul' := by
        intro r x
        apply PiLp.ext
        intro i
        cases i using Fin.cases <;> rfl }).toContinuousLinearEquiv

theorem polynomialSuccessorSystem_map {σ : Type*} [Fintype σ] {c : ℕ}
    (P : Fin c → MvPolynomial σ ℝ) (B : MvPolynomial σ ℝ) :
    rectangularPolynomialMap (polynomialSuccessorSystem P B)=
      successorOutputEquiv c ∘ (fun x => (rectangularPolynomialMap P x,eval x B)) := by
  funext x
  apply PiLp.ext
  intro i
  cases i using Fin.cases <;> rfl

theorem polynomialSuccessorSystem_zero {σ : Type*} [Fintype σ] {c : ℕ}
    (P : Fin c → MvPolynomial σ ℝ) (B : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) :
    rectangularPolynomialMap (polynomialSuccessorSystem P B) x=0 ↔
      rectangularPolynomialMap P x=0 ∧ eval x B=0 := by
  rw [polynomialSuccessorSystem_map]
  change successorOutputEquiv c (rectangularPolynomialMap P x,eval x B)=0 ↔ _
  constructor
  · intro h
    have hh : successorOutputEquiv c (rectangularPolynomialMap P x,eval x B)=successorOutputEquiv c 0 := by simpa using h
    exact Prod.mk_eq_zero.mp ((successorOutputEquiv c).injective hh)
  · rintro ⟨hP,hB⟩
    simp [hP,hB]

theorem polynomialSuccessorSystem_degree {σ : Type*} {c D E : ℕ}
    (P : Fin c → MvPolynomial σ ℝ) (B : MvPolynomial σ ℝ)
    (hP : ∀ i, (P i).totalDegree≤D) (hB : B.totalDegree≤E) :
    ∀ i, (polynomialSuccessorSystem P B i).totalDegree≤max D E := by
  intro i
  cases i using Fin.cases with
  | zero => exact hB.trans (le_max_right _ _)
  | succ i => exact (hP i).trans (le_max_left _ _)

theorem polynomialSuccessorSystem_fderiv {σ : Type*} [Fintype σ] {c : ℕ}
    (P : Fin c → MvPolynomial σ ℝ) (B : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) :
    fderiv ℝ (rectangularPolynomialMap (polynomialSuccessorSystem P B)) x=
      (successorOutputEquiv c).toContinuousLinearMap.comp
        (fderiv ℝ (fun y => (rectangularPolynomialMap P y,eval y B)) x) := by
  rw [polynomialSuccessorSystem_map]
  have hd := ((rectangularPolynomialMap_contDiff P 1).differentiable (by norm_num) x).prodMk
    ((finite_polynomial_eval_contDiff B 1).differentiable (by norm_num) x)
  exact ((successorOutputEquiv c).toContinuousLinearMap.hasFDerivAt.comp x hd.hasFDerivAt).fderiv

theorem polynomialSuccessorSystem_regular {σ : Type*} [Fintype σ] {c : ℕ}
    (P : Fin c → MvPolynomial σ ℝ) (B : MvPolynomial σ ℝ)
    (hjoint : ∀ x : EuclideanSpace ℝ σ, rectangularPolynomialMap P x=0 → eval x B=0 →
      (fderiv ℝ (fun y => (rectangularPolynomialMap P y,eval y B)) x).range=⊤) :
    ∀ x : EuclideanSpace ℝ σ,
      rectangularPolynomialMap (polynomialSuccessorSystem P B) x=0 →
      (fderiv ℝ (rectangularPolynomialMap (polynomialSuccessorSystem P B)) x).range=⊤ := by
  intro x hx
  obtain ⟨hP,hB⟩ := (polynomialSuccessorSystem_zero P B x).mp hx
  rw [polynomialSuccessorSystem_fderiv]
  apply LinearMap.range_eq_top.mpr
  intro y
  obtain ⟨v,hv⟩ := LinearMap.range_eq_top.mp (hjoint x hP hB) ((successorOutputEquiv c).symm y)
  refine ⟨v,?_⟩
  change successorOutputEquiv c ((fderiv ℝ (fun z => (rectangularPolynomialMap P z,eval z B)) x) v)=y
  change (fderiv ℝ (fun z => (rectangularPolynomialMap P z,eval z B)) x) v=(successorOutputEquiv c).symm y at hv
  rw [hv]
  exact (successorOutputEquiv c).apply_symm_apply y

/-- Fin-indexed successor equations ready for the physical seed API. -/
def finitePolynomialSuccessor {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (B : MvPolynomial (Fin b ⊕ Fin c) ℝ) :
    Fin (c+1) → MvPolynomial (Fin (b+c)) ℝ :=
  fun i => rename finSumFinEquiv (polynomialSuccessorSystem P B i)

theorem finitePolynomialSuccessor_degree {b c D E : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (B : MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hP : ∀ i, (P i).totalDegree≤D) (hB : B.totalDegree≤E) :
    ∀ i, (finitePolynomialSuccessor P B i).totalDegree≤max D E := by
  intro i
  exact (polynomialCoordinateRename_degree finSumFinEquiv _).le.trans
    (polynomialSuccessorSystem_degree P B hP hB i)

theorem finitePolynomialSuccessor_regular {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (B : MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hjoint : ∀ x : EuclideanSpace ℝ (Fin b ⊕ Fin c),
      rectangularPolynomialMap P x=0 → eval x B=0 →
      (fderiv ℝ (fun y => (rectangularPolynomialMap P y,eval y B)) x).range=⊤) :
    ∀ x : EuclideanSpace ℝ (Fin (b+c)),
      rectangularPolynomialMap (finitePolynomialSuccessor P B) x=0 →
      (fderiv ℝ (rectangularPolynomialMap (finitePolynomialSuccessor P B)) x).range=⊤ :=
  polynomialCoordinateRename_regular finSumFinEquiv _ (polynomialSuccessorSystem_regular P B hjoint)

theorem finitePolynomialSuccessor_zero {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (B : MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (x : EuclideanSpace ℝ (Fin b ⊕ Fin c)) :
    rectangularPolynomialMap (finitePolynomialSuccessor P B)
      (euclideanCoordinateRename finSumFinEquiv x)=0 ↔
      rectangularPolynomialMap P x=0 ∧ eval x B=0 := by
  rw [show finitePolynomialSuccessor P B=fun i => rename finSumFinEquiv (polynomialSuccessorSystem P B i) from rfl,
    rectangularPolynomialMap_rename,polynomialSuccessorSystem_zero]

/-- Exact radius-preserving successor neighborhood transport for seed inputs. -/
theorem finitePolynomialSuccessor_thickening {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (B : MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (x : EuclideanSpace ℝ (Fin b ⊕ Fin c)) (r : ℝ) :
    euclideanCoordinateRename finSumFinEquiv x ∈ Metric.thickening r
      {y | rectangularPolynomialMap (finitePolynomialSuccessor P B) y=0} ↔
    x ∈ Metric.thickening r
      ({y | rectangularPolynomialMap P y=0} ∩ {y | eval y B=0}) := by
  rw [show finitePolynomialSuccessor P B=fun i => rename finSumFinEquiv (polynomialSuccessorSystem P B i) from rfl,
    polynomialCoordinateRename_zero_thickening]
  have hs : {y : EuclideanSpace ℝ (Fin b ⊕ Fin c) | rectangularPolynomialMap (polynomialSuccessorSystem P B) y=0}=
      {y | rectangularPolynomialMap P y=0} ∩ {y | eval y B=0} := by
    ext y
    exact polynomialSuccessorSystem_zero P B y
  rw [hs]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialSuccessorSystem_zero
#print axioms KakeyaTwoScale.polynomialSuccessorSystem_degree
#print axioms KakeyaTwoScale.polynomialSuccessorSystem_fderiv
#print axioms KakeyaTwoScale.polynomialSuccessorSystem_regular
#print axioms KakeyaTwoScale.finitePolynomialSuccessor_degree
#print axioms KakeyaTwoScale.finitePolynomialSuccessor_regular
#print axioms KakeyaTwoScale.finitePolynomialSuccessor_zero

#print axioms KakeyaTwoScale.finitePolynomialSuccessor_thickening
