module
public import KakeyaTwoScale.CoordinateGridFaces
public import KakeyaTwoScale.PolynomialTransverseGrid

@[expose] public section

open Set Metric MvPolynomial
noncomputable section
namespace KakeyaTwoScale

theorem compact_algebraic_components_bound_fintype {d D : ℕ} {ι : Type*} [Fintype ι]
    (P : ι→MvPolynomial (Fin d) ℝ) (hP : ∀ i, (P i).totalDegree≤D)
    (a : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR : 0≤R) :
    let K := {x : EuclideanSpace ℝ (Fin d) | ∀ i, eval x.ofLp (P i)=0} ∩ closedBall a R
    (actualSetComponents K).Finite ∧ (actualSetComponents K).ncard≤(4*D+5)^d := by
  classical
  let e := Fintype.equivFin ι
  have hb := compact_algebraic_components_bound (fun j => P (e.symm j))
    (fun j => hP (e.symm j)) a R hR
  have he : {x : EuclideanSpace ℝ (Fin d) | ∀ j, eval x.ofLp (P (e.symm j))=0}=
      {x | ∀ i, eval x.ofLp (P i)=0} := by
    ext x
    constructor
    · intro hx i
      simpa only [e.symm_apply_apply] using hx (e i)
    · intro hx j
      exact hx (e.symm j)
  dsimp only at hb ⊢
  rwa [he] at hb

def coordinateSlicePolynomials {d s : ℕ} (P : Fin s→MvPolynomial (Fin d) ℝ)
    (a theta : Fin d→ℝ) (h : ℝ) (z : Fin d→ℤ) (J : Finset (Fin d)) :
    (Fin s ⊕ J)→MvPolynomial (Fin d) ℝ :=
  Sum.elim P (fun j => X j.val-C (gridLevel a theta h z j))

def coordinateGridPlane {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ)
    (z : Fin d→ℤ) (J : Finset (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ j∈J, x j=gridLevel a theta h z j}

theorem coordinateSlicePolynomials_zero {d s : ℕ} (P : Fin s→MvPolynomial (Fin d) ℝ)
    (a theta : Fin d→ℝ) (h : ℝ) (z : Fin d→ℤ) (J : Finset (Fin d)) :
    {x : EuclideanSpace ℝ (Fin d) | ∀ i, eval x.ofLp (coordinateSlicePolynomials P a theta h z J i)=0}=
      {x | rectangularPolynomialMap P x=0} ∩ coordinateGridPlane a theta h z J := by
  ext x
  simp only [mem_ofPred_eq,mem_inter_iff]
  constructor
  · intro hx
    constructor
    · ext j
      exact hx (Sum.inl j)
    · intro j hj
      have hh := hx (Sum.inr ⟨j,hj⟩)
      simpa [coordinateSlicePolynomials,sub_eq_zero] using hh
  · rintro ⟨hx,hp⟩ i
    cases i with
    | inl i => exact congrArg (fun v : EuclideanSpace ℝ (Fin s) => v i) hx
    | inr j => simpa [coordinateSlicePolynomials,sub_eq_zero] using hp j j.property

/-- Every actual coordinate slice has a uniform compact component bound in
the ORIGINAL ambient space. No reduced-coordinate rank or sphere regularity
hypothesis is introduced. -/
theorem coordinate_slice_components_bound {d s D : ℕ}
    (P : Fin s→MvPolynomial (Fin d) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (a theta : Fin d→ℝ) (h : ℝ) (z : Fin d→ℤ) (J : Finset (Fin d))
    (center : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR : 0≤R) :
    let K := ({x | rectangularPolynomialMap P x=0} ∩ coordinateGridPlane a theta h z J) ∩
      closedBall center R
    (actualSetComponents K).Finite ∧ (actualSetComponents K).ncard≤(4*max D 1+5)^d := by
  have hdeg (i : Fin s ⊕ J) :
      (coordinateSlicePolynomials P a theta h z J i).totalDegree≤ max D 1 := by
    cases i with
    | inl j => exact (hP j).trans (le_max_left _ _)
    | inr j =>
      exact (totalDegree_sub _ _).trans (max_le ((totalDegree_X j.val).le.trans (le_max_right _ _))
        (by rw [totalDegree_C]; omega))
  have hb := compact_algebraic_components_bound_fintype
    (coordinateSlicePolynomials P a theta h z J) hdeg center R hR
  dsimp only at hb ⊢
  rwa [coordinateSlicePolynomials_zero] at hb

end KakeyaTwoScale
#print axioms KakeyaTwoScale.compact_algebraic_components_bound_fintype
#print axioms KakeyaTwoScale.coordinateSlicePolynomials_zero
#print axioms KakeyaTwoScale.coordinate_slice_components_bound
