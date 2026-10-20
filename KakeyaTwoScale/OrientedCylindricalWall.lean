module
public import KakeyaTwoScale.PolynomialCoordinateRename
public import KakeyaTwoScale.BufferedPolynomialGeometry
public import KakeyaTwoScale.AmbientPolynomialWall

@[expose] public section

open Set MvPolynomial Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The physical Fin-index projection corresponding to the selected orientation. -/
def orientedFiniteProjection {b c : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)) :
    EuclideanSpace ℝ (Fin (b+c)) →L[ℝ] EuclideanSpace ℝ (Fin b) :=
  coordinateBaseProjection.comp (e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (euclideanCoordinateRename finSumFinEquiv).symm.toContinuousLinearEquiv.toContinuousLinearMap)

def orientedFiniteFactor {b c : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (q : MvPolynomial (Fin b) ℝ) : MvPolynomial (Fin (b+c)) ℝ :=
  rename finSumFinEquiv (polynomialLinearPullback e.toContinuousLinearEquiv.toContinuousLinearMap
    (sumCylindricalPolynomial q))

theorem orientedFiniteFactor_eval {b c : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (q : MvPolynomial (Fin b) ℝ) (x : EuclideanSpace ℝ (Fin (b+c))) :
    eval x (orientedFiniteFactor e q)=eval (orientedFiniteProjection e x) q := by
  let R := euclideanCoordinateRename (finSumFinEquiv : Fin b ⊕ Fin c ≃ Fin (b+c))
  have hh := polynomialCoordinateRename_eval finSumFinEquiv
    (polynomialLinearPullback e.toContinuousLinearEquiv.toContinuousLinearMap (sumCylindricalPolynomial q))
    (R.symm x)
  change eval (R (R.symm x)) (orientedFiniteFactor e q)=_ at hh
  rw [R.apply_symm_apply] at hh
  rw [hh,polynomialLinearPullback_eval,sumCylindricalPolynomial_eval]
  rfl

theorem orientedFiniteFactor_degree {b c : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (q : MvPolynomial (Fin b) ℝ) : (orientedFiniteFactor e q).totalDegree≤q.totalDegree :=
  (totalDegree_rename_le _ _).trans ((polynomialLinearPullback_degree _ _).trans
    (totalDegree_rename_le _ _))

theorem orientedFiniteProjection_dist_le {b c : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (x y : EuclideanSpace ℝ (Fin (b+c))) :
    dist (orientedFiniteProjection e x) (orientedFiniteProjection e y)≤dist x y := by
  let R := euclideanCoordinateRename (finSumFinEquiv : Fin b ⊕ Fin c ≃ Fin (b+c))
  change dist (coordinateBaseProjection (e (R.symm x)))
    (coordinateBaseProjection (e (R.symm y))) ≤ _
  rw [dist_eq_norm,← map_sub]
  calc
    _ ≤ ‖coordinateBaseProjection (b:=Fin b) (c:=Fin c)‖ * ‖e (R.symm x)-e (R.symm y)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖e (R.symm x)-e (R.symm y)‖ :=
      mul_le_mul_of_nonneg_right coordinateBaseProjection_norm_le (norm_nonneg _)
    _ = dist x y := by rw [one_mul,← dist_eq_norm,e.dist_map,R.symm.dist_map]

/-- Exact physical product-wall identity, with actual transformed factors. -/
theorem orientedFiniteFactor_product_zero {b c s : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (q : Fin s → MvPolynomial (Fin b) ℝ) (x : EuclideanSpace ℝ (Fin (b+c))) :
    x ∈ ambientPolynomialZeroSet (∏ i, orientedFiniteFactor e (q i)) ↔
      orientedFiniteProjection e x ∈ polynomialFactorZeros q := by
  classical
  change eval x (∏ i, orientedFiniteFactor e (q i))=0 ↔ ∃ i, eval (orientedFiniteProjection e x) (q i)=0
  simp only [map_prod,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,orientedFiniteFactor_eval]

/-- An open projected buffer of radius r gives the closed physical product
wall clearance of every smaller radius, without a nearest-point hypothesis. -/
theorem orientedFiniteFactor_avoids_closed_wall {b c s : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (q : Fin s → MvPolynomial (Fin b) ℝ) (x : EuclideanSpace ℝ (Fin (b+c)))
    (a r : ℝ) (hr : 0<r) (har : a<r)
    (hx : orientedFiniteProjection e x ∉ thickening r (polynomialFactorZeros q)) :
    x ∉ cthickening a (ambientPolynomialZeroSet (∏ i, orientedFiniteFactor e (q i))) := by
  intro hwall
  have ho := cthickening_subset_thickening' hr har _ hwall
  obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp ho
  apply hx
  exact mem_thickening_iff.mpr ⟨orientedFiniteProjection e y,
    (orientedFiniteFactor_product_zero e q y).mp hy,
    (orientedFiniteProjection_dist_le e x y).trans_lt hxy⟩

/-- Whole-set sign owners become actual physical polynomial sign owners. -/
theorem orientedFiniteFactor_signCell {b c s : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (q : Fin s → MvPolynomial (Fin b) ℝ) (owner : Fin s → Bool) :
    polynomialSignCell (fun i => orientedFiniteFactor e (q i)) owner=
      orientedFiniteProjection e ⁻¹' polynomialSignCell q owner := by
  ext x
  change (∀ i, x ∈ polynomialSignSide (orientedFiniteFactor e (q i)) (owner i)) ↔
    ∀ i, orientedFiniteProjection e x ∈ polynomialSignSide (q i) (owner i)
  refine forall_congr' (fun i => ?_)
  cases owner i <;> simp [polynomialSignSide,orientedFiniteFactor_eval]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orientedFiniteFactor_eval
#print axioms KakeyaTwoScale.orientedFiniteFactor_degree
#print axioms KakeyaTwoScale.orientedFiniteProjection_dist_le
#print axioms KakeyaTwoScale.orientedFiniteFactor_product_zero
#print axioms KakeyaTwoScale.orientedFiniteFactor_avoids_closed_wall
#print axioms KakeyaTwoScale.orientedFiniteFactor_signCell
