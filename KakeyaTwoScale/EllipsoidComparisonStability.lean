module
public import KakeyaTwoScale.NormalizedBodyEllipsoid
public import KakeyaTwoScale.UnitBallEllipsoidPacking

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

theorem ellipsoidFormComparable_trans {N : ℕ} {R S : ℝ} (hR : 0≤R) (hS : 0≤S)
    {A B C : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)}
    (hAB : ellipsoidFormComparable R A B) (hBC : ellipsoidFormComparable S B C) :
    ellipsoidFormComparable (R*S) A C := by
  intro x
  constructor
  · exact (hAB x).1.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hBC x).1 hR)
  · exact (hBC x).2.trans (by
      simpa only [← mul_assoc,mul_comm S R] using mul_le_mul_of_nonneg_left (hAB x).2 hS)

theorem ellipsoidFormComparable_mono {N : ℕ} {R S : ℝ} (hRS : R≤S)
    {A B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)}
    (h : ellipsoidFormComparable R A B) : ellipsoidFormComparable S A B := by
  intro x
  exact ⟨(h x).1.trans (mul_le_mul_of_nonneg_right hRS (sq_nonneg _)),
    (h x).2.trans (mul_le_mul_of_nonneg_right hRS (sq_nonneg _))⟩

/-- Actual cross-inclusions of unit ellipsoids imply form comparison, with a
concrete uniform constant. This converts geometric body margins to conflicts. -/
theorem ellipsoid_comparable_of_cross_bounds {N : ℕ}
    (A B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (C : ℝ) (hC : 0≤C)
    (hAB : ∀ x ∈ affineEllipsoid A 0,
      ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤ C)
    (hBA : ∀ x ∈ affineEllipsoid B 0,
      ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤ C) :
    ellipsoidFormComparable ((2*C)^2) A B := by
  have forward (L T : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
      (h : ∀ x ∈ affineEllipsoid L 0,
        ‖(WithLp.toLp 2 (T.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤ C) (x) :
      ‖(WithLp.toLp 2 (T.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤
        (2*C)*‖(WithLp.toLp 2 (L.symm x) : EuclideanSpace ℝ (Fin N))‖ := by
    have hb := coordinate_linear_bound_from_ball (L.trans T.symm) 1 C zero_lt_one
      (fun z hz => h _ ⟨z,hz,by simp⟩) (L.symm x)
    simpa only [ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.apply_symm_apply,div_one] using hb
  intro x
  have h1 := forward A B hAB x
  have h2 := forward B A hBA x
  have hp1 := norm_nonneg (WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))
  have hp2 := norm_nonneg (WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))
  constructor
  · nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hC) hp2]
  · nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hC) hp1]

/-- A strict conflict margin is available before taking coefficient limits:
labels of the same color must agree whenever their two intervening shapes are
sufficiently comparable. All comparisons here use squared form factors. -/
theorem same_color_comparable_labels_eq {N : ℕ}
    (F : Finset ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)))
    (color : ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) → ℕ)
    (R κ γ : ℝ) (hκ : 0≤κ) (hγ : 0≤γ) (hmargin : κ*γ*κ ≤ R)
    (hcolor : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ellipsoidFormComparable R A B → color A ≠ color B)
    (A B C D : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (hA : A ∈ F) (hB : B ∈ F)
    (hcol : color A=color B) (hAC : ellipsoidFormComparable κ A C)
    (hCD : ellipsoidFormComparable γ C D) (hDB : ellipsoidFormComparable κ D B) : A=B := by
  by_contra hne
  apply hcolor A hA B hB hne _ hcol
  apply ellipsoidFormComparable_mono hmargin
  exact ellipsoidFormComparable_trans (mul_nonneg hκ hγ) hκ
    (ellipsoidFormComparable_trans hκ hγ hAC hCD) hDB

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ellipsoidFormComparable_trans
#print axioms KakeyaTwoScale.ellipsoidFormComparable_mono
#print axioms KakeyaTwoScale.ellipsoid_comparable_of_cross_bounds
#print axioms KakeyaTwoScale.same_color_comparable_labels_eq
