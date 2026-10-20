module
public import KakeyaTwoScale.LinearEllipsoidForms

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

theorem normalized_gram_comparison {N : ℕ} (t : ℝ)
    (A B C : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (h : ∀ x, matrixQuadraticValue (linearGramMatrix (A.trans B.symm)) x ≤
        t*matrixQuadraticValue (linearGramMatrix (A.trans C.symm)) x ∧
      matrixQuadraticValue (linearGramMatrix (A.trans C.symm)) x ≤
        t*matrixQuadraticValue (linearGramMatrix (A.trans B.symm)) x) :
    ellipsoidFormComparable t B C := by
  intro x
  simpa only [linearGramMatrix_value,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply] using h (A.symm x)

/-- A uniform local packing bound for actual centered ellipsoids. A finite
factor-two-separated family lying in the R-comparison neighborhood of any A
has at most M(N,R) elements, independently of A and all eccentricities. -/
theorem ellipsoid_neighbor_bound (N : ℕ) (R : ℝ) (hR : 0<R) :
    ∃ M : ℕ, ∀ (A : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
      (F : Finset ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))),
      (∀ B ∈ F, ellipsoidFormComparable R A B) →
      (∀ B ∈ F, ∀ C ∈ F, B ≠ C → ¬ ellipsoidFormComparable 2 B C) →
      F.card ≤ M := by
  classical
  obtain ⟨M,hM⟩ := normalized_quadratic_packing_bound N (1/R) R (by positivity)
  refine ⟨M,?_⟩
  intro A F hnear hsep
  let Q := fun B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) => linearGramMatrix (A.trans B.symm)
  have hupper (B) (hB : B ∈ F) (x : Fin N → ℝ) :
      ‖(WithLp.toLp 2 ((A.trans B.symm) x) : EuclideanSpace ℝ (Fin N))‖^2 ≤
        R*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 := by
    simpa only [ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.symm_apply_apply]
      using (hnear B hB (A x)).2
  have hlower (B) (hB : B ∈ F) (x : Fin N → ℝ) :
      (1/R)*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 ≤ matrixQuadraticValue (Q B) x := by
    simp only [Q,linearGramMatrix_value]
    have hh := (hnear B hB (A x)).1
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hh
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (div_le_iff₀ hR).mpr (by simpa only [ContinuousLinearEquiv.trans_apply,mul_comm] using hh)
  have hinj : Set.InjOn Q (↑F : Set _) := by
    intro B hB C hC he
    by_contra hbc
    apply hsep B hB C hC hbc
    apply normalized_gram_comparison 2 A B C
    change ∀ x, matrixQuadraticValue (Q B) x ≤ 2*matrixQuadraticValue (Q C) x ∧
      matrixQuadraticValue (Q C) x ≤ 2*matrixQuadraticValue (Q B) x
    intro x
    rw [he]
    have hp : 0 ≤ matrixQuadraticValue (Q C) x := by simp only [Q,linearGramMatrix_value]; positivity
    constructor <;> linarith
  have hb : (F.image Q).card ≤ M := by
    apply hM
    · intro T hT i j
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hT
      exact linearGramMatrix_entry_bound _ R (hupper B hB) i j
    · intro T hT x
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hT
      exact hlower B hB x
    · intro T hT V hV hTV hc
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hV
      exact hsep B hB C hC (fun he => hTV (congrArg Q he))
        (normalized_gram_comparison 2 A B C hc)
  rwa [Finset.card_image_of_injOn hinj] at hb

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalized_gram_comparison
#print axioms KakeyaTwoScale.ellipsoid_neighbor_bound
