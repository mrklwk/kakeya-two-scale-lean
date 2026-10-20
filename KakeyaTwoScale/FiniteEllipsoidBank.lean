module
public import KakeyaTwoScale.UniformEllipsoidColoring
public import KakeyaTwoScale.FiniteRelationNet

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- Actual inverse-form bounds, with no determinant or spectral certificate. -/
def boundedEllipsoidClass (N : ℕ) (a b : ℝ) :
    Set ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) :=
  {B | ∀ x, a*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 ≤
      ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖^2 ∧
    ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖^2 ≤
      b*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2}

/-- A finite bank of actual ellipsoids covers every bounded/coercive shape.
The conflict palette is chosen before the coercivity and upper bounds, so it
is independent of the bank size and the possible eccentricity. -/
theorem finite_ellipsoid_bank (N : ℕ) (R : ℝ) (hR : 0<R) :
    ∃ M : ℕ, 0<M ∧ ∀ a b : ℝ, 0<a →
      ∃ F : Finset ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)),
        (↑F : Set _) ⊆ boundedEllipsoidClass N a b ∧
        (∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ellipsoidFormComparable 2 A B) ∧
        (∀ A ∈ boundedEllipsoidClass N a b, ∃ B ∈ F, ellipsoidFormComparable 2 A B) ∧
        ∃ c : ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) → ℕ,
          (∀ A ∈ F, c A < M) ∧ ∀ A ∈ F, ∀ B ∈ F,
            A ≠ B → ellipsoidFormComparable R A B → c A ≠ c B := by
  classical
  obtain ⟨M,hM,hcolor⟩ := uniform_ellipsoid_coloring N R hR
  refine ⟨M,hM,?_⟩
  intro a b ha
  let S := boundedEllipsoidClass N a b
  let T := max b (1/a)
  have hT : 0<T := lt_of_lt_of_le (by positivity : (0:ℝ)<1/a) (le_max_right _ _)
  obtain ⟨K,hK⟩ := ellipsoid_neighbor_bound N T hT
  have hnear (B) (hB : B ∈ S) :
      ellipsoidFormComparable T (ContinuousLinearEquiv.refl ℝ (Fin N → ℝ)) B := by
    intro x
    have hb := hB x
    have hq : 0 ≤ ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖^2 := sq_nonneg _
    change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 ≤ T*_ ∧ _ ≤ T*_
    constructor
    · have hh : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 ≤
          ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖^2/a :=
        (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hb.1)
      exact hh.trans (by
        rw [div_eq_mul_inv,mul_comm]
        exact mul_le_mul_of_nonneg_right (by simp [one_div,T]) hq)
    · exact hb.2.trans (mul_le_mul_of_nonneg_right (le_max_left b (1/a)) (sq_nonneg _))
  have hbound (F : Finset ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)))
      (hF : (↑F : Set _) ⊆ S)
      (hsep : (↑F : Set _).Pairwise (fun A B => ¬ellipsoidFormComparable 2 A B)) : F.card ≤ K :=
    hK (ContinuousLinearEquiv.refl ℝ (Fin N → ℝ)) F (fun B hB => hnear B (hF hB))
      (fun A hA B hB hAB => hsep hA hB hAB)
  have hrefl (B) (_hB : B ∈ S) : ellipsoidFormComparable 2 B B := by
    intro x
    have hq := sq_nonneg ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖
    constructor <;> nlinarith
  obtain ⟨F,hFS,hsep,hcover⟩ := finite_relation_net S (ellipsoidFormComparable 2)
    hrefl (fun A B => (ellipsoidFormComparable_symm 2 A B).mp) K hbound
  have hsep' : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ellipsoidFormComparable 2 A B :=
    fun A hA B hB hAB => hsep hA hB hAB
  exact ⟨F,hFS,hsep',hcover,hcolor F hsep'⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_ellipsoid_bank
