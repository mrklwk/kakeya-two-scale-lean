module
public import KakeyaTwoScale.NormalizedQuadraticPacking

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

def linearGramMatrix {N : ℕ} (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (i j : Fin N) : ℝ :=
  inner ℝ (WithLp.toLp 2 (L (Pi.single i 1)) : EuclideanSpace ℝ (Fin N))
    (WithLp.toLp 2 (L (Pi.single j 1)))

theorem linearGramMatrix_value {N : ℕ}
    (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (x : Fin N → ℝ) :
    matrixQuadraticValue (linearGramMatrix L) x =
      ‖(WithLp.toLp 2 (L x) : EuclideanSpace ℝ (Fin N))‖^2 := by
  have hx : x = ∑ i, x i • Pi.single i 1 := by ext j; simp [Pi.single_apply]
  have he : (WithLp.toLp 2 (L x) : EuclideanSpace ℝ (Fin N)) =
      ∑ i, x i • WithLp.toLp 2 (L (Pi.single i 1)) := by
    conv_lhs => rw [hx]
    simp only [map_sum,map_smul]
    ext k
    simp
  rw [← real_inner_self_eq_norm_sq,he]
  simp only [matrixQuadraticValue,linearGramMatrix,inner_sum,sum_inner,
    real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (WithLp.toLp 2 (L (Pi.single j 1)))]
  ring

/-- A quadratic upper bound controls every Gram coefficient, without spectral
or principal-axis choices. -/
theorem linearGramMatrix_entry_bound {N : ℕ}
    (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (R : ℝ)
    (hL : ∀ x, ‖(WithLp.toLp 2 (L x) : EuclideanSpace ℝ (Fin N))‖^2 ≤
      R*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2) (i j : Fin N) :
    |linearGramMatrix L i j| ≤ R := by
  have hei (k : Fin N) : (WithLp.toLp 2 (Pi.single k (1:ℝ)) : EuclideanSpace ℝ (Fin N)) =
      EuclideanSpace.single k 1 := by ext; rfl
  have hi := hL (Pi.single i 1)
  have hj := hL (Pi.single j 1)
  simp only [hei,PiLp.norm_single,Real.norm_eq_abs,abs_one,one_pow,mul_one] at hi hj
  have hab := abs_real_inner_le_norm
    (WithLp.toLp 2 (L (Pi.single i 1)) : EuclideanSpace ℝ (Fin N))
    (WithLp.toLp 2 (L (Pi.single j 1)))
  change |linearGramMatrix L i j| ≤ _ at hab
  nlinarith [sq_nonneg (‖(WithLp.toLp 2 (L (Pi.single i 1)) : EuclideanSpace ℝ (Fin N))‖-
    ‖(WithLp.toLp 2 (L (Pi.single j 1)) : EuclideanSpace ℝ (Fin N))‖)]

/-- Multiplicative comparison of the actual inverse-map quadratic forms of two
centered ellipsoids. Squared radii are used in this predicate. -/
def ellipsoidFormComparable {N : ℕ} (R : ℝ)
    (A B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) : Prop :=
  ∀ x, ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖^2 ≤
      R*‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖^2 ∧
    ‖(WithLp.toLp 2 (B.symm x) : EuclideanSpace ℝ (Fin N))‖^2 ≤
      R*‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖^2

theorem ellipsoidFormComparable_symm {N : ℕ} (R : ℝ)
    (A B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) :
    ellipsoidFormComparable R A B ↔ ellipsoidFormComparable R B A :=
  ⟨fun h x => (h x).symm,fun h x => (h x).symm⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.linearGramMatrix_value
#print axioms KakeyaTwoScale.linearGramMatrix_entry_bound
#print axioms KakeyaTwoScale.ellipsoidFormComparable_symm
