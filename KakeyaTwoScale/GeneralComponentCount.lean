module
public import KakeyaTwoScale.PerturbationSelection
public import KakeyaTwoScale.PolynomialCriticalBridge
public import KakeyaTwoScale.CompactSuperlevelMaximum

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- Every finite family of actual complementary components of an arbitrary
real polynomial has the general dimension/degree bound (2D+1)^n. -/
theorem finite_polynomial_complement_components_card_le {n D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D)
    (A : Finset (Set (EuclideanSpace ℝ (Fin n))))
    (hA : (A : Set (Set (EuclideanSpace ℝ (Fin n)))) ⊆ polynomialComplementComponents P) :
    A.card ≤ (2*D+1)^n := by
  classical
  have hrep : ∀ S : A, ∃ x : EuclideanSpace ℝ (Fin n),
      x ∉ ambientPolynomialZeroSet P ∧
        connectedComponentIn (ambientPolynomialZeroSet P)ᶜ x = S.val := fun S => hA S.property
  choose x hx hcomp using hrep
  let v : A → Fin n → ℝ := fun j i => x j i
  have hv : ∀ j, eval (v j) P ≠ 0 := fun j => hx j
  obtain ⟨ε,hε,a,ha,hvalues⟩ := exists_positive_perturbation_superlevel P D v hv
  let Q := coercivePolynomialPerturbation P D ε
  let f : (Fin n → ℝ) → ℝ := fun z => eval z Q
  let S : Set (Fin n → ℝ) := {z | a ≤ f z}
  have hc : IsCompact S := coercivePolynomialPerturbation_superlevel_isCompact P hP ε hε a ha.le
  have hmax : ∀ j : A, ∃ y : Fin n → ℝ, IsLocalMax f y ∧
      WithLp.toLp 2 y ∈ connectedComponentIn (ambientPolynomialZeroSet P)ᶜ (x j) := by
    intro j
    obtain ⟨y,hy,hm,_⟩ := exists_localMax_in_compact_superlevel_component
      f Q.continuous_eval a hc (v j) (hvalues j)
    let C := connectedComponentIn S (v j)
    have himg : IsPreconnected ((WithLp.toLp 2) '' C) :=
      isPreconnected_connectedComponentIn.image _ (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).continuousOn
    have hsub : (WithLp.toLp 2) '' C ⊆ (ambientPolynomialZeroSet P)ᶜ := by
      rintro z ⟨w,hw,rfl⟩
      have hwS : a ≤ f w := connectedComponentIn_subset S (v j) hw
      exact coercivePolynomialPerturbation_pos_nonzero P D ε hε.le w (ha.trans_le hwS)
    have hximg : x j ∈ (WithLp.toLp 2) '' C := by
      refine ⟨v j,mem_connectedComponentIn (hvalues j).le,?_⟩
      ext i
      rfl
    exact ⟨y,hm,himg.subset_connectedComponentIn hximg hsub ⟨y,hy,rfl⟩⟩
  choose y hymax hycomp using hmax
  have hyinj : Function.Injective y := by
    intro j k hjk
    apply Subtype.ext
    rw [← hcomp j,← hcomp k,connectedComponentIn_eq (hycomp j),
      connectedComponentIn_eq (hycomp k),hjk]
  have hcrit := coercivePolynomialPerturbation_localMax_finite_ncard_le P hP ε hε.ne'
  have hsub : Set.range y ⊆ {z : Fin n → ℝ | IsLocalMax f z} := by
    rintro z ⟨j,rfl⟩
    exact hymax j
  have hcard := (Set.ncard_le_ncard hsub hcrit.1).trans hcrit.2
  rw [Set.ncard_range_of_injective hyinj] at hcard
  simpa using hcard

/-- Actual global component finiteness and the explicit general bound, with
no smoothness, genericity, boundedness or assumed component-finiteness premise. -/
theorem polynomialComplementComponents_finite_ncard_le {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    (polynomialComplementComponents P).Finite ∧
      (polynomialComplementComponents P).ncard ≤ (2*P.totalDegree+1)^n :=
  finite_ncard_le_of_finset_bound _ _
    (finite_polynomial_complement_components_card_le P le_rfl)

/-- The explicit O_n(D^n) form for a positive prescribed degree budget. -/
theorem polynomialComplementComponents_ncard_le_degree_budget {n D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D) (hD : 0 < D) :
    (polynomialComplementComponents P).ncard ≤ 3^n * D^n := by
  calc
    _ ≤ (2*P.totalDegree+1)^n := (polynomialComplementComponents_finite_ncard_le P).2
    _ ≤ (3*D)^n := by gcongr; omega
    _ = _ := Nat.mul_pow 3 D n

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_polynomial_complement_components_card_le
#print axioms KakeyaTwoScale.polynomialComplementComponents_finite_ncard_le

#print axioms KakeyaTwoScale.polynomialComplementComponents_ncard_le_degree_budget
