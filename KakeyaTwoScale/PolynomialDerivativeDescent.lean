module
public import KakeyaTwoScale.FormalPolynomialJacobian
public import Mathlib.Data.Finsupp.Order

@[expose] public section

open MvPolynomial
noncomputable section
namespace KakeyaTwoScale

theorem polynomial_eq_constant_of_pderiv_zero {σ : Type*}
    (P : MvPolynomial σ ℝ) (h : ∀ j, pderiv j P = 0) : P = C (P.coeff 0) := by
  classical
  ext s
  by_cases hs : s = 0
  · simp [hs]
  · obtain ⟨j,hj⟩ : ∃ j, s j ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hs (Finsupp.ext hh)
    have hle : Finsupp.single j 1 ≤ s := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj)
    have hc := congrArg (fun Q : MvPolynomial σ ℝ => Q.coeff (s-Finsupp.single j 1)) (h j)
    rw [coeff_pderiv] at hc
    simp only [tsub_add_cancel_of_le hle] at hc
    change _ = (0 : ℝ) at hc
    have hn : (Nat.cast ((s - (Finsupp.single j 1 : σ →₀ ℕ)) j) : ℝ) + 1 ≠ 0 := by positivity
    have hp : P.coeff s = 0 := (mul_eq_zero.mp hc).resolve_right hn
    simp [coeff_C,Ne.symm hs,hp]

theorem pderiv_totalDegree_lt {σ : Type*} (P : MvPolynomial σ ℝ) (j : σ)
    (hP : P.totalDegree ≠ 0) : (pderiv j P).totalDegree < P.totalDegree := by
  classical
  apply (Finset.sup_lt_iff (Nat.pos_of_ne_zero hP)).mpr
  intro s hs
  have hc := MvPolynomial.mem_support_iff.mp hs
  rw [coeff_pderiv] at hc
  have hsp : s+Finsupp.single j 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hh := MvPolynomial.le_totalDegree hsp
  simp [Finsupp.sum_add_index] at hh
  omega

/-- A finite derivative family; its definition is independent of the point. -/
def derivativeCoverFamily {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : ℕ → Finset (MvPolynomial (Fin n) ℝ)
  | 0 => ∅
  | D+1 => insert P (Finset.univ.biUnion fun j => derivativeCoverFamily (pderiv j P) D)

theorem derivativeCoverFamily_card {n D : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (derivativeCoverFamily P D).card ≤ (n+1)^D := by
  induction D generalizing P with
  | zero => simp [derivativeCoverFamily]
  | succ D ih =>
    calc
      (derivativeCoverFamily P (D+1)).card ≤
          1 + ∑ j : Fin n, (derivativeCoverFamily (pderiv j P) D).card := by
        apply (Finset.card_insert_le _ _).trans
        have hh := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n)))
          (t := fun j => derivativeCoverFamily (pderiv j P) D)
        omega
      _ ≤ 1 + n*(n+1)^D := by
        gcongr
        simpa using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => ih (pderiv j P))
      _ ≤ (n+1)^(D+1) := by
        have hp : 1 ≤ (n+1)^D := Nat.one_le_pow D (n+1) (by omega)
        rw [pow_succ]
        nlinarith

theorem derivativeCoverFamily_degree {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (Q : MvPolynomial (Fin n) ℝ) (hQ : Q ∈ derivativeCoverFamily P D) :
    Q.totalDegree ≤ P.totalDegree := by
  induction D generalizing P with
  | zero => simp [derivativeCoverFamily] at hQ
  | succ D ih =>
    simp only [derivativeCoverFamily,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_univ,true_and] at hQ
    rcases hQ with rfl | ⟨j,hj⟩
    · exact le_rfl
    · exact (ih _ hj).trans (pderiv_totalDegree_le P j)

/-- All zeros, including singular zeros, lie on a regular zero of a member
of the fixed finite derivative family. This is containment, not stratification. -/
theorem derivativeCoverFamily_covers {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P ≠ 0) (hD : P.totalDegree ≤ D) (x : Fin n → ℝ) (hx : eval x P = 0) :
    ∃ Q ∈ derivativeCoverFamily P D, eval x Q = 0 ∧ ∃ j, eval x (pderiv j Q) ≠ 0 := by
  induction D generalizing P with
  | zero =>
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hD)
    have hc : P.coeff 0 = 0 := by rw [he,eval_C] at hx; exact hx
    exact (hP (by rw [he,hc,map_zero])).elim
  | succ D ih =>
    by_cases hr : ∃ j, eval x (pderiv j P) ≠ 0
    · exact ⟨P,Finset.mem_insert_self _ _,hx,hr⟩
    · have he : ∃ j, pderiv j P ≠ 0 := by
        by_contra hh
        push Not at hh
        have hc := polynomial_eq_constant_of_pderiv_zero P hh
        have hz : P.coeff 0 = 0 := by rw [hc,eval_C] at hx; exact hx
        exact hP (by rw [hc,hz,map_zero])
      obtain ⟨j,hj⟩ := he
      have hp : P.totalDegree ≠ 0 := by
        intro hz
        have hc := totalDegree_eq_zero_iff_eq_C.mp hz
        exact hj (by rw [hc,pderiv_C])
      have hd := pderiv_totalDegree_lt P j hp
      have hzero : eval x (pderiv j P)=0 := by simpa using not_exists.mp hr j
      obtain ⟨Q,hQ,hz,hreg⟩ := ih (pderiv j P) hj (by omega) hzero
      refine ⟨Q,Finset.mem_insert_of_mem ?_,hz,hreg⟩
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hQ⟩

/-- Intersecting back with the original zero set removes all extra points.
The pieces need not have the dimension of their containing hypersurfaces. -/
theorem derivativeCoverFamily_exact_restricted_cover {n D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0) (hD : P.totalDegree ≤ D) :
    {x | eval x P = 0} = ⋃ Q ∈ derivativeCoverFamily P D,
      {x | eval x P = 0 ∧ eval x Q = 0 ∧ ∃ j, eval x (pderiv j Q) ≠ 0} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨Q,hQ,hz,hr⟩ := derivativeCoverFamily_covers P hP hD x hx
    exact ⟨Q,hQ,hx,hz,hr⟩
  · rintro ⟨Q,hQ,hx,hz,hr⟩
    exact hx

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_eq_constant_of_pderiv_zero
#print axioms KakeyaTwoScale.pderiv_totalDegree_lt
#print axioms KakeyaTwoScale.derivativeCoverFamily_card
#print axioms KakeyaTwoScale.derivativeCoverFamily_degree
#print axioms KakeyaTwoScale.derivativeCoverFamily_covers
#print axioms KakeyaTwoScale.derivativeCoverFamily_exact_restricted_cover
