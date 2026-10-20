module
public import KakeyaTwoScale.AlgebraicProjectionBarrier

@[expose] public section

open Set Metric MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Finite positive witnesses separated by nonpositive coordinate fibers
lie in distinct actual polynomial-complement components. -/
theorem positive_projection_separated_count {n D : ℕ} {I : Type*} [Fintype I]
    (Q : MvPolynomial (Fin n) ℝ) (coordinate : Fin n)
    (x : I → EuclideanSpace ℝ (Fin n)) (hdeg : Q.totalDegree ≤ D)
    (hpos : ∀ i, 0 < eval (fun j => x i j) Q)
    (hsep : ∀ i j, i ≠ j → ∃ r : ℝ,
      ((x i coordinate < r ∧ r < x j coordinate) ∨
       (x j coordinate < r ∧ r < x i coordinate)) ∧
      ∀ z : EuclideanSpace ℝ (Fin n), z coordinate=r → eval (fun j => z j) Q ≤ 0) :
    Fintype.card I ≤ (2*D+1)^n := by
  classical
  let C (i : I) := connectedComponentIn (ambientPolynomialZeroSet Q)ᶜ (x i)
  have hx (i : I) : x i ∈ C i := mem_connectedComponentIn (hpos i).ne'
  have hCpos (i : I) : ∀ z ∈ C i, 0 < eval (fun j => z j) Q := by
    intro z hz
    have hh := preconnected_polynomial_sign_constant Q (C i)
      isPreconnected_connectedComponentIn
      (fun _ hw => connectedComponentIn_subset _ _ hw) (hx i) hz
    exact hh.mp (hpos i)
  have hinj : Function.Injective C := by
    intro i j he
    by_contra hne
    obtain ⟨r,hr,hcut⟩ := hsep i j hne
    have hxj : x j ∈ C i := he.symm ▸ hx j
    have hc : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) => z coordinate) (C i) :=
      (EuclideanSpace.proj coordinate).continuous.continuousOn
    have hex : ∃ z ∈ C i, z coordinate=r := by
      rcases hr with hr | hr
      · exact isPreconnected_connectedComponentIn.intermediate_value (hx i) hxj hc ⟨hr.1.le,hr.2.le⟩
      · exact isPreconnected_connectedComponentIn.intermediate_value hxj (hx i) hc ⟨hr.1.le,hr.2.le⟩
    obtain ⟨z,hz,hzr⟩ := hex
    exact (not_le_of_gt (hCpos i z hz)) (hcut z hzr)
  have hs : Set.range C ⊆ polynomialComplementComponents Q := by
    rintro _ ⟨i,rfl⟩
    exact ⟨x i,(hpos i).ne',rfl⟩
  have hh := finite_polynomial_complement_components_card_le Q hdeg
    (Finset.univ.image C) (by simpa using hs)
  rwa [Finset.card_image_of_injective _ hinj,Finset.card_univ] at hh

/-- Actual zeros of a nonnegative polynomial cannot have more mutually
separated projection fibers than the ambient degree bound. All separator
polynomials and epsilon choices are constructed by compactness. -/
theorem algebraic_projection_separated_count {n D : ℕ} {I : Type*} [Fintype I]
    (G : MvPolynomial (Fin n) ℝ) (coordinate : Fin n)
    (x : I → EuclideanSpace ℝ (Fin n)) (hdeg : G.totalDegree ≤ D)
    (hnonneg : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ eval (fun j => z j) G)
    (hzero : ∀ i, eval (fun j => x i j) G=0)
    (hsep : ∀ i j, i ≠ j → ∃ r : ℝ,
      ((x i coordinate < r ∧ r < x j coordinate) ∨
       (x j coordinate < r ∧ r < x i coordinate)) ∧
      ∀ z : EuclideanSpace ℝ (Fin n), z coordinate=r → eval (fun j => z j) G ≠ 0) :
    Fintype.card I ≤ (2*(max D 2)+1)^n := by
  classical
  have hex : ∀ ij : I × I, ∃ r : ℝ, ij.1 ≠ ij.2 →
      ((x ij.1 coordinate < r ∧ r < x ij.2 coordinate) ∨
       (x ij.2 coordinate < r ∧ r < x ij.1 coordinate)) ∧
      ∀ z : EuclideanSpace ℝ (Fin n), z coordinate=r → eval (fun j => z j) G ≠ 0 := by
    intro ij
    by_cases h : ij.1=ij.2
    · exact ⟨0,fun hn => False.elim (hn h)⟩
    · obtain ⟨r,hr⟩ := hsep ij.1 ij.2 h
      exact ⟨r,fun _ => hr⟩
  choose r hr using hex
  let cuts := (Finset.univ.filter (fun ij : I × I => ij.1 ≠ ij.2)).image r
  let R : ℝ := 1+∑ i, ‖x i‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hxR : ∀ i, ‖x i‖ < R := by
    intro i
    have hh := Finset.single_le_sum (f := fun i => ‖x i‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ i)
    dsimp [R]
    linarith
  have hcuts : ∀ z : EuclideanSpace ℝ (Fin n), z coordinate ∈ cuts →
      0 < eval (fun j => z j) G := by
    intro z hz
    obtain ⟨ij,hij,he⟩ := Finset.mem_image.mp hz
    have hn := (hr ij (Finset.mem_filter.mp hij).2).2 z he.symm
    exact lt_of_le_of_ne (hnonneg z) hn.symm
  obtain ⟨Q,hQdeg,hQpos,hQcuts⟩ := exists_algebraic_projection_barrier G coordinate cuts
    hR hdeg hnonneg hcuts
  apply positive_projection_separated_count Q coordinate x hQdeg
    (fun i => hQpos (x i) (hxR i) (hzero i))
  intro i j hij
  refine ⟨r (i,j),(hr (i,j) hij).1,?_⟩
  intro z hz
  apply (hQcuts z ?_).le
  rw [hz]
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,rfl⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.positive_projection_separated_count
#print axioms KakeyaTwoScale.algebraic_projection_separated_count
