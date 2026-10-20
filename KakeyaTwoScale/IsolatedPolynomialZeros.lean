module
public import KakeyaTwoScale.AlgebraicProjectionBarrier

@[expose] public section

open Set Metric MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Degree-uniform bound for any finite collection of isolated zeros of a
nonnegative polynomial. Isolation is local in the FULL zero set; other zeros
may be singular, nonisolated and unbounded. -/
theorem isolated_nonnegative_polynomial_zeros_card_le {n D : ℕ} {I : Type*} [Fintype I]
    (G : MvPolynomial (Fin n) ℝ) (hdeg : G.totalDegree ≤ D)
    (hnonneg : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ eval (fun j => z j) G)
    (x : I → EuclideanSpace ℝ (Fin n)) (hxinj : Function.Injective x)
    (hzero : ∀ i, eval (fun j => x i j) G=0)
    (hiso : ∀ i, ∃ r : ℝ, 0 < r ∧ ∀ z : EuclideanSpace ℝ (Fin n),
      dist z (x i) ≤ r → eval (fun j => z j) G=0 → z=x i) :
    Fintype.card I ≤ (2*D+1)^n := by
  classical
  choose r hr hiso using hiso
  let f (z : EuclideanSpace ℝ (Fin n)) := eval (fun j => z j) G
  have hf : Continuous f := G.continuous_eval.comp
    (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
  let T : Set (EuclideanSpace ℝ (Fin n)) := ⋃ i, sphere (x i) (r i)
  have hT : IsCompact T := isCompact_iUnion (fun i => isCompact_sphere (x i) (r i))
  have hTpos : ∀ z ∈ T, 0 < f z := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hd : dist z (x i)=r i := hi
    have hn : f z ≠ 0 := by
      intro he
      have hz := hiso i z hd.le he
      rw [hz,dist_self] at hd
      linarith [hr i]
    exact lt_of_le_of_ne (hnonneg z) hn.symm
  obtain ⟨a,ha,hlower⟩ := hT.exists_forall_le' hf.continuousOn hTpos
  let Q : MvPolynomial (Fin n) ℝ := C (a/2)-G
  have hQeval (z : EuclideanSpace ℝ (Fin n)) : eval (fun j => z j) Q=a/2-f z := by
    simp [Q,f]
  have hQdeg : Q.totalDegree ≤ D :=
    (totalDegree_sub _ _).trans (by simpa only [totalDegree_C,Nat.zero_max] using hdeg)
  have hpos (i : I) : 0 < eval (fun j => x i j) Q := by
    rw [hQeval]
    have hh : f (x i)=0 := hzero i
    rw [hh]
    linarith
  have hcut (i : I) (z : EuclideanSpace ℝ (Fin n)) (hz : dist z (x i)=r i) :
      eval (fun j => z j) Q < 0 := by
    have hh := hlower z (mem_iUnion.mpr ⟨i,hz⟩)
    rw [hQeval]
    linarith
  let Cc (i : I) := connectedComponentIn (ambientPolynomialZeroSet Q)ᶜ (x i)
  have hx (i : I) : x i ∈ Cc i := mem_connectedComponentIn (hpos i).ne'
  have hCpos (i : I) : ∀ z ∈ Cc i, 0 < eval (fun j => z j) Q := by
    intro z hz
    exact (preconnected_polynomial_sign_constant Q (Cc i)
      isPreconnected_connectedComponentIn
      (fun _ hw => connectedComponentIn_subset _ _ hw) (hx i) hz).mp (hpos i)
  have hinj : Function.Injective Cc := by
    intro i j he
    by_contra hij
    have hd : r i < dist (x j) (x i) := by
      by_contra hnot
      have heq := hiso i (x j) (le_of_not_gt hnot) (hzero j)
      exact hij (hxinj heq.symm)
    have hxj : x j ∈ Cc i := he.symm ▸ hx j
    have hc : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) => dist z (x i)) (Cc i) :=
      (continuous_id.dist continuous_const).continuousOn
    obtain ⟨z,hz,hzr⟩ := isPreconnected_connectedComponentIn.intermediate_value
      (hx i) hxj hc (show r i ∈ Icc (dist (x i) (x i)) (dist (x j) (x i)) by
        simpa using And.intro (hr i).le hd.le)
    exact (not_lt_of_ge (hCpos i z hz).le) (hcut i z hzr)
  have hs : Set.range Cc ⊆ polynomialComplementComponents Q := by
    rintro _ ⟨i,rfl⟩
    exact ⟨x i,(hpos i).ne',rfl⟩
  have hh := finite_polynomial_complement_components_card_le Q hQdeg
    (Finset.univ.image Cc) (by simpa using hs)
  rwa [Finset.card_image_of_injective _ hinj,Finset.card_univ] at hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.isolated_nonnegative_polynomial_zeros_card_le
