module
public import KakeyaTwoScale.SignConditionIsolatedPoints
public import KakeyaTwoScale.RegularPolynomialFibers
public import KakeyaTwoScale.PolynomialBaseSpecialization

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- A C1 map's regular fiber has a uniform bound whenever that actual whole
fiber is specified by bounded-degree polynomial signs. The derivative need not
have a polynomial or semialgebraic description. -/
theorem sign_description_regular_fiber_encard_le {n s D : ℕ}
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 1 f)
    (P : Fin s → MvPolynomial (Fin n) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (accept : (Fin s → SignType) → Prop) (y : Fin n → ℝ)
    (hdesc : ∀ x, f x=y ↔ accept (fun j => SignType.sign (eval x (P j)))) :
    Set.encard {x : Fin n → ℝ | f x=y ∧ (fderiv ℝ f x).det≠0}≤
      (2^s*(4*D+1)^n : ℕ) := by
  classical
  apply Set.encard_le_coe_iff_finite_ncard_le.mpr
  apply finite_ncard_le_of_finset_bound
  intro A hA
  let xE : A → EuclideanSpace ℝ (Fin n) := fun a => WithLp.toLp 2 a.val
  have hx (a : A) : xE a∈polynomialSignSet P accept :=
    (hdesc a.val).mp (hA a.property).1
  have hi (a : A) : ∃ r : ℝ, 0<r ∧ ∀ z,
      dist z (xE a)≤r → z∈polynomialSignSet P accept → z=xE a := by
    obtain ⟨r,hr,hiso⟩ := contDiff_det_ne_zero_isolates_fiber f a.val hf (hA a.property).2
    have hc : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) => (fun j => z j)) (xE a) :=
      (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).continuousAt
    obtain ⟨e,he,hsmall⟩ := Metric.continuousAt_iff.mp hc r hr
    refine ⟨e/2,by positivity,?_⟩
    intro z hz hzmem
    have hd : dist (fun j => z j) a.val≤r :=
      (hsmall (show dist z (xE a)<e by linarith)).le
    have hzmap : f (fun j => z j)=f a.val :=
      ((hdesc _).mpr hzmem).trans (hA a.property).1.symm
    have heq := hiso (fun j => z j) hd hzmap
    ext j
    exact congrFun heq j
  have hh := sign_condition_isolated_points_card_le P hP accept xE
    (fun a b h => Subtype.ext (congrArg WithLp.ofLp h)) hx hi
  simpa only [Fintype.card_coe] using hh

/-- Affine substitution cannot increase total degree. This includes a zero
or constant atom and coefficients depending on an arbitrary output and time. -/
theorem polynomial_affine_substitution_degree {ι κ : Type*}
    (P : MvPolynomial ι ℝ) (f : ι → MvPolynomial κ ℝ)
    (hf : ∀ i, (f i).totalDegree≤1) :
    (P.eval₂ C f).totalDegree≤P.totalDegree := by
  classical
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro a ha
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans _ (le_totalDegree ha)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (a i) (hf i))

/-- Graph atoms use (output,input) coordinates. Substitute output=z-t*input. -/
def sliceGraphPolynomial {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin n) ℝ)
    (t : ℝ) (z : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  P.eval₂ C (Sum.elim (fun i => C (z i)-C t*X i) X)

theorem sliceGraphPolynomial_degree {n : ℕ}
    (P : MvPolynomial (Fin n ⊕ Fin n) ℝ) (t : ℝ) (z : Fin n → ℝ) :
    (sliceGraphPolynomial P t z).totalDegree≤P.totalDegree := by
  apply polynomial_affine_substitution_degree
  intro i
  cases i with
  | inl i =>
    apply (totalDegree_sub _ _).trans
    apply max_le (by simp)
    exact (totalDegree_mul _ _).trans (by simp)
  | inr i => simp

theorem sliceGraphPolynomial_eval {n : ℕ}
    (P : MvPolynomial (Fin n ⊕ Fin n) ℝ) (t : ℝ) (z x : Fin n → ℝ) :
    eval x (sliceGraphPolynomial P t z)=eval (Sum.elim (z-t • x) x) P := by
  change (eval₂Hom (RingHom.id ℝ) x)
    (P.eval₂ C (Sum.elim (fun i => C (z i)-C t*X i) X))=_
  rw [eval₂_comp_left]
  have hc : (eval₂Hom (RingHom.id ℝ) x).comp C=RingHom.id ℝ := by ext a; simp
  rw [hc]
  congr 1
  funext i
  cases i <;> simp

/-- No regular-fiber cardinality premise: it follows from the actual polynomial
sign description of the intercept graph, uniformly in time and target point. -/
theorem sign_graph_regular_slice_encard_le {n s D : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 1 F)
    (P : Fin s → MvPolynomial (Fin n ⊕ Fin n) ℝ)
    (hP : ∀ j, (P j).totalDegree≤D) (accept : (Fin s → SignType) → Prop)
    (hgraph : ∀ x w, F x=w ↔ accept (fun j => SignType.sign (eval (Sum.elim w x) (P j))))
    (t : ℝ) (z : Fin n → ℝ) :
    Set.encard {x : Fin n → ℝ | F x+t • x=z ∧
      (fderiv ℝ (fun x => F x+t • x) x).det≠0}≤(2^s*(4*D+1)^n : ℕ) := by
  apply sign_description_regular_fiber_encard_le (fun x => F x+t • x)
    (hF.add (contDiff_id.const_smul t)) (fun j => sliceGraphPolynomial (P j) t z)
    (fun j => (sliceGraphPolynomial_degree _ _ _).trans (hP j)) accept z
  intro x
  simp_rw [sliceGraphPolynomial_eval]
  rw [← hgraph]
  exact eq_sub_iff_add_eq.symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sign_description_regular_fiber_encard_le
#print axioms KakeyaTwoScale.sign_graph_regular_slice_encard_le
