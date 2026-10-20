module
public import KakeyaTwoScale.BoundedFormatSelection

@[expose] public section

open Set Metric MvPolynomial
noncomputable section
namespace KakeyaTwoScale

theorem contDiffAt_det_ne_zero_isolates_fiber {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E)
    (x : E) (hf : ContDiffAt ℝ 1 f x)
    (hdet : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, dist z x ≤ r → f z = f x → z = x := by
  let e := (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = fderiv ℝ f x := by
    ext z
    simp [e]
  have hd : HasFDerivAt f (e : E →L[ℝ] E) x := by
    rw [he]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  let h := hf.toOpenPartialHomeomorph f hd (by norm_num)
  have hx : x ∈ h.source := hf.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (h.open_source.mem_nhds hx)
  refine ⟨r/2,by positivity,?_⟩
  intro z hz heq
  apply h.injOn (hball (by change dist z x < r; linarith)) hx
  exact heq

theorem sign_description_open_regular_fiber_encard_le {n s D : ℕ}
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (U : Set (Fin n → ℝ)) (hf : ∀ x ∈ U, ContDiffAt ℝ 1 f x)
    (P : Fin s → MvPolynomial (Fin n) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (accept : (Fin s → SignType) → Prop) (y : Fin n → ℝ)
    (hdesc : ∀ x, f x=y ↔ accept (fun j => SignType.sign (eval x (P j)))) :
    Set.encard {x : Fin n → ℝ | x ∈ U ∧ f x=y ∧ (fderiv ℝ f x).det≠0}≤
      (2^s*(4*D+1)^n : ℕ) := by
  classical
  apply Set.encard_le_coe_iff_finite_ncard_le.mpr
  apply finite_ncard_le_of_finset_bound
  intro A hA
  let xE : A → EuclideanSpace ℝ (Fin n) := fun a => WithLp.toLp 2 a.val
  have hx (a : A) : xE a∈polynomialSignSet P accept :=
    (hdesc a.val).mp (hA a.property).2.1
  have hi (a : A) : ∃ r : ℝ, 0<r ∧ ∀ z,
      dist z (xE a)≤r → z∈polynomialSignSet P accept → z=xE a := by
    obtain ⟨r,hr,hiso⟩ := contDiffAt_det_ne_zero_isolates_fiber f a.val (hf a.val (hA a.property).1) (hA a.property).2.2
    have hc : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) => (fun j => z j)) (xE a) :=
      (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).continuousAt
    obtain ⟨e,he,hsmall⟩ := Metric.continuousAt_iff.mp hc r hr
    refine ⟨e/2,by positivity,?_⟩
    intro z hz hzmem
    have hd : dist (fun j => z j) a.val≤r :=
      (hsmall (show dist z (xE a)<e by linarith)).le
    have hzmap : f (fun j => z j)=f a.val :=
      ((hdesc _).mpr hzmem).trans (hA a.property).2.1.symm
    have heq := hiso (fun j => z j) hd hzmap
    ext j
    exact congrFun heq j
  have hh := sign_condition_isolated_points_card_le P hP accept xE
    (fun a b h => Subtype.ext (congrArg WithLp.ofLp h)) hx hi
  simpa only [Fintype.card_coe] using hh

/-- The sign-graph slice bound requires C1 only on the open regular domain. -/
theorem sign_graph_open_regular_slice_encard_le {n s D : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U)
    (P : Fin s → MvPolynomial (Fin n ⊕ Fin n) ℝ)
    (hP : ∀ j, (P j).totalDegree ≤ D) (accept : (Fin s → SignType) → Prop)
    (hgraph : ∀ x w, F x = w ↔ accept (fun j => SignType.sign (eval (Sum.elim w x) (P j))))
    (t : ℝ) (z : Fin n → ℝ) :
    Set.encard {x : Fin n → ℝ | x ∈ U ∧ F x+t • x=z ∧
      (fderiv ℝ (fun x => F x+t • x) x).det ≠ 0} ≤ (2^s*(4*D+1)^n : ℕ) := by
  apply sign_description_open_regular_fiber_encard_le (fun x => F x+t • x) U
    (fun x hx => ((hF x hx).contDiffAt (hU.mem_nhds hx)).add (contDiffAt_id.const_smul t))
    (fun j => sliceGraphPolynomial (P j) t z)
    (fun j => (sliceGraphPolynomial_degree _ _ _).trans (hP j)) accept z
  intro x
  simp_rw [sliceGraphPolynomial_eval]
  rw [← hgraph]
  exact eq_sub_iff_add_eq.symm

/-- Constructed sections have one uniform regular-slice multiplicity constant.
No section, C1 decomposition or multiplicity bound is an input. -/
theorem bounded_format_selected_regular_fibers (n s d : ℕ)
    (W : (Fin s → SignType) → Prop) :
    ∃ M : ℕ, ∀ P : Fin s → MvPolynomial (Fin n ⊕ Fin n) ℝ,
      (∀ j, (P j).totalDegree ≤ d) →
      ∃ F : (Fin n → ℝ) → (Fin n → ℝ), ∃ U : Set (Fin n → ℝ),
        (∀ x, (∃ y, W (fun j => SignType.sign (eval (Sum.elim x y) (P j)))) →
          W (fun j => SignType.sign (eval (Sum.elim x (F x)) (P j)))) ∧
        IsOpen U ∧ MeasureTheory.volume Uᶜ = 0 ∧ ContDiffOn ℝ 1 F U ∧
        ∀ t : ℝ, ∀ z : Fin n → ℝ,
          Set.encard {x : Fin n → ℝ | x ∈ U ∧ F x+t • x=z ∧
            (fderiv ℝ (fun x => F x+t • x) x).det ≠ 0} ≤ M := by
  obtain ⟨b,D,h⟩ := bounded_format_selection n n s d W
  refine ⟨2^b*(4*D+1)^n,?_⟩
  intro P hP
  obtain ⟨F,Q,accept,hF,hQ,hgraph,U,hU,hnull,hreg⟩ := h P hP
  refine ⟨F,U,hF,hU,hnull,hreg,?_⟩
  intro t z
  exact sign_graph_open_regular_slice_encard_le F U hU hreg Q hQ accept
    (fun x y => eq_comm.trans (hgraph x y)) t z

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sign_description_open_regular_fiber_encard_le

#print axioms KakeyaTwoScale.bounded_format_selected_regular_fibers
