module
public import KakeyaTwoScale.RelativeRegularPartition
public import KakeyaTwoScale.BufferedPolynomialGeometry
public import KakeyaTwoScale.WeightedEuclideanMarginal
public import KakeyaTwoScale.WeightedLabelSelection

@[expose] public section

open Set MvPolynomial MeasureTheory Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- A constructed weighted buffered partition in one Gauss orientation.
The output is a literal cellular/algebraic dichotomy on whole labelled sets.
All weights are the original weights: no trimmed-density premise is assumed. -/
theorem exists_weighted_buffered_partition {b c J : ℕ} {C : Type*}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hPdeg : ∀ i, (P i).totalDegree ≤ J)
    (hP : ∀ x, rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤)
    (s : ℕ) (D : ℕ → ℕ) (hd : ∀ j < s, 2^j < (D j+1)^b)
    (cubes : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (weight : C → ℝ)
    (hQ : ∀ u ∈ cubes, MeasurableSet (Q u))
    (hfinite : ∀ u ∈ cubes, volume (Q u) ≠ ⊤)
    (hpositive : ∀ u ∈ cubes, 0 < volume.real (Q u))
    (hconnected : ∀ u ∈ cubes, IsPreconnected (Q u))
    (hw : ∀ u ∈ cubes, 0 ≤ weight u) (hH : 0 < ∑ u ∈ cubes, weight u)
    (tag : C → EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (htag : ∀ u ∈ cubes, rectangularPolynomialMap P (tag u)=0)
    (hratio : ∀ u ∈ cubes, (7:ℝ)/8 <
      (polynomialNormalJacobianAt P (tag u)).det^2 / eval (tag u) (polynomialNormalGram P))
    (η r : ℝ) (hr : 0 < r)
    (hnear : ∀ u ∈ cubes, ∀ x ∈ Q u, dist x (tag u) < η) :
    ∃ (q : Fin s → MvPolynomial (Fin b) ℝ) (τ : ℝ),
      τ ∈ Ioo ((3:ℝ)/4) ((7:ℝ)/8) ∧
      (∀ i, q i ≠ 0) ∧
      (∑ i, (q i).totalDegree) ≤ b*(∑ j ∈ Finset.range s, D j) ∧
      (∀ i : Option (Fin s),
        (bufferedSuccessorPolynomial P q τ i).totalDegree ≤
          max (2*c*(J-1)) (b*(∑ j ∈ Finset.range s, D j))) ∧
      (∀ i x, rectangularPolynomialMap P x=0 →
        eval x (bufferedSuccessorPolynomial P q τ i)=0 →
        (fderiv ℝ (fun y => (rectangularPolynomialMap P y,
          eval y (bufferedSuccessorPolynomial P q τ i))) x).range=⊤) ∧
      ((∃ (G : Finset C) (owner : C → (Fin s → Bool)), G ⊆ cubes ∧
        (∑ u ∈ cubes, weight u) ≤ 2*∑ u ∈ G, weight u ∧
        (∀ u ∈ G, Q u ⊆ coordinateBaseProjection ⁻¹' polynomialSignCell q (owner u)) ∧
        (∀ u ∈ G, ∀ x ∈ Q u,
          coordinateBaseProjection x ∉ thickening r (polynomialFactorZeros q)) ∧
        (∀ sign : Fin s → Bool,
          (∑ u ∈ G.filter (fun u => owner u=sign), weight u) ≤
            2*((∑ u ∈ cubes, weight u)/(2:ℝ)^s))) ∨
      (∃ (G : Finset C) (i : Option (Fin s)), G ⊆ cubes ∧
        (∑ u ∈ cubes, weight u) ≤ 2*(s+1:ℕ)*∑ u ∈ G, weight u ∧
        (∀ u ∈ G, Q u ⊆ thickening (η+2*(η+r))
          ({y | rectangularPolynomialMap P y=0} ∩
            {y | eval y (bufferedSuccessorPolynomial P q τ i)=0})))) := by
  classical
  let w := weightedEuclideanMarginal cubes Q weight
  have hi := integrable_weightedEuclideanMarginal cubes Q weight hQ hfinite
  have htotal := integral_weightedEuclideanMarginal cubes Q weight hQ hfinite hpositive
  obtain ⟨q,hq,hdegree,hregular,hmass⟩ := exists_relative_regular_iterated_partition P hP s D hd
    w hi (by simpa only [w,htotal] using hH)
  obtain ⟨τ,hτ,hgdegree,hgregular,hgpositive⟩ := exists_regular_polynomialGaussBarrier P hPdeg hP
  refine ⟨q,τ,hτ,hq,hdegree,?_,?_,?_⟩
  · intro i
    cases i with
    | none => exact hgdegree.trans (le_max_left _ _)
    | some i =>
      apply (totalDegree_rename_le _ _).trans
      exact (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans
        (hdegree.trans (le_max_right _ _))
  · intro i
    cases i with
    | none => exact hgregular
    | some i => simpa only [bufferedSuccessorPolynomial,sumCylindricalPolynomial_eval] using hregular i
  let bad : C → Prop := fun u => ∃ x ∈ Q u,
    coordinateBaseProjection x ∈ thickening r (polynomialFactorZeros q)
  let G := cubes.filter (fun u => ¬ bad u)
  have hG : G ⊆ cubes := Finset.filter_subset _ _
  have havoid : ∀ u ∈ G, ∀ x ∈ Q u,
      coordinateBaseProjection x ∉ thickening r (polynomialFactorZeros q) := by
    intro u hu x hx hc
    exact (Finset.mem_filter.mp hu).2 ⟨x,hx,hc⟩
  have hcell : ∀ u : C, ∃ sign : Fin s → Bool, u ∈ G →
      Q u ⊆ coordinateBaseProjection ⁻¹' polynomialSignCell q sign := by
    intro u
    by_cases hu : u ∈ G
    · obtain ⟨sign,hsign⟩ := preconnected_polynomial_cell_of_avoids_buffer (Q u)
        (hconnected u (hG hu)) coordinateBaseProjection coordinateBaseProjection.continuous
        q r hr (havoid u hu)
      exact ⟨sign,fun _ => hsign⟩
    · exact ⟨fun _ => false,fun h => (hu h).elim⟩
  choose owner howner using hcell
  have hcap (sign : Fin s → Bool) :
      (∑ u ∈ G.filter (fun u => owner u=sign), weight u) ≤
        2*((∑ u ∈ cubes, weight u)/(2:ℝ)^s) := by
    have hm := wholeSetWeight_le_marginal_setIntegral cubes (G.filter (fun u => owner u=sign))
      Q weight ((Finset.filter_subset _ _).trans hG) hQ hfinite hpositive hw
      (polynomialSignCell q sign) (isOpen_polynomialSignCell q sign).measurableSet (by
        intro u hu
        obtain ⟨hu,he⟩ := Finset.mem_filter.mp hu
        simpa only [← he] using howner u hu)
    exact hm.trans (by simpa only [w,htotal] using (hmass sign).2.le)
  by_cases hhalf : (∑ u ∈ cubes, weight u) ≤ 2*∑ u ∈ G, weight u
  · exact Or.inl ⟨G,owner,hG,hhalf,howner,havoid,hcap⟩
  · let B := cubes \ G
    have hsum : (∑ u ∈ G, weight u)+(∑ u ∈ B, weight u) = ∑ u ∈ cubes, weight u := by
      rw [add_comm]
      exact Finset.sum_sdiff hG
    have hBhalf : (∑ u ∈ cubes, weight u) ≤ 2*∑ u ∈ B, weight u := by linarith
    have hcapture : ∀ u : C, ∃ i : Option (Fin s), u ∈ B → Q u ⊆ thickening (η+2*(η+r))
        ({y | rectangularPolynomialMap P y=0} ∩ {y | eval y (bufferedSuccessorPolynomial P q τ i)=0}) := by
      intro u
      by_cases hu : u ∈ B
      · have hc := (Finset.mem_sdiff.mp hu).1
        have hb : bad u := by
          by_contra hb
          exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_filter.mpr ⟨hc,hb⟩)
        obtain ⟨i,hi⟩ := buffered_polynomial_wall_capture P q τ hτ.1.le (Q u) (tag u) η r
          (htag u hc) (hgpositive _ (htag u hc) (hratio u hc)).le (hnear u hc) hb
        exact ⟨i,fun _ => hi⟩
      · exact ⟨none,fun h => (hu h).elim⟩
    choose label hlabel using hcapture
    obtain ⟨i,hi⟩ := exists_heaviest_weighted_label B label weight
    have hi' : (∑ u ∈ B, weight u) ≤ (s+1:ℕ)*∑ u ∈ B.filter (fun u => label u=i), weight u := by
      simpa only [Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hi
    refine Or.inr ⟨B.filter (fun u => label u=i),i,
      (Finset.filter_subset _ _).trans Finset.sdiff_subset,by nlinarith,?_⟩
    intro u hu
    obtain ⟨hu,he⟩ := Finset.mem_filter.mp hu
    simpa only [← he] using hlabel u hu

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_weighted_buffered_partition
