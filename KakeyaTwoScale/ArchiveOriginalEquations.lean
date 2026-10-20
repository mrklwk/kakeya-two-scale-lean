module
public import KakeyaTwoScale.ActualPrefixCaptureSweep
public import KakeyaTwoScale.NestedCaptureVolumeBound

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale
namespace PolynomialArchiveSnapshot

/-- Transport the original equations into the common ambient coordinates.
The rank assertion is on these equations, never on zero padding. -/
theorem exists_original_capture_equations {k : ℕ} {T C O : Type}
    (S : PolynomialArchiveSnapshot k T C O) (n e D : ℕ)
    (hd : S.dimension=n) (he : S.codimension≤e) (g : S.state.Grain)
    (hdeg : ∀ j, (S.equations g j).totalDegree≤D)
    (hreg : ∀ x, rectangularPolynomialMap (S.equations g) x=0 →
      (fderiv ℝ (rectangularPolynomialMap (S.equations g)) x).range=⊤) :
    ∃ Q : Fin S.codimension→MvPolynomial (Fin n) ℝ,
      (∀ j, (Q j).totalDegree≤D) ∧
      (∀ x, rectangularPolynomialMap Q x=0 → (fderiv ℝ (rectangularPolynomialMap Q) x).range=⊤) ∧
      {x : EuclideanSpace ℝ (Fin n) | ∀ j, eval x.ofLp (S.captureEquations n e hd g j)=0}=
        {x | rectangularPolynomialMap Q x=0} := by
  subst n
  refine ⟨S.equations g,hdeg,hreg,?_⟩
  ext x
  exact S.captureEquations_zero S.dimension e rfl he g x

end PolynomialArchiveSnapshot
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Actual positive-prefix equations admit an unpadded regular representation.
Both polynomial degree and regularity are discharged from the immutable archive. -/
theorem prefix_exists_original_equations
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n+1) (depth : Fin H.polynomialSnapshots.length)
    (y : T) (hy : y∈(H.polynomialSnapshots[depth]).state.tuples)
    (J0 : ℕ) (hJ : J≤J0) (hs : s=b*t)
    (hseq : ∀ j∈Finset.range s, I.D j=partitionBoxDegree b j) :
    ∃ Q : ∀ i : Fin depth.val, Fin (c+(i.val+1))→MvPolynomial (Fin (n+1)) ℝ,
      ∀ i, (∀ j, (Q i j).totalDegree≤archiveDegreeCalendar (n+1) t J0 fuel) ∧
      (∀ x, rectangularPolynomialMap (Q i) x=0 →
        (fderiv ℝ (rectangularPolynomialMap (Q i)) x).range=⊤) ∧
      captureZeroSet (H.prefixCaptureEquations n (n+1+fuel) hn depth y i)=
        {x | rectangularPolynomialMap (Q i) x=0} := by
  classical
  have hex (i : Fin depth.val) :
      ∃ Q : Fin (c+(i.val+1))→MvPolynomial (Fin (n+1)) ℝ,
        (∀ j, (Q j).totalDegree≤archiveDegreeCalendar (n+1) t J0 fuel) ∧
        (∀ x, rectangularPolynomialMap Q x=0 →
          (fderiv ℝ (rectangularPolynomialMap Q) x).range=⊤) ∧
        captureZeroSet (H.prefixCaptureEquations n (n+1+fuel) hn depth y i)=
          {x | rectangularPolynomialMap Q x=0} := by
    let S := H.polynomialSnapshots[H.positivePrefixIndex depth i]
    have hS : S∈H.polynomialSnapshots := List.getElem_mem (H.positivePrefixIndex depth i).isLt
    have hg : S.state.grain (I.cube y)∈S.state.grains I.cube :=
      Finset.mem_image.mpr ⟨y,H.prefix_tuple_mem depth y hy i,rfl⟩
    have hdim := (H.polynomialSnapshots_dimension S hS).trans hn
    have he : S.codimension≤n+1+fuel := by
      have hh := H.polynomialSnapshots_codimension_le S hS
      omega
    have hcal := H.polynomialSnapshots_calendar (n+1) J0 (max I.K 0)
      (le_max_right _ _) 0 hn hs hseq hJ (le_max_left _ _) S hS
    have hdeg : ∀ j, (S.equations (S.state.grain (I.cube y)) j).totalDegree≤
        archiveDegreeCalendar (n+1) t J0 fuel := by
      intro j
      exact ((H.polynomialSnapshots_sound S hS).1 _ hg j).trans
        (by simpa only [Nat.zero_add] using hcal.1)
    have hh := S.exists_original_capture_equations (n+1) (n+1+fuel)
      (archiveDegreeCalendar (n+1) t J0 fuel) hdim he _ hdeg
      ((H.polynomialSnapshots_sound S hS).2.1 _ hg)
    have hcod : S.codimension=c+(i.val+1) := H.positivePrefix_codimension depth i
    rw [← hcod]
    exact hh
  choose Q hQ using hex
  exact ⟨Q,hQ⟩

/-- Root-codimension-zero specialization without any rank assertion on padding. -/
theorem prefix_exists_root_equations
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n+1) (hc : c=0) (depth : Fin H.polynomialSnapshots.length)
    (y : T) (hy : y∈(H.polynomialSnapshots[depth]).state.tuples)
    (J0 : ℕ) (hJ : J≤J0) (hs : s=b*t)
    (hseq : ∀ j∈Finset.range s, I.D j=partitionBoxDegree b j) :
    ∃ Q : ∀ i : Fin depth.val, Fin (i.val+1)→MvPolynomial (Fin (n+1)) ℝ,
      ∀ i, (∀ j, (Q i j).totalDegree≤archiveDegreeCalendar (n+1) t J0 fuel) ∧
      (∀ x, rectangularPolynomialMap (Q i) x=0 →
        (fderiv ℝ (rectangularPolynomialMap (Q i)) x).range=⊤) ∧
      captureZeroSet (H.prefixCaptureEquations n (n+1+fuel) hn depth y i)=
        {x | rectangularPolynomialMap (Q i) x=0} := by
  classical
  have hex (i : Fin depth.val) :
      ∃ Q : Fin (i.val+1)→MvPolynomial (Fin (n+1)) ℝ,
        (∀ j, (Q j).totalDegree≤archiveDegreeCalendar (n+1) t J0 fuel) ∧
        (∀ x, rectangularPolynomialMap Q x=0 →
          (fderiv ℝ (rectangularPolynomialMap Q) x).range=⊤) ∧
        captureZeroSet (H.prefixCaptureEquations n (n+1+fuel) hn depth y i)=
          {x | rectangularPolynomialMap Q x=0} := by
    let S := H.polynomialSnapshots[H.positivePrefixIndex depth i]
    have hS : S∈H.polynomialSnapshots := List.getElem_mem (H.positivePrefixIndex depth i).isLt
    have hg : S.state.grain (I.cube y)∈S.state.grains I.cube :=
      Finset.mem_image.mpr ⟨y,H.prefix_tuple_mem depth y hy i,rfl⟩
    have hdim := (H.polynomialSnapshots_dimension S hS).trans hn
    have he : S.codimension≤n+1+fuel := by
      have hh := H.polynomialSnapshots_codimension_le S hS
      omega
    have hcal := H.polynomialSnapshots_calendar (n+1) J0 (max I.K 0)
      (le_max_right _ _) 0 hn hs hseq hJ (le_max_left _ _) S hS
    have hdeg : ∀ j, (S.equations (S.state.grain (I.cube y)) j).totalDegree≤
        archiveDegreeCalendar (n+1) t J0 fuel := by
      intro j
      exact ((H.polynomialSnapshots_sound S hS).1 _ hg j).trans
        (by simpa only [Nat.zero_add] using hcal.1)
    have hh := S.exists_original_capture_equations (n+1) (n+1+fuel)
      (archiveDegreeCalendar (n+1) t J0 fuel) hdim he _ hdeg
      ((H.polynomialSnapshots_sound S hS).2.1 _ hg)
    have hcod : S.codimension=i.val+1 := by
      simpa only [hc,Nat.zero_add] using H.positivePrefix_codimension depth i
    rw [← hcod]
    exact hh
  choose Q hQ using hex
  exact ⟨Q,hQ⟩

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.PolynomialArchiveSnapshot.exists_original_capture_equations
#print axioms KakeyaTwoScale.ActualBufferedArchive.prefix_exists_original_equations

#print axioms KakeyaTwoScale.ActualBufferedArchive.prefix_exists_root_equations
