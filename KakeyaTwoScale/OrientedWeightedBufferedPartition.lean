module
public import KakeyaTwoScale.WeightedBufferedPartition
public import KakeyaTwoScale.PolynomialOrientationAssignment

@[expose] public section

open Set MvPolynomial MeasureTheory Metric
open scoped BigOperators ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- Returning a selected canonical successor to physical coordinates preserves
its actual joint rank with the unchanged original constraints. -/
theorem orthogonal_successor_regular {b c : ℕ}
    (e : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (R : MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hR : ∀ y, rectangularPolynomialMap (fun i => polynomialLinearPullback
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap (P i)) y=0 → eval y R=0 →
      (fderiv ℝ (fun z => (rectangularPolynomialMap (fun i => polynomialLinearPullback
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap (P i)) z,eval z R)) y).range=⊤) :
    ∀ x, rectangularPolynomialMap P x=0 →
      eval x (polynomialLinearPullback e.toContinuousLinearEquiv.toContinuousLinearMap R)=0 →
      (fderiv ℝ (fun y => (rectangularPolynomialMap P y,
        eval y (polynomialLinearPullback e.toContinuousLinearEquiv.toContinuousLinearMap R))) x).range=⊤ := by
  let Pe := fun i => polynomialLinearPullback e.symm.toContinuousLinearEquiv.toContinuousLinearMap (P i)
  let F := fun y : EuclideanSpace ℝ (Fin b ⊕ Fin c) => (rectangularPolynomialMap Pe y,eval y R)
  have heq : (fun y : EuclideanSpace ℝ (Fin b ⊕ Fin c) => (rectangularPolynomialMap P y,
      eval y (polynomialLinearPullback e.toContinuousLinearEquiv.toContinuousLinearMap R)))=F ∘ e := by
    funext y
    simp [F,Pe,rectangularPolynomialMap_pullback,polynomialLinearPullback_eval]
  intro x hx hRx
  have hPe : rectangularPolynomialMap Pe (e x)=0 := by
    simpa [Pe,rectangularPolynomialMap_pullback] using hx
  have hRe : eval (e x) R=0 := by rwa [polynomialLinearPullback_eval] at hRx
  have hs := hR (e x) hPe hRe
  have hd : DifferentiableAt ℝ F (e x) :=
    ((rectangularPolynomialMap_contDiff Pe ∞).differentiable (by simp) _).prodMk
      ((finite_polynomial_eval_contDiff R ∞).differentiable (by simp) _)
  rw [heq,(hd.hasFDerivAt.comp x e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv]
  apply LinearMap.range_eq_top.mpr
  intro y
  obtain ⟨v,hv⟩ := LinearMap.range_eq_top.mp hs y
  exact ⟨e.symm v,by simpa [F,Pe] using hv⟩

/-- Complete physical-coordinate output of the weighted buffered split. -/
structure OrientedWeightedBufferedData {b c J s : ℕ} {C : Type}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (D : ℕ → ℕ)
    (S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (cubes : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (weight : C → ℝ) (η r : ℝ) where
  orientation : EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)
  orientation_mem : orientation ∈ S
  selected : Finset C
  selected_subset : selected ⊆ cubes
  selected_positive : 0 < ∑ u ∈ selected, weight u
  orientation_mass : (∑ u ∈ cubes, weight u) ≤ (S.card:ℝ)*∑ u ∈ selected, weight u
  q : Fin s → MvPolynomial (Fin b) ℝ
  threshold : ℝ
  threshold_mem : threshold ∈ Ioo ((3:ℝ)/4) ((7:ℝ)/8)
  factors_nonzero : ∀ i, q i ≠ 0
  factors_degree : (∑ i, (q i).totalDegree) ≤ b*(∑ j ∈ Finset.range s, D j)
  wall : Option (Fin s) → MvPolynomial (Fin b ⊕ Fin c) ℝ
  wall_eq : ∀ i, wall i = polynomialLinearPullback orientation.toContinuousLinearEquiv.toContinuousLinearMap
    (bufferedSuccessorPolynomial (fun j => polynomialLinearPullback
      orientation.symm.toContinuousLinearEquiv.toContinuousLinearMap (P j)) q threshold i)
  wall_degree : ∀ i, (wall i).totalDegree ≤ max (2*c*(J-1)) (b*(∑ j ∈ Finset.range s, D j))
  wall_regular : ∀ i x, rectangularPolynomialMap P x=0 → eval x (wall i)=0 →
    (fderiv ℝ (fun y => (rectangularPolynomialMap P y,eval y (wall i))) x).range=⊤
  alternative :
    (∃ (G : Finset C) (owner : C → (Fin s → Bool)), G ⊆ selected ∧
      (∑ u ∈ cubes, weight u) ≤ 2*(S.card:ℝ)*∑ u ∈ G, weight u ∧
      (∀ u ∈ G, Q u ⊆ (fun x => coordinateBaseProjection (orientation x)) ⁻¹'
        polynomialSignCell q (owner u)) ∧
      (∀ u ∈ G, ∀ x ∈ Q u,
        coordinateBaseProjection (orientation x) ∉ thickening r (polynomialFactorZeros q)) ∧
      (∀ sign : Fin s → Bool,
        (∑ u ∈ G.filter (fun u => owner u=sign), weight u) ≤
          2*((∑ u ∈ selected, weight u)/(2:ℝ)^s))) ∨
    (∃ (G : Finset C) (i : Option (Fin s)), G ⊆ selected ∧
      (∑ u ∈ cubes, weight u) ≤ 2*(S.card:ℝ)*(s+1:ℕ)*∑ u ∈ G, weight u ∧
      (∀ u ∈ G, Q u ⊆ thickening (η+2*(η+r))
        ({y | rectangularPolynomialMap P y=0} ∩ {y | eval y (wall i)=0})))

/-- Dimension-only orientations are selected first; all remaining geometry,
weights, polynomials, and scales are arbitrary. No orientation tag hypothesis
or relative partition oracle remains in the constructed output. -/
theorem exists_oriented_weighted_buffered_partition (b c : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)),
      ∀ {J s : ℕ} {C : Type}
        (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ),
        (∀ i, (P i).totalDegree ≤ J) →
        (∀ x, rectangularPolynomialMap P x=0 →
          (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) →
        ∀ (D : ℕ → ℕ), (∀ j < s, 2^j < (D j+1)^b) →
        ∀ (cubes : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (weight : C → ℝ),
        (∀ u ∈ cubes, MeasurableSet (Q u)) →
        (∀ u ∈ cubes, volume (Q u) ≠ ⊤) →
        (∀ u ∈ cubes, 0 < volume.real (Q u)) →
        (∀ u ∈ cubes, IsPreconnected (Q u)) →
        (∀ u ∈ cubes, 0 ≤ weight u) → (0 < ∑ u ∈ cubes, weight u) →
        ∀ (tag : C → EuclideanSpace ℝ (Fin b ⊕ Fin c)),
        (∀ u ∈ cubes, rectangularPolynomialMap P (tag u)=0) →
        ∀ (η r : ℝ), 0 < r →
        (∀ u ∈ cubes, ∀ x ∈ Q u, dist x (tag u) < η) →
        Nonempty (OrientedWeightedBufferedData (J := J) (s := s) P D S cubes Q weight η r) := by
  classical
  obtain ⟨S,hS⟩ := exists_finite_polynomial_orientation_assignment b c
  refine ⟨S,?_⟩
  intro J s C P hPdeg hP D hd cubes Q weight hQ hfinite hpositive hconnected hw hH tag htag η r hr hnear
  obtain ⟨orient,horient⟩ := hS P hP
  have hcubes : cubes.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hH
  obtain ⟨u₀,hu₀⟩ := hcubes
  let e₀ : S := ⟨orient ⟨tag u₀,htag u₀ hu₀⟩,(horient ⟨tag u₀,htag u₀ hu₀⟩).1⟩
  let : Nonempty S := ⟨e₀⟩
  let owner : C → S := fun u => if h : u ∈ cubes then
    ⟨orient ⟨tag u,htag u h⟩,(horient ⟨tag u,htag u h⟩).1⟩ else e₀
  obtain ⟨e,hmass⟩ := exists_heaviest_weighted_label cubes owner weight
  let B := cubes.filter (fun u => owner u=e)
  have hB : B ⊆ cubes := Finset.filter_subset _ _
  have hmass' : (∑ u ∈ cubes, weight u) ≤ (S.card:ℝ)*∑ u ∈ B, weight u := by
    simpa only [Fintype.card_coe] using hmass
  have hBpos : 0 < ∑ u ∈ B, weight u := by
    have hcard : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
    by_contra hh
    have hn := mul_nonpos_of_nonneg_of_nonpos hcard (le_of_not_gt hh)
    linarith
  let Pe := fun i => polynomialLinearPullback e.val.symm.toContinuousLinearEquiv.toContinuousLinearMap (P i)
  let Qe := fun u => e.val '' Q u
  let te := fun u => e.val (tag u)
  have hPeval (x : EuclideanSpace ℝ (Fin b ⊕ Fin c)) :
      rectangularPolynomialMap Pe (e.val x)=rectangularPolynomialMap P x := by
    simp [Pe,rectangularPolynomialMap_pullback]
  have hvol (u : C) (hu : u ∈ B) : volume (Qe u)=volume (Q u) := by
    have hh := e.val.symm.measurePreserving.measure_preimage (hQ u (hB hu)).nullMeasurableSet
    have hs : e.val.symm ⁻¹' Q u=e.val '' Q u := by
      ext x
      constructor
      · intro hx
        exact ⟨e.val.symm x,hx,e.val.apply_symm_apply x⟩
      · rintro ⟨y,hy,rfl⟩
        simpa using hy
    simpa only [Qe,hs] using hh
  have hQe : ∀ u ∈ B, MeasurableSet (Qe u) := fun u hu =>
    e.val.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hQ u (hB hu))
  have hratio : ∀ u ∈ B, (7:ℝ)/8 <
      (polynomialNormalJacobianAt Pe (te u)).det^2 / eval (te u) (polynomialNormalGram Pe) := by
    intro u hu
    obtain ⟨huc,hue⟩ := Finset.mem_filter.mp hu
    have ho : orient ⟨tag u,htag u huc⟩=e.val := by
      have hh := congrArg Subtype.val hue
      simpa only [owner,dite_eq_left huc] using hh
    have hh := (horient ⟨tag u,htag u huc⟩).2
    simpa only [ho] using hh
  obtain ⟨q,τ,hτ,hq,hdegree,hwallDegree,hwallRegular,hcases⟩ :=
    exists_weighted_buffered_partition Pe (fun i => (polynomialLinearPullback_degree _ _).trans (hPdeg i))
      (orthogonal_polynomial_pullback_regular e.val.symm P hP) s D hd B Qe weight
      hQe (fun u hu => by rw [hvol u hu]; exact hfinite u (hB hu))
      (fun u hu => by simpa only [Measure.real,hvol u hu] using hpositive u (hB hu))
      (fun u hu => (hconnected u (hB hu)).image e.val e.val.continuous.continuousOn)
      (fun u hu => hw u (hB hu)) hBpos te
      (fun u hu => (hPeval (tag u)).trans (htag u (hB hu))) hratio η r hr (by
        intro u hu x hx
        obtain ⟨y,hy,rfl⟩ := hx
        exact (e.val.dist_map y (tag u)).trans_lt (hnear u (hB hu) y hy))
  let R := fun i => polynomialLinearPullback e.val.toContinuousLinearEquiv.toContinuousLinearMap
    (bufferedSuccessorPolynomial Pe q τ i)
  refine ⟨⟨e.val,e.property,B,hB,hBpos,hmass',q,τ,hτ,hq,hdegree,R,(fun _ => rfl),
    fun i => (polynomialLinearPullback_degree _ _).trans (hwallDegree i),
    fun i => orthogonal_successor_regular e.val P _ (hwallRegular i),?_⟩⟩
  rcases hcases with ⟨G,cell,hGB,hgood,hcell,havoid,hcap⟩ | ⟨G,i,hGB,hbad,hcapture⟩
  · refine Or.inl ⟨G,cell,hGB,?_,?_,?_,hcap⟩
    · have hh := mul_le_mul_of_nonneg_left hgood (Nat.cast_nonneg S.card : (0:ℝ) ≤ S.card)
      nlinarith
    · intro u hu x hx
      exact hcell u hu ⟨x,hx,rfl⟩
    · intro u hu x hx
      exact havoid u hu (e.val x) ⟨x,hx,rfl⟩
  · refine Or.inr ⟨G,i,hGB,?_,?_⟩
    · have hh := mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg S.card : (0:ℝ) ≤ S.card)
      nlinarith
    · intro u hu x hx
      have hh := hcapture u hu ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hh
      apply mem_thickening_iff.mpr
      refine ⟨e.val.symm y,⟨?_,?_⟩,?_⟩
      · have he := hPeval (e.val.symm y)
        rw [e.val.apply_symm_apply] at he
        exact he.symm.trans hy.1
      · change eval (e.val.symm y) (polynomialLinearPullback
          e.val.toContinuousLinearEquiv.toContinuousLinearMap (bufferedSuccessorPolynomial Pe q τ i))=0
        rw [polynomialLinearPullback_eval]
        simpa using hy.2
      · have he := e.val.dist_map x (e.val.symm y)
        rw [e.val.apply_symm_apply] at he
        exact he ▸ hxy

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orthogonal_successor_regular
#print axioms KakeyaTwoScale.exists_oriented_weighted_buffered_partition
