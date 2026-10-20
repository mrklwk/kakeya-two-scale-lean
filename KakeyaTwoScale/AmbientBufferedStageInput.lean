module
public import KakeyaTwoScale.BufferedStageInput
public import KakeyaTwoScale.FrozenSuccessorTags
public import KakeyaTwoScale.PolynomialCoordinateRename
public import KakeyaTwoScale.NumericBufferedDepth

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Raw ambient data for a repeated dimension stage. In particular, neither
tags nor a local partition nor an output state is a field. -/
structure AmbientBufferedStageData (b c k A B Lh J s : ℕ) (T C O : Type)
    [DecidableEq T] [DecidableEq C] where
  W : FrozenGeometryState (b+c) k T C O
  Y₀ : Finset T
  cube : T→C
  tube : T→Fin k→O
  cubes : Finset C
  Q : C→Set (EuclideanSpace ℝ (Fin (b+c)))
  P : W.Grain→Fin c→MvPolynomial (Fin (b+c)) ℝ
  D : ℕ→ℕ
  alpha : ℝ
  δ : ℝ
  K : ℝ
  center : C→EuclideanSpace ℝ (Fin (b+c))
  dimension_pos : 0 < b
  families_pos : 0 < k
  exponent_pos : 0 < alpha
  exponent_le_one : alpha ≤ 1
  width_pos : 0 < δ
  capture_nonneg : 0 ≤ K
  valid : W.Valid Y₀ cube tube Q δ
  balanced : W.Balanced cube cubes alpha
  nonempty : W.tuples.Nonempty
  support : ∀ y ∈ Y₀, cube y ∈ cubes
  cardinal_bound : (Y₀.card:ℝ) ≤ (2:ℝ)^B
  height_bound : ∀ j, W.height j ≤ Lh
  degree : ∀ g ∈ W.grains cube, ∀ i, (P g i).totalDegree ≤ J
  regular : ∀ g ∈ W.grains cube, ∀ x, rectangularPolynomialMap (P g) x=0 →
    (fderiv ℝ (rectangularPolynomialMap (P g)) x).range=⊤
  capture : ∀ y ∈ W.tuples, ∀ j, W.geometry δ j (W.parent y j) ⊆
    thickening (K*δ) {x | rectangularPolynomialMap (P (W.grain (cube y))) x=0}
  partition_dimension : ∀ j < s, 2^j < (D j+1)^b
  partition_size : 2 ≤ s
  «measurable» : ∀ q ∈ cubes, MeasurableSet (Q q)
  finite_volume : ∀ q ∈ cubes, volume (Q q)≠⊤
  positive_volume : ∀ q ∈ cubes, 0 < volume.real (Q q)
  preconnected : ∀ q ∈ cubes, IsPreconnected (Q q)
  cube_radius : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*δ

namespace AmbientBufferedStageData
variable {b c k A B Lh J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

theorem physical_inverse_image (Q : Set (EuclideanSpace ℝ (Fin (b+c)))) :
    physicalCoordinateCube ((euclideanCoordinateRename (finSumFinEquiv : Fin b ⊕ Fin c ≃ Fin (b+c))).symm '' Q)=Q := by
  simp only [physicalCoordinateCube,Set.image_image]
  simp

/-- Construct the next buffered input, including genuine zero-set tags and
volume-preserving coordinate transport. -/
def toInput (I : AmbientBufferedStageData b c k A B Lh J s T C O) :
    BufferedStageInput b c k A B Lh J s (B/(s-1)+1) T C O := by
  classical
  let E := euclideanCoordinateRename (finSumFinEquiv : Fin b ⊕ Fin c ≃ Fin (b+c))
  let Q' := fun q=>E.symm '' I.Q q
  let P' := fun g i=>MvPolynomial.rename finSumFinEquiv.symm (I.P g i)
  have hQ (q) : physicalCoordinateCube (Q' q)=I.Q q := physical_inverse_image _
  have heval (g) (x : EuclideanSpace ℝ (Fin (b+c))) :
      rectangularPolynomialMap (P' g) (E.symm x)=rectangularPolynomialMap (I.P g) x :=
    by
      have he : E.symm x=euclideanCoordinateRename finSumFinEquiv.symm x := by
        apply E.injective
        rw [E.apply_symm_apply]
        apply PiLp.ext
        intro i
        simp [E]
      rw [he]
      exact rectangularPolynomialMap_rename finSumFinEquiv.symm (I.P g) x
  have hvol (q) (hq : q ∈ I.cubes) : volume (Q' q)=volume (I.Q q) := by
    have h := E.measurePreserving.measure_preimage (I.measurable q hq).nullMeasurableSet
    have hs : E ⁻¹' I.Q q=Q' q := by
      ext x
      constructor
      · intro hx; exact ⟨E x,hx,E.symm_apply_apply x⟩
      · rintro ⟨y,hy,rfl⟩; simpa using hy
    rwa [hs] at h
  have hdiam : ∀ q ∈ I.W.tuples.image I.cube, ∀ x ∈ I.Q q, dist x (I.center q) ≤ (A:ℝ)*I.δ := by
    intro q hq x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    exact I.cube_radius _ (I.support y (I.valid.1 hy)) x hx
  have htags := I.W.exists_successor_tags I.Y₀ I.cube I.tube I.Q
    I.δ A I.K I.families_pos I.valid
    (fun g=>{x | rectangularPolynomialMap (I.P g) x=0}) I.capture I.center (by simpa only [Finset.mem_image] using hdiam)
  let tag := Classical.choose htags
  have htag := (Classical.choose_spec htags).1
  have hnear := (Classical.choose_spec htags).2
  refine {
    W := I.W, Y₀ := I.Y₀, cube := I.cube, tube := I.tube, cubes := I.cubes,
    Q := Q', P := P', D := I.D, alpha := I.alpha, δ := I.δ,
    η := (2*A+I.K)*I.δ, r := 3*I.δ, R := 3*(2*A+I.K)+6,
    tag := fun q=>E.symm (tag q), center := I.center,
    dimension_pos := I.dimension_pos, families_pos := I.families_pos,
    exponent_pos := I.exponent_pos, exponent_le_one := I.exponent_le_one,
    width_pos := I.width_pos, buffer_gap := by linarith [I.width_pos],
    capture_budget := le_of_eq (by ring),
    radius_nonneg := mul_nonneg (by nlinarith [I.capture_nonneg, Nat.cast_nonneg (α:=ℝ) A]) I.width_pos.le,
    valid := by simpa only [hQ] using I.valid,
    balanced := I.balanced, nonempty := I.nonempty, support := I.support,
    cardinal_bound := I.cardinal_bound, height_bound := I.height_bound,
    degree := ?_, regular := ?_, partition_dimension := I.partition_dimension,
    partition_size := I.partition_size, «measurable» := ?_, finite_volume := ?_,
    positive_volume := ?_, preconnected := ?_, tag_zero := ?_, tag_near := ?_,
    stopping_depth := ?_, cube_radius := ?_ }
  · intro g hg i
    change (MvPolynomial.rename finSumFinEquiv.symm (I.P g i)).totalDegree ≤ J
    rw [polynomialCoordinateRename_degree]
    exact I.degree g hg i
  · intro g hg
    exact polynomialCoordinateRename_regular finSumFinEquiv.symm (I.P g) (I.regular g hg)
  · intro q hq
    exact E.symm.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (I.measurable q hq)
  · intro q hq
    rw [hvol q hq]
    exact I.finite_volume q hq
  · intro q hq
    change 0 < (volume (Q' q)).toReal
    rw [hvol q hq]
    exact I.positive_volume q hq
  · intro q hq
    exact (I.preconnected q hq).image E.symm E.symm.continuous.continuousOn
  · intro y hy
    rw [heval]
    apply htag
    simp only [Finset.mem_image]
    exact ⟨y,hy,rfl⟩
  · intro q hq x hx
    obtain ⟨y,hy,rfl⟩ := hx
    rw [E.symm.dist_map]
    apply hnear q ?_ y hy
    simpa only [Finset.mem_image] using hq
  · intro g _
    apply buffered_log_depth_sharp B s _ I.partition_size (by unfold tupleCubeMass; positivity)
    have hc : ((I.W.grainTuples I.cube g).card:ℝ) ≤ I.Y₀.card := by
      exact_mod_cast Finset.card_le_card ((I.W.grainTuples_subset I.cube g).trans I.valid.1)
    exact (tuple_mass_le_card _ _ _ I.exponent_pos I.exponent_le_one).trans (hc.trans I.cardinal_bound)
  · intro q hq x hx
    rw [hQ q] at hx
    exact I.cube_radius q hq x hx

@[simp] theorem toInput_W (I : AmbientBufferedStageData b c k A B Lh J s T C O) :
    I.toInput.W=I.W := rfl

@[simp] theorem toInput_physicalCube (I : AmbientBufferedStageData b c k A B Lh J s T C O) (q : C) :
    physicalCoordinateCube (I.toInput.Q q)=I.Q q := physical_inverse_image _

@[simp] theorem toInput_polynomial (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    (g : I.W.Grain) (i : Fin c) :
    I.toInput.P g i=MvPolynomial.rename finSumFinEquiv.symm (I.P g i) := rfl

@[simp] theorem toInput_back_polynomial
    (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    (g : I.W.Grain) (i : Fin c) :
    MvPolynomial.rename finSumFinEquiv (I.toInput.P g i)=I.P g i := by
  rw [toInput_polynomial,MvPolynomial.rename_rename]
  simp

end AmbientBufferedStageData
end KakeyaTwoScale
#print axioms KakeyaTwoScale.AmbientBufferedStageData.toInput
#print axioms KakeyaTwoScale.AmbientBufferedStageData.toInput_physicalCube

#print axioms KakeyaTwoScale.AmbientBufferedStageData.toInput_back_polynomial
