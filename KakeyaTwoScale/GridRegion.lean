module
public import KakeyaTwoScale.MeasurableCellPruning
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem measurable_gridIndex {n : ℕ} (r : ℝ) : Measurable (gridIndex (n:=n) r) := by
  unfold gridIndex
  apply Measurable.of_eval
  intro i
  have hd : Measurable (fun x : Fin n → ℝ => x i / r) :=
    (measurable_pi_apply i).div measurable_const
  exact Int.measurable_floor.comp hd

def occupiedGridRegion {n : ℕ} {J : Type*} (family : Finset J)
    (b v : J → (Fin n → ℝ)) (r : ℝ) (I : J → Set ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  ⋃ j ∈ family, {z | z.1 ∈ I j ∧ gridIndex r z.2 = gridIndex r (segmentPoint (b j) (v j) z.1)}

theorem measurableSet_occupiedGridRegion {n : ℕ} {J : Type*} (family : Finset J)
    (b v : J → (Fin n → ℝ)) (r : ℝ) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j)) :
    MeasurableSet (occupiedGridRegion family b v r I) := by
  apply Finset.measurableSet_biUnion
  intro j hj
  have he : {z : ℝ × (Fin n → ℝ) | z.1 ∈ I j ∧
      gridIndex r z.2 = gridIndex r (segmentPoint (b j) (v j) z.1)} =
      (Prod.fst ⁻¹' I j) ∩ {z | gridIndex r z.2 = gridIndex r (segmentPoint (b j) (v j) z.1)} := rfl
  rw [he]
  exact ((hm j hj).preimage measurable_fst).inter
    (measurableSet_eq_fun ((measurable_gridIndex r).comp measurable_snd)
      ((measurable_gridIndex r).comp
        (continuous_const.add (continuous_fst.smul continuous_const)).measurable))

theorem occupiedGridRegion_section {n : ℕ} {J : Type*} (family : Finset J)
    (b v : J → (Fin n → ℝ)) {r : ℝ} (hr : 0 < r) (I : J → Set ℝ) (t : ℝ) :
    (fun x => (t,x)) ⁻¹' occupiedGridRegion family b v r I =
      ⋃ k ∈ (family.filter (fun j => t ∈ I j)).image
        (fun j => gridIndex r (segmentPoint (b j) (v j) t)), gridCell r k := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj,ht,hx⟩ := Set.mem_iUnion₂.mp hx
    apply Set.mem_iUnion₂.mpr
    refine ⟨gridIndex r (segmentPoint (b j) (v j) t), ?_, (mem_gridCell_iff hr x _).mpr hx⟩
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,ht⟩,rfl⟩
  · intro hx
    obtain ⟨k,hk,hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hj,ht⟩ := Finset.mem_filter.mp hj
    exact Set.mem_iUnion₂.mpr ⟨j,hj,ht,(mem_gridCell_iff hr x _).mp hx⟩

/-- Every finite-family occupied region has finite product volume over a finite
height measure. This supplies integrability rather than assuming it. -/
theorem occupiedGridRegion_volume_ne_top {n : ℕ} {J : Type*}
    (μ : Measure ℝ) [IsFiniteMeasure μ] (family : Finset J)
    (b v : J → (Fin n → ℝ)) {r : ℝ} (hr : 0 < r) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j)) :
    (μ.prod volume) (occupiedGridRegion family b v r I) ≠ ⊤ := by
  have hmeas := measurableSet_occupiedGridRegion family b v r I hm
  apply ne_of_lt
  rw [Measure.prod_apply hmeas]
  calc
    _ ≤ ∫⁻ _t : ℝ, (family.card : ℝ≥0∞) * ENNReal.ofReal r^n ∂μ := by
      apply lintegral_mono
      intro t
      change volume ((fun x => (t,x)) ⁻¹' occupiedGridRegion family b v r I) ≤ _
      rw [occupiedGridRegion_section family b v hr I t, volume_gridCell_union hr]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le family _))
    _ < ⊤ := by rw [lintegral_const]; finiteness

/-- Fubini for the actual occupied grid union, with finiteness already derived. -/
theorem occupiedGridRegion_section_integral {n : ℕ} {J : Type*}
    (μ : Measure ℝ) [IsFiniteMeasure μ] (family : Finset J)
    (b v : J → (Fin n → ℝ)) {r : ℝ} (hr : 0 < r) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j)) :
    (∫ t, volume.real ((fun x => (t,x)) ⁻¹' occupiedGridRegion family b v r I) ∂μ) =
      (μ.prod volume).real (occupiedGridRegion family b v r I) := by
  have hs := measurableSet_occupiedGridRegion family b v r I hm
  have hf := occupiedGridRegion_volume_ne_top μ family b v hr I hm
  rw [Measure.real, Measure.prod_apply hs]
  exact integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
    (Measure.ae_measure_lt_top hs hf)

/-- Integrate the constructed low-cell deletion bound over genuine horizontal
unions. All discarded-mass and section-volume integrability is proved. -/
theorem safe_low_portion_mass {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, t ∈ Set.Icc (0:ℝ) 1)
    (b v : Child → (Fin n → ℝ)) (bP vP : P → (Fin n → ℝ))
    {r : ℝ} (hr : 0 < r) (hscale : F.coarseCellVolume = r^n)
    (M : ℝ) (D : Child → Set ℝ) (hm : ∀ x ∈ F.children, MeasurableSet (D x))
    (hb : ∀ x ∈ F.children, bP (F.assign x) = gridRound r (b x))
    (hv : ∀ x ∈ F.children, vP (F.assign x) = gridRound r (v x))
    (hlow : ∀ x ∈ F.children, ∀ t ∈ D x, F.weight*(safeCellParents F.parents bP vP r
      (gridIndex r (segmentPoint (b x) (v x) t)) t).card ≤ M) :
    F.portionMass μ D ≤ 2*M*(μ.prod volume).real (occupiedGridRegion F.children b v r D) := by
  let E := occupiedGridRegion F.children b v r D
  have hE := measurableSet_occupiedGridRegion F.children b v r D hm
  have hf := occupiedGridRegion_volume_ne_top μ F.children b v hr D hm
  have hi := Measure.integrable_measure_prodMk_left hE hf
  rw [F.portionMass_eq_integral μ D hm, ← occupiedGridRegion_section_integral μ F.children b v hr D hm]
  calc
    _ ≤ ∫ t, 2*M*volume.real ((fun x => (t,x)) ⁻¹' E) ∂μ := by
      apply integral_mono_ae ((integrable_card_filter μ F.children D hm).const_mul _)
        (hi.const_mul _)
      filter_upwards [hμ] with t ht
      rw [occupiedGridRegion_section F.children b v hr D t]
      apply safe_low_children_volume F b v bP vP hr hscale M t ht hb hv
        (F.activeChildren D t) (Finset.filter_subset _ _)
      intro x hx
      obtain ⟨hx,ht⟩ := Finset.mem_filter.mp hx
      exact hlow x hx t ht
    _ = _ := integral_const_mul _ _
/-- The source-facing low-cell deletion estimate uses full Lebesgue volume.
Restricting the height measure to [0,1] is discharged, not an extra convention. -/
theorem safe_low_portion_mass_volume {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (b v : Child → (Fin n → ℝ)) (bP vP : P → (Fin n → ℝ))
    {r : ℝ} (hr : 0 < r) (hscale : F.coarseCellVolume = r^n)
    (M : ℝ) (D : Child → Set ℝ) (hm : ∀ x ∈ F.children, MeasurableSet (D x))
    (hunit : ∀ x ∈ F.children, D x ⊆ Set.Icc (0:ℝ) 1)
    (hb : ∀ x ∈ F.children, bP (F.assign x) = gridRound r (b x))
    (hv : ∀ x ∈ F.children, vP (F.assign x) = gridRound r (v x))
    (hlow : ∀ x ∈ F.children, ∀ t ∈ D x, F.weight*(safeCellParents F.parents bP vP r
      (gridIndex r (segmentPoint (b x) (v x) t)) t).card ≤ M) :
    F.portionMass volume D ≤ 2*M*volume.real (occupiedGridRegion F.children b v r D) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  have hmass : F.portionMass μ D = F.portionMass volume D := by
    unfold FixedParents.portionMass
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [Measure.real, Measure.restrict_apply (hm x hx), Set.inter_eq_left.mpr (hunit x hx)]
    rfl
  have hsub : occupiedGridRegion F.children b v r D ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.univ := by
    intro z hz
    obtain ⟨x,hx,ht,_⟩ := Set.mem_iUnion₂.mp hz
    exact ⟨hunit x hx ht,Set.mem_univ _⟩
  have hvol : (μ.prod volume).real (occupiedGridRegion F.children b v r D) =
      volume.real (occupiedGridRegion F.children b v r D) := by
    rw [Measure.real, Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_apply (measurableSet_occupiedGridRegion F.children b v r D hm),
      Set.inter_eq_left.mpr hsub, ← Measure.volume_eq_prod]
    rfl
  have hh := safe_low_portion_mass F μ (ae_restrict_mem measurableSet_Icc)
    b v bP vP hr hscale M D hm hb hv hlow
  rwa [hmass, hvol] at hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurableSet_occupiedGridRegion
#print axioms KakeyaTwoScale.occupiedGridRegion_volume_ne_top
#print axioms KakeyaTwoScale.safe_low_portion_mass

#print axioms KakeyaTwoScale.safe_low_portion_mass_volume
