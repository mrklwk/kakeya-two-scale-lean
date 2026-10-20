module
public import KakeyaTwoScale.ParallelVolume

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Restricting the height measure does not change the volume of portions
whose heights lie in the unit interval. -/
theorem occupiedGridRegion_restrict_volume {n : ℕ} {J : Type*}
    (family : Finset J) (b v : J → Fin n → ℝ) (r : ℝ) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j))
    (hs : ∀ j ∈ family, I j ⊆ Set.Icc (0:ℝ) 1) :
    ((volume.restrict (Set.Icc (0:ℝ) 1)).prod volume) (occupiedGridRegion family b v r I) =
      volume (occupiedGridRegion family b v r I) := by
  have hsub : occupiedGridRegion family b v r I ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.univ := by
    intro z hz
    obtain ⟨j,hj,ht,_⟩ := Set.mem_iUnion₂.mp hz
    exact ⟨hs j hj ht,Set.mem_univ _⟩
  rw [Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply (measurableSet_occupiedGridRegion family b v r I hm),
    Set.inter_eq_left.mpr hsub,← Measure.volume_eq_prod]

theorem occupiedGridRegion_finite_volume {n : ℕ} {J : Type*}
    (family : Finset J) (b v : J → Fin n → ℝ) {r : ℝ} (hr : 0 < r) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j))
    (hs : ∀ j ∈ family, I j ⊆ Set.Icc (0:ℝ) 1) :
    volume (occupiedGridRegion family b v r I) ≠ ⊤ := by
  rw [← occupiedGridRegion_restrict_volume family b v r I hm hs]
  exact occupiedGridRegion_volume_ne_top _ family b v hr I hm

/-- A positive-length member yields strictly positive genuine union volume. -/
theorem occupiedGridRegion_positive_volume {n : ℕ} {J : Type*}
    (family : Finset J) (b v : J → Fin n → ℝ) {r : ℝ} (hr : 0 < r) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j))
    (hs : ∀ j ∈ family, I j ⊆ Set.Icc (0:ℝ) 1)
    (j : J) (hj : j ∈ family) (hI : 0 < volume.real (I j)) :
    0 < volume.real (occupiedGridRegion family b v r I) := by
  have hf := occupiedGridRegion_finite_volume family b v hr I hm hs
  have hsub : gridPortion (b j) (v j) r (I j) ⊆ occupiedGridRegion family b v r I := by
    intro x hx; exact Set.mem_iUnion₂.mpr ⟨j,hj,hx⟩
  have hle := measureReal_mono hsub hf
  have hvol : volume.real (gridPortion (b j) (v j) r (I j)) = r^n*volume.real (I j) := by
    rw [Measure.real,Measure.volume_eq_prod,volume_gridPortion volume _ _ hr _ (hm j hj)]
    simp [ENNReal.toReal_mul,ENNReal.toReal_pow,hr.le,Measure.real]
  rw [hvol] at hle
  exact (mul_pos (pow_pos hr n) hI).trans_le hle

/-- Exact real-valued section volume of the occupied grid union. -/
theorem occupiedGridRegion_section_real {n : ℕ} {J : Type*}
    (family : Finset J) (b v : J → Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (I : J → Set ℝ) (t : ℝ) :
    volume.real ((fun x => (t,x)) ⁻¹' occupiedGridRegion family b v r I) =
      (((family.filter (fun j => t ∈ I j)).image
        (fun j => gridIndex r (segmentPoint (b j) (v j) t))).card:ℝ)*r^n := by
  rw [occupiedGridRegion_section family b v hr I t,Measure.real,volume_gridCell_union hr]
  simp [ENNReal.toReal_mul,ENNReal.toReal_pow,hr.le]

/-- Markov selection with an exact loss of at most half the portion density.
The threshold is expressed using the actual product volume, not an assumed
section-count average. -/
theorem grid_small_sections {n : ℕ} {J : Type*}
    (family : Finset J) (hne : family.Nonempty) (b v : J → Fin n → ℝ)
    {r lam : ℝ} (hr : 0 < r) (hlam : 0 < lam) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j))
    (hs : ∀ j ∈ family, I j ⊆ Set.Icc (0:ℝ) 1)
    (hsize : ∀ j ∈ family, lam ≤ volume.real (I j)) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Set.Icc (0:ℝ) 1 ∧
      (∀ j ∈ family, lam/2 ≤ volume.real (I j ∩ A)) ∧
      ∀ t ∈ A,
        volume.real ((fun x => (t,x)) ⁻¹' occupiedGridRegion family b v r I) ≤
          2*volume.real (occupiedGridRegion family b v r I)/lam := by
  let E := occupiedGridRegion family b v r I
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let f := fun t => volume.real ((fun x => (t,x)) ⁻¹' E)
  let V := volume.real E
  have hE := measurableSet_occupiedGridRegion family b v r I hm
  have hf : Measurable f := (measurable_measure_prodMk_left hE).ennreal_toReal
  have hfin := occupiedGridRegion_volume_ne_top μ family b v hr I hm
  have hint : Integrable f μ := Measure.integrable_measure_prodMk_left hE hfin
  have htotal : ∫ t, f t ∂μ = V := by
    rw [occupiedGridRegion_section_integral μ family b v hr I hm]
    change (((volume.restrict (Set.Icc (0:ℝ) 1)).prod volume) E).toReal = _
    rw [occupiedGridRegion_restrict_volume family b v r I hm hs]
    rfl
  obtain ⟨j₀,hj₀⟩ := hne
  have hV : 0 < V := occupiedGridRegion_positive_volume family b v hr I hm hs j₀ hj₀
    (hlam.trans_le (hsize j₀ hj₀))
  let bad := {t | 2*V/lam ≤ f t}
  have hbad : MeasurableSet bad := measurableSet_le measurable_const hf
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ:=μ) (f:=f) (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) hint (2*V/lam)
  rw [htotal] at hmark
  have hbadsize : μ.real bad ≤ lam/2 := by
    have hpos : 0 < 2*V/lam := by positivity
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      (2*V/lam)*μ.real bad ≤ V := hmark
      _ = (2*V/lam)*(lam/2) := by field_simp
  let A := Set.Icc (0:ℝ) 1 \ bad
  refine ⟨A,measurableSet_Icc.diff hbad,Set.sdiff_subset,?_,?_⟩
  · intro j hj
    have hIeq : μ.real (I j)=volume.real (I j) := by
      rw [Measure.real,Measure.restrict_apply (hm j hj),Set.inter_eq_left.mpr (hs j hj)]
      rfl
    have hAeq : μ.real (I j \ bad)=volume.real (I j \ bad) := by
      rw [Measure.real,Measure.restrict_apply ((hm j hj).diff hbad),
        Set.inter_eq_left.mpr (Set.sdiff_subset.trans (hs j hj))]
      rfl
    have hsplit := measureReal_inter_add_sdiff (μ:=μ) (s:=I j) hbad
    have hcap : μ.real (I j ∩ bad) ≤ μ.real bad := measureReal_mono Set.inter_subset_right
    have he : I j ∩ A = I j \ bad := by
      ext t; simp only [A,Set.mem_inter_iff,Set.mem_sdiff];
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hs j hj h.1,h.2⟩⟩
    rw [he,← hAeq]
    rw [hIeq] at hsplit
    linarith [hsize j hj]
  · intro t ht
    exact le_of_lt (lt_of_not_ge ht.2)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.occupiedGridRegion_restrict_volume
#print axioms KakeyaTwoScale.occupiedGridRegion_finite_volume
#print axioms KakeyaTwoScale.occupiedGridRegion_positive_volume
#print axioms KakeyaTwoScale.grid_small_sections

#print axioms KakeyaTwoScale.occupiedGridRegion_section_real
