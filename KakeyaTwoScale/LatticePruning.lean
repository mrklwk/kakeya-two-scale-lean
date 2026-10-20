module
public import KakeyaTwoScale.GridMultiplicity
public import KakeyaTwoScale.AffineGridVolume

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Source multiplicity pruning for actual translated lattice segments.
Both formerly assumed volume estimates are now proved for the SAME fixed
high region. The retained sets are measurable unit-height portions, retain
(1-eta) of the original mass, and satisfy an everywhere cell cap. -/
theorem lattice_multiplicity_pruning (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty →
      Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
      ∀ z w : Fin n → ℝ, ∃ I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (I j) ∧ I j ⊆ Set.Icc (0:ℝ) 1) ∧
      (1-eta)*(G.card:ℝ) ≤ ∑ j ∈ G, volume.real (I j) ∧
      ∀ t k, ((G.filter (fun j => t ∈ I j ∧ gridIndex r
        (segmentPoint (latticePoint r j.1+z) (latticePoint r j.2+w) t)=k)).card:ℝ) ≤
        C*(G.card:ℝ)^theta := by
  obtain ⟨c,hc,hportion⟩ := lattice_portions_volume n (eta/2) (by positivity)
  refine ⟨pruningCoefficient c eta,pruningCoefficient_pos hc heta,?_⟩
  intro r hr G hG hinj z w
  let b := fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint r p.1+z
  let v := fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint r p.2+w
  let cell := fun j t => gridIndex r (segmentPoint (b j) (v j) t)
  let T := pruningCoefficient c eta*(G.card:ℝ)^theta
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hm : ∀ i ∈ G, ∀ j, MeasurableSet {t | cell i t=cell j t} := by
    intro i _ j
    exact measurableSet_eq_fun
      ((measurable_gridIndex r).comp (continuous_const.add (continuous_id.smul continuous_const)).measurable)
      ((measurable_gridIndex r).comp (continuous_const.add (continuous_id.smul continuous_const)).measurable)
  let bad := fun j => {t | T < axisMultiplicity G cell j t}
  have hbad : ∀ j, MeasurableSet (bad j) := by
    intro j
    exact measurableSet_lt measurable_const
      (Finset.measurable_sum _ (fun i hi => measurable_const.indicator (hm i hi j)))
  let J := fun j => Set.Icc (0:ℝ) 1 ∩ bad j
  have hJ (j) : MeasurableSet (J j) := measurableSet_Icc.inter (hbad j)
  have hlength (j) : μ.real (bad j)=volume.real (J j) := by
    rw [Measure.real,Measure.restrict_apply (hbad j)]
    simp only [J,Set.inter_comm,Measure.real]
  let S := G.filter (fun j => eta/2 ≤ μ.real (bad j))
  let V := volume.real (gridHighRegion G b v r T)
  have hlower : c*r^n*(S.card:ℝ)^a ≤ V := by
    by_cases hS : S.Nonempty
    · have hh := hportion r hr S hS (hinj.mono (Finset.filter_subset _ _)) z w J
        (fun j _ => hJ j) (fun _ _ => Set.inter_subset_left) (fun j hj => by
          rw [← hlength]; exact (Finset.mem_filter.mp hj).2)
      exact hh.trans (measureReal_mono
        (grid_exception_region_subset G S (Finset.filter_subset _ _) b v r T)
        (gridHighRegion_finite G b v hr T))
    · have he := Finset.not_nonempty_iff_eq_empty.mp hS
      simpa [he,Real.zero_rpow (show a ≠ 0 by norm_num [a])] using
        (show 0 ≤ V from measureReal_nonneg)
  have hupper : T*V ≤ r^n*(G.card:ℝ) := grid_high_volume_bound G b v hr T
  obtain ⟨I₀,hI₀,hmass,hcap⟩ := pruning_from_volume_bounds μ G hG cell c eta (r^n) V
    hc heta (pow_pos hr n) hm hupper hlower
  let I := fun j => Set.Icc (0:ℝ) 1 ∩ I₀ j
  have hreal (j) : volume.real (I j)=μ.real (I₀ j) := by
    rw [Measure.real,Measure.real,Measure.restrict_apply (hI₀ j)]
    simp only [I,Set.inter_comm]
  refine ⟨I,fun j => ⟨measurableSet_Icc.inter (hI₀ j),Set.inter_subset_left⟩,?_,?_⟩
  · simpa only [hreal] using hmass
  · intro t k
    have hsub : G.filter (fun j => t ∈ I j ∧ cell j t=k) ⊆
        G.filter (fun j => t ∈ I₀ j ∧ cell j t=k) := by
      intro j hj
      obtain ⟨hj,ht,hk⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hj,ht.2,hk⟩
    have hcard := (Nat.cast_le (α:=ℝ)).mpr (Finset.card_le_card hsub)
    have hcap' : ((G.filter (fun j => t ∈ I₀ j ∧ cell j t=k)).card:ℝ) ≤
        pruningCoefficient c eta*(G.card:ℝ)^theta := by
      convert hcap t k using 1
      congr 2
      ext j
      simp only [Finset.mem_filter]
    have hh := hcard.trans hcap'
    convert hh using 1
    congr 2
    ext j
    simp only [Finset.mem_filter,cell,b,v]

/-- The same pruning theorem in independently affine-moving measurement grids. -/
theorem lattice_multiplicity_pruning_affine (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty →
      Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
      ∀ z w xi zeta : Fin n → ℝ, ∃ I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (I j) ∧ I j ⊆ Set.Icc (0:ℝ) 1) ∧
      (1-eta)*(G.card:ℝ) ≤ ∑ j ∈ G, volume.real (I j) ∧
      ∀ t k, ((G.filter (fun j => t ∈ I j ∧ gridIndex r
        (segmentPoint (latticePoint r j.1+z) (latticePoint r j.2+w) t-(xi+t • zeta))=k)).card:ℝ) ≤
        C*(G.card:ℝ)^theta := by
  obtain ⟨C,hC,hprune⟩ := lattice_multiplicity_pruning n eta heta
  refine ⟨C,hC,?_⟩
  intro r hr G hG hinj z w xi zeta
  obtain ⟨I,hm,hmass,hcap⟩ := hprune r hr G hG hinj (z-xi) (w-zeta)
  refine ⟨I,hm,hmass,?_⟩
  intro t k
  simpa only [affine_grid_cell_identity,add_sub_assoc] using hcap t k

end KakeyaTwoScale
#print axioms KakeyaTwoScale.lattice_multiplicity_pruning

#print axioms KakeyaTwoScale.lattice_multiplicity_pruning_affine
