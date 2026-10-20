module
public import KakeyaTwoScale.PortionGridVolume
public import KakeyaTwoScale.ArithmeticPruning

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

def gridMultiplicity {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r : ℝ) (x : ℝ × (Fin n → ℝ)) : ℝ :=
  membershipCount G (fun j => gridPortion (b j) (v j) r (Set.Icc (0:ℝ) 1)) x

def gridHighRegion {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r T : ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  occupiedGridRegion G b v r (fun _ => Set.Icc (0:ℝ) 1) ∩
    {x | T < gridMultiplicity G b v r x}

theorem measurable_gridMultiplicity {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r : ℝ) : Measurable (gridMultiplicity G b v r) := by
  exact Finset.measurable_sum _ (fun j _ => measurable_const.indicator
    (measurableSet_gridPortion (b j) (v j) r _ measurableSet_Icc))

theorem gridMultiplicity_nonneg {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r : ℝ) (x : ℝ × (Fin n → ℝ)) :
    0 ≤ gridMultiplicity G b v r x := by
  rw [gridMultiplicity,membershipCount_eq_card]
  positivity

theorem measurableSet_gridHighRegion {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r T : ℝ) : MeasurableSet (gridHighRegion G b v r T) :=
  (measurableSet_occupiedGridRegion G b v r _ (fun _ _ => measurableSet_Icc)).inter
    (measurableSet_lt measurable_const (measurable_gridMultiplicity G b v r))

theorem gridHighRegion_finite {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) {r : ℝ} (hr : 0 < r) (T : ℝ) :
    volume (gridHighRegion G b v r T) ≠ ⊤ :=
  measure_ne_top_of_subset Set.inter_subset_left
    (occupiedGridRegion_finite_volume G b v hr _ (fun _ _ => measurableSet_Icc)
      (fun _ _ => Set.Subset.rfl))

theorem gridMultiplicity_integral {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (gridMultiplicity G b v r) volume ∧
      (∫ x, gridMultiplicity G b v r x) = r^n*(G.card:ℝ) := by
  have hvol (j) : volume (gridPortion (b j) (v j) r (Set.Icc (0:ℝ) 1)) =
      ENNReal.ofReal r^n := by
    rw [Measure.volume_eq_prod,volume_gridPortion volume _ _ hr _ measurableSet_Icc]
    simp
  have hint (j) : Integrable ((gridPortion (b j) (v j) r (Set.Icc (0:ℝ) 1)).indicator (fun _ => (1:ℝ))) volume := by
    apply (integrable_indicator_iff (measurableSet_gridPortion _ _ _ _ measurableSet_Icc)).mpr
    exact integrableOn_const (by rw [hvol]; finiteness)
  refine ⟨integrable_finsetSum G (fun j _ => hint j),?_⟩
  unfold gridMultiplicity membershipCount
  rw [integral_finsetSum G (fun j _ => hint j)]
  have hv (j) : volume.real (gridPortion (b j) (v j) r (Set.Icc (0:ℝ) 1))=r^n := by
    rw [Measure.real,hvol]; simp [hr.le]
  calc
    _ = ∑ _j ∈ G, r^n := Finset.sum_congr rfl (fun j _ => by
      rw [integral_indicator_const (1:ℝ) (measurableSet_gridPortion (b j) (v j) r _ measurableSet_Icc)]
      simp [hv])
    _ = _ := by simp [mul_comm]

/-- Markov's inequality for the actual high-multiplicity grid union. -/
theorem grid_high_volume_bound {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) {r : ℝ} (hr : 0 < r) (T : ℝ) :
    T*volume.real (gridHighRegion G b v r T) ≤ r^n*(G.card:ℝ) := by
  have hm := measurableSet_gridHighRegion G b v r T
  have hi : Integrable ((gridHighRegion G b v r T).indicator (fun _ => T)) volume :=
    (integrable_indicator_iff hm).mpr (integrableOn_const (gridHighRegion_finite G b v hr T))
  have hh := integral_mono hi (gridMultiplicity_integral G b v hr).1 (fun x => by
    by_cases hx : x ∈ gridHighRegion G b v r T
    · rw [Set.indicator_of_mem hx]; exact hx.2.le
    · rw [Set.indicator_of_notMem hx]; exact gridMultiplicity_nonneg G b v r x)
  rw [integral_indicator_const T hm,(gridMultiplicity_integral G b v hr).2] at hh
  simpa [mul_comm] using hh

/-- Axis multiplicity is constant on each whole horizontal grid cell. -/
theorem gridMultiplicity_eq_axis {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (j : J) (x : Fin n → ℝ)
    (hx : gridIndex r x=gridIndex r (segmentPoint (b j) (v j) t)) :
    gridMultiplicity G b v r (t,x) =
      axisMultiplicity G (fun j t => gridIndex r (segmentPoint (b j) (v j) t)) j t := by
  unfold gridMultiplicity axisMultiplicity
  rw [membershipCount_eq_card,membershipCount_eq_card]
  congr 2
  ext k
  simp only [Finset.mem_filter,gridPortion,Set.mem_ofPred_eq,ht,true_and,hx]
  exact and_congr_right (fun _ => eq_comm)

/-- Portions selected by high axis multiplicity occupy whole cells contained
in the same fixed high region used in the Markov estimate. -/
theorem grid_exception_region_subset {n : ℕ} {J : Type*} (G S : Finset J)
    (hSG : S ⊆ G) (b v : J → Fin n → ℝ) (r T : ℝ) :
    occupiedGridRegion S b v r (fun j => Set.Icc (0:ℝ) 1 ∩
      {t | T < axisMultiplicity G (fun j t => gridIndex r (segmentPoint (b j) (v j) t)) j t}) ⊆
      gridHighRegion G b v r T := by
  intro x hx
  obtain ⟨j,hj,ht,hcell⟩ := Set.mem_iUnion₂.mp hx
  refine ⟨Set.mem_iUnion₂.mpr ⟨j,hSG hj,ht.1,hcell⟩,?_⟩
  change T < gridMultiplicity G b v r (x.1,x.2)
  rw [gridMultiplicity_eq_axis G b v r x.1 ht.1 j x.2 hcell]
  exact ht.2

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurable_gridMultiplicity
#print axioms KakeyaTwoScale.gridMultiplicity_nonneg
#print axioms KakeyaTwoScale.measurableSet_gridHighRegion
#print axioms KakeyaTwoScale.gridHighRegion_finite
#print axioms KakeyaTwoScale.gridMultiplicity_integral
#print axioms KakeyaTwoScale.grid_high_volume_bound
#print axioms KakeyaTwoScale.gridMultiplicity_eq_axis
#print axioms KakeyaTwoScale.grid_exception_region_subset
