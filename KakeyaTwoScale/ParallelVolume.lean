module
public import KakeyaTwoScale.GridRegion

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Moving every grid intercept by the same displacement preserves indices
up to one common translation, at every real height and every scale. -/
theorem gridIndex_lattice_translate {n : ℕ} {r : ℝ} (hr : 0 < r)
    (B : Fin n → ℤ) (z : Fin n → ℝ) :
    gridIndex r (fun i => r*(B i : ℝ)+z i) = fun i => B i + gridIndex r z i := by
  funext i
  unfold gridIndex
  rw [add_div, mul_div_cancel_left₀ _ hr.ne', Int.floor_intCast_add]

def gridPortion {n : ℕ} (b v : Fin n → ℝ) (r : ℝ) (I : Set ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {z | z.1 ∈ I ∧ gridIndex r z.2 = gridIndex r (segmentPoint b v z.1)}

theorem measurableSet_gridPortion {n : ℕ} (b v : Fin n → ℝ) (r : ℝ)
    (I : Set ℝ) (hI : MeasurableSet I) : MeasurableSet (gridPortion b v r I) := by
  exact (hI.preimage measurable_fst).inter
    (measurableSet_eq_fun ((measurable_gridIndex r).comp measurable_snd)
      ((measurable_gridIndex r).comp
        (continuous_const.add (continuous_fst.smul continuous_const)).measurable))

/-- Exact genuine product volume of one grid-thickened portion. -/
theorem volume_gridPortion {n : ℕ} (μ : Measure ℝ) [SFinite μ]
    (b v : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (I : Set ℝ) (hI : MeasurableSet I) :
    (μ.prod volume) (gridPortion b v r I) = ENNReal.ofReal r^n * μ I := by
  rw [Measure.prod_apply (measurableSet_gridPortion b v r I hI)]
  have he : (fun t => volume ((fun x => (t,x)) ⁻¹' gridPortion b v r I)) =
      I.indicator (fun _ => ENNReal.ofReal r^n) := by
    funext t
    by_cases ht : t ∈ I
    · have hs : (fun x => (t,x)) ⁻¹' gridPortion b v r I =
          gridCell r (gridIndex r (segmentPoint b v t)) := by
        ext x
        simp [gridPortion, ht, mem_gridCell_iff hr]
      rw [hs, volume_gridCell r _, Set.indicator_of_mem ht]
    · have hs : (fun x => (t,x)) ⁻¹' gridPortion b v r I = ∅ := by
        ext x; simp [gridPortion, ht]
      simp [hs, ht]
  rw [he, lintegral_indicator hI, lintegral_const]
  simp

/-- Distinct lattice intercepts with common slope have disjoint occupied
cells, even with arbitrary measurable portions and arbitrary grid translation. -/
theorem parallel_gridPortions_disjoint {n : ℕ} {r : ℝ} (hr : 0 < r)
    (B D : Fin n → ℤ) (hBD : B ≠ D) (z v : Fin n → ℝ) (I J : Set ℝ) :
    Disjoint (gridPortion (fun i => r*(B i : ℝ)+z i) v r I)
      (gridPortion (fun i => r*(D i : ℝ)+z i) v r J) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have he := hx.2.symm.trans hy.2
  have haxis (A : Fin n → ℤ) :
      segmentPoint (fun i => r*(A i : ℝ)+z i) v x.1 =
      fun i => r*(A i : ℝ)+(z i+x.1*v i) := by
    funext i
    simp only [segmentPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [haxis B, haxis D] at he
  rw [gridIndex_lattice_translate hr, gridIndex_lattice_translate hr] at he
  apply hBD
  funext i
  have hh := congrFun he i
  exact add_right_cancel hh

/-- Exact volume, rather than a conditional volume certificate, for a whole
parallel fiber. No arithmetic counting theorem is used. -/
theorem parallel_portions_volume {n : ℕ} {J : Type*} (μ : Measure ℝ) [SFinite μ]
    (family : Finset J) (B : J → Fin n → ℤ) (hB : Set.InjOn B (↑family : Set J))
    (z v : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j)) :
    (μ.prod volume) (occupiedGridRegion family
      (fun j i => r*(B j i : ℝ)+z i) (fun _ => v) r I) =
      ENNReal.ofReal r^n * ∑ j ∈ family, μ (I j) := by
  change (μ.prod volume) (⋃ j ∈ family, gridPortion _ v r (I j)) = _
  rw [measure_biUnion_finset]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact volume_gridPortion μ _ v hr _ (hm j hj)
  · intro j hj k hk hjk
    exact parallel_gridPortions_disjoint hr (B j) (B k) (fun h => hjk (hB hj hk h)) z v _ _
  · intro j hj
    exact measurableSet_gridPortion _ v r _ (hm j hj)

/-- In a mixed-slope family every parallel fiber supplies an unconditional
lower bound for the actual union volume. The filter is the actual slope fiber. -/
theorem parallel_fiber_volume_lower {n : ℕ} {J : Type*} (μ : Measure ℝ) [SFinite μ]
    (family : Finset J) (B : J → Fin n → ℤ) (v : J → Fin n → ℝ)
    (z w : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (I : J → Set ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (I j))
    (hB : Set.InjOn B (↑(family.filter (fun j => v j = w)) : Set J)) :
    ENNReal.ofReal r^n * ∑ j ∈ family.filter (fun j => v j = w), μ (I j) ≤
      (μ.prod volume) (occupiedGridRegion family (fun j i => r*(B j i : ℝ)+z i) v r I) := by
  rw [← parallel_portions_volume μ (family.filter (fun j => v j = w)) B hB z w hr I
    (fun j hj => hm j (Finset.mem_filter.mp hj).1)]
  apply measure_mono
  intro x hx
  obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨hj, hv⟩ := Finset.mem_filter.mp hj
  apply Set.mem_iUnion₂.mpr
  exact ⟨j, hj, by simpa [hv] using hx⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.gridIndex_lattice_translate
#print axioms KakeyaTwoScale.volume_gridPortion
#print axioms KakeyaTwoScale.parallel_gridPortions_disjoint
#print axioms KakeyaTwoScale.parallel_portions_volume

#print axioms KakeyaTwoScale.parallel_fiber_volume_lower
