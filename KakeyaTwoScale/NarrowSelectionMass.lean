module
public import KakeyaTwoScale.BroadNarrowSelection

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Genuine product integration of arbitrary measurable grid portions. -/
theorem grid_portion_multiplicity_integral {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) {d : ℝ} (hd : 0 < d) (I : J → Set ℝ)
    (hI : ∀ j ∈ G, MeasurableSet (I j))
    (hunit : ∀ j ∈ G, I j ⊆ Set.Icc (0:ℝ) 1) :
    Integrable (membershipCount G (fun j => gridPortion (b j) (v j) d (I j))) volume ∧
      (∫ x, membershipCount G (fun j => gridPortion (b j) (v j) d (I j)) x) =
        d^n*∑ j ∈ G, volume.real (I j) := by
  have hfinite (j) (hj : j ∈ G) : volume (I j) ≠ ⊤ :=
    measure_ne_top_of_subset (hunit j hj) (by simp)
  have hvol (j) (hj : j ∈ G) : volume (gridPortion (b j) (v j) d (I j))=
      ENNReal.ofReal d^n*volume (I j) := by
    rw [Measure.volume_eq_prod,volume_gridPortion volume _ _ hd _ (hI j hj)]
  have hint (j) (hj : j ∈ G) : Integrable ((gridPortion (b j) (v j) d (I j)).indicator (fun _ => (1:ℝ))) volume := by
    apply (integrable_indicator_iff (measurableSet_gridPortion _ _ _ _ (hI j hj))).mpr
    have hf : volume (gridPortion (b j) (v j) d (I j)) ≠ ⊤ := by
      rw [hvol j hj]
      exact ENNReal.mul_ne_top (by finiteness) (hfinite j hj)
    exact integrableOn_const hf
  refine ⟨integrable_finsetSum G hint,?_⟩
  unfold membershipCount
  rw [integral_finsetSum G hint,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_indicator_const (1:ℝ) (measurableSet_gridPortion _ _ _ _ (hI j hj))]
  simp only [smul_eq_mul,mul_one]
  rw [Measure.real,hvol j hj,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hd.le]
  rfl

/-- The actual broad locus is measurable because its predicate depends only
on the finite original incidence pattern. -/
def gridBroadRegion {n N : ℕ} (b v : Fin N → Fin n → ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {x | ¬ narrowPattern u k r
    (incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) x)}

theorem measurableSet_gridBroadRegion {n N : ℕ} (b v : Fin N → Fin n → ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) :
    MeasurableSet (gridBroadRegion b v u k d r) :=
  measurableSet_incidentPattern_property _
    (fun j => measurableSet_gridPortion (b j) (v j) d _ measurableSet_Icc)
    (fun S => ¬ narrowPattern u k r S)

/-- Integrating the actual half-retention at every narrow cell gives the
source 3U/8 mass. No retained-mass or integrability premise is assumed. -/
theorem narrow_grid_retained_mass {n N : ℕ} (b v : Fin N → Fin n → ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) (hd : 0 < d)
    (hbroad : (∫ x in gridBroadRegion b v u k d r,
      gridMultiplicity Finset.univ b v d x) ≤ (d^n*(N:ℝ))/4) :
    3*(d^n*(N:ℝ))/8 ≤ d^n*∑ j : Fin N, volume.real (narrowGridHeights b v u k d r j) := by
  let I := narrowGridHeights b v u k d r
  let old := gridMultiplicity Finset.univ b v d
  let kept := membershipCount Finset.univ (fun j => gridPortion (b j) (v j) d (I j))
  let Ω := gridBroadRegion b v u k d r
  have hΩ : MeasurableSet Ω := measurableSet_gridBroadRegion b v u k d r
  have hi := grid_portion_multiplicity_integral Finset.univ b v hd I
    (fun j _ => measurableSet_narrowGridHeights b v u k d r j) (fun _ _ _ hx => hx.1)
  have hkept : ∀ x, 0 ≤ kept x := by
    intro x
    change 0 ≤ membershipCount Finset.univ (fun j => gridPortion (b j) (v j) d (I j)) x
    rw [membershipCount_eq_card]
    positivity
  have hpoint (x : ℝ × (Fin n → ℝ)) : old x ≤ Ω.indicator old x+2*kept x := by
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
      linarith [hkept x]
    · rw [Set.indicator_of_notMem hx]
      have hn : narrowPattern u k r
          (incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) x) := by
        simpa only [Ω,gridBroadRegion,Set.mem_ofPred_eq,not_not] using hx
      have hh := narrowGrid_retained_card b v u k d r x.1 x.2 hn
      dsimp [old,kept,gridMultiplicity]
      rw [membershipCount_eq_card,membershipCount_eq_card]
      simp only [zero_add]
      exact_mod_cast hh
  have hold := gridMultiplicity_integral Finset.univ b v hd
  have htotal := integral_mono hold.1 ((hold.1.indicator hΩ).add (hi.1.const_mul 2)) hpoint
  change (∫ x, old x) ≤ ∫ x, Ω.indicator old x+2*kept x at htotal
  rw [integral_add (hold.1.indicator hΩ) (hi.1.const_mul 2),integral_indicator hΩ,integral_const_mul] at htotal
  have ho : (∫ x, old x)=d^n*(N:ℝ) := by simpa [old] using hold.2
  have hk : (∫ x, kept x)=d^n*∑ j : Fin N, volume.real (I j) := hi.2
  rw [ho,hk] at htotal
  change (∫ x in Ω, old x) ≤ (d^n*(N:ℝ))/4 at hbroad
  change 3*(d^n*(N:ℝ))/8 ≤ d^n*∑ j : Fin N, volume.real (I j)
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.grid_portion_multiplicity_integral
#print axioms KakeyaTwoScale.measurableSet_gridBroadRegion
#print axioms KakeyaTwoScale.narrow_grid_retained_mass
