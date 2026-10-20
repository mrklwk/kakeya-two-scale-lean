module
public import KakeyaTwoScale.FiniteNarrowSelection

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {J : Type*} [Countable J]

/-- The actual broad locus is measurable because its predicate depends only
on the finite original incidence pattern. -/
def finiteGridBroadRegion {n : ℕ} (G : Finset J) (b v : J → Fin n → ℝ)
    (u : J → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {x | ¬ finiteNarrowPattern u k r
    (finiteIncidentPattern G (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) x)}

theorem measurableSet_finiteGridBroadRegion {n : ℕ} (G : Finset J) (b v : J → Fin n → ℝ)
    (u : J → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) :
    MeasurableSet (finiteGridBroadRegion G b v u k d r) :=
  measurableSet_finiteIncidentPattern_property G _
    (fun j => measurableSet_gridPortion (b j) (v j) d _ measurableSet_Icc)
    (fun S => ¬ finiteNarrowPattern u k r S)

/-- Integrating the actual half-retention at every narrow cell gives the
source 3U/8 mass. No retained-mass or integrability premise is assumed. -/
theorem finite_narrow_grid_retained_mass {n : ℕ} (G : Finset J) (b v : J → Fin n → ℝ)
    (u : J → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) (hd : 0 < d)
    (hbroad : (∫ x in finiteGridBroadRegion G b v u k d r,
      gridMultiplicity G b v d x) ≤ (d^n*(G.card:ℝ))/4) :
    3*(d^n*(G.card:ℝ))/8 ≤ d^n*∑ j∈G, volume.real (finiteNarrowGridHeights G b v u k d r j) := by
  let I := finiteNarrowGridHeights G b v u k d r
  let old := gridMultiplicity G b v d
  let kept := membershipCount G (fun j => gridPortion (b j) (v j) d (I j))
  let Ω := finiteGridBroadRegion G b v u k d r
  have hΩ : MeasurableSet Ω := measurableSet_finiteGridBroadRegion G b v u k d r
  have hi := grid_portion_multiplicity_integral G b v hd I
    (fun j _ => measurableSet_finiteNarrowGridHeights G b v u k d r j) (fun _ _ _ hx => hx.1)
  have hkept : ∀ x, 0 ≤ kept x := by
    intro x
    change 0 ≤ membershipCount G (fun j => gridPortion (b j) (v j) d (I j)) x
    rw [membershipCount_eq_card]
    positivity
  have hpoint (x : ℝ × (Fin n → ℝ)) : old x ≤ Ω.indicator old x+2*kept x := by
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
      linarith [hkept x]
    · rw [Set.indicator_of_notMem hx]
      have hn : finiteNarrowPattern u k r
          (finiteIncidentPattern G (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) x) := by
        simpa only [Ω,finiteGridBroadRegion,Set.mem_ofPred_eq,not_not] using hx
      have hh := finiteNarrowGrid_retained_card G b v u k d r x.1 x.2 hn
      dsimp [old,kept,gridMultiplicity]
      rw [membershipCount_eq_card,membershipCount_eq_card]
      simp only [zero_add]
      exact_mod_cast hh
  have hold := gridMultiplicity_integral G b v hd
  have htotal := integral_mono hold.1 ((hold.1.indicator hΩ).add (hi.1.const_mul 2)) hpoint
  change (∫ x, old x) ≤ ∫ x, Ω.indicator old x+2*kept x at htotal
  rw [integral_add (hold.1.indicator hΩ) (hi.1.const_mul 2),integral_indicator hΩ,integral_const_mul] at htotal
  have ho : (∫ x, old x)=d^n*(G.card:ℝ) := by simpa [old] using hold.2
  have hk : (∫ x, kept x)=d^n*∑ j∈G, volume.real (I j) := hi.2
  rw [ho,hk] at htotal
  change (∫ x in Ω, old x) ≤ (d^n*(G.card:ℝ))/4 at hbroad
  change 3*(d^n*(G.card:ℝ))/8 ≤ d^n*∑ j∈G, volume.real (I j)
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurableSet_finiteGridBroadRegion
#print axioms KakeyaTwoScale.finite_narrow_grid_retained_mass
