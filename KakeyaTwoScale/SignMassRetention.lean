module
public import KakeyaTwoScale.BisectionScaleChoice

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Restricting a sign set to a large measurable inner set loses at most the
outer annulus mass. Finiteness is proved from the actual enclosing set. -/
theorem retained_mass_lower {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (B I S : Set X) (hI : MeasurableSet I)
    (hB : μ B ≠ ∞) (hIB : I ⊆ B) (hSB : S ⊆ B)
    (hs : (2/5:ℝ)*μ.real B ≤ μ.real S)
    (hi : (9/10:ℝ)*μ.real B ≤ μ.real I) :
    (3/10:ℝ)*μ.real B ≤ μ.real (S ∩ I) := by
  have hS : μ S ≠ ∞ := measure_ne_top_of_subset hSB hB
  have h1 := measureReal_inter_add_sdiff (μ := μ) (s := S) hI hS
  have h2 := measureReal_inter_add_sdiff (μ := μ) (s := B) hI hB
  have hinter : B ∩ I = I := inter_eq_right.mpr hIB
  rw [hinter] at h2
  have hd : μ.real (S \ I) ≤ μ.real (B \ I) :=
    ENNReal.toReal_mono (measure_ne_top_of_subset sdiff_subset hB)
      (measure_mono (sdiff_subset_sdiff_left hSB))
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.retained_mass_lower
