module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
namespace KakeyaTwoScale

/-- The change of progression origin and step has exactly the expected area scaling.
The proof uses Fubini and the one-dimensional translation and dilation formulas. -/
theorem volume_preimage_progressionAffine (i d : ℝ) (hd : d ≠ 0)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    volume ((fun p : ℝ × ℝ => (p.1 + i*p.2, d*p.2)) ⁻¹' E) =
      ENNReal.ofReal |d⁻¹| * volume E := by
  have hm : Measurable (fun p : ℝ × ℝ => (p.1 + i*p.2, d*p.2)) :=
    (measurable_fst.add (measurable_const.mul measurable_snd)).prodMk
      (measurable_const.mul measurable_snd)
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (hE.preimage hm)]
  have hs (y : ℝ) :
      volume ((fun x : ℝ => (x,y)) ⁻¹'
        ((fun p : ℝ × ℝ => (p.1+i*p.2,d*p.2)) ⁻¹' E)) =
      volume ((fun x : ℝ => (x,d*y)) ⁻¹' E) := by
    exact (measurePreserving_add_right volume (i*y)).measure_preimage
      (hE.preimage (measurable_id.prodMk
        (measurable_const : Measurable (fun _ : ℝ => d*y)))).nullMeasurableSet
  simp_rw [hs]
  rw [← lintegral_map (μ := (volume : Measure ℝ))
      (f := fun y : ℝ => volume ((fun x : ℝ => (x,y)) ⁻¹' E))
      (g := fun y : ℝ => d*y) (measurable_measure_prodMk_right hE)
      (measurable_const.mul measurable_id), Real.map_volume_mul_left hd,
      lintegral_smul_measure, ← Measure.prod_apply_symm hE]
  rfl

theorem volume_preimage_progressionAffine_le (i d : ℝ) (hd : 1 ≤ d)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    volume ((fun p : ℝ × ℝ => (p.1 + i*p.2, d*p.2)) ⁻¹' E) ≤ volume E := by
  rw [volume_preimage_progressionAffine i d (by linarith) hE]
  have hc : ENNReal.ofReal |d⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr (by linarith))]
    exact ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ hd)
  simpa using mul_le_mul_left hc (volume E)

end KakeyaTwoScale

#print axioms KakeyaTwoScale.volume_preimage_progressionAffine
#print axioms KakeyaTwoScale.volume_preimage_progressionAffine_le
