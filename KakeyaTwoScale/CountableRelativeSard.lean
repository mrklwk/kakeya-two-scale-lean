module
public import KakeyaTwoScale.SmoothFiberRegularValues
public import Mathlib.MeasureTheory.Group.Arithmetic

@[expose] public section

open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- A single translated arithmetic grid avoids the critical levels of a
countable family of actual regular fibers. Codomains may vary across fibers.
No transversality or null-set certificate is supplied as an input. -/
theorem countable_fibers_transverse_grid_offset
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {I : Type} [Countable I] (F : I→Type)
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)]
    (f : ∀ i, E→F i) (g : E→ℝ) (c : ∀ i, F i)
    (hf : ∀ i x, f i x=c i → ContDiffAt ℝ ∞ (f i) x)
    (hg : ContDiff ℝ ∞ g)
    (hreg : ∀ i x, f i x=c i → (fderiv ℝ (f i) x).range=⊤)
    (h : ℝ) (hh : 0<h) :
    ∃ theta∈Ioo 0 h, ∀ i (m : ℤ) x, f i x=c i → g x=theta+m*h →
      ∃ v : E, fderiv ℝ (f i) x v=0 ∧ fderiv ℝ g x v≠0 := by
  classical
  let bad : I→Set ℝ := fun i => g '' {x | f i x=c i ∧
    ∀ v : E, fderiv ℝ (f i) x v=0 → fderiv ℝ g x v=0}
  have hb (i) : volume (bad i)=0 := smooth_fiber_critical_values_null
    (f i) g (c i) (hf i) (fun _ _ => hg.contDiffAt) (hreg i)
  let shifted : I→ℤ→Set ℝ := fun i m => (fun t : ℝ => t+m*h) ⁻¹' bad i
  have hn : volume (⋃ i, ⋃ m, shifted i m)=0 := by
    apply measure_iUnion_null
    intro i
    apply measure_iUnion_null
    intro m
    dsimp [shifted]
    rw [measure_preimage_add_right]
    exact hb i
  have hnot : ¬Ioo 0 h ⊆ ⋃ i, ⋃ m, shifted i m := by
    intro hs
    have he := measure_mono (μ := volume) hs
    rw [hn] at he
    exact (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hh)).not_ge he
  obtain ⟨theta,ht,htbad⟩ := Set.not_subset.mp hnot
  refine ⟨theta,ht,?_⟩
  intro i m x hx hxt
  by_contra hc
  push Not at hc
  apply htbad
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨m,⟨x,⟨hx,hc⟩,hxt⟩⟩⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.countable_fibers_transverse_grid_offset
