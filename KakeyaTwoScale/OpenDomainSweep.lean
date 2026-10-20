module
public import KakeyaTwoScale.CompactC1Extension
public import KakeyaTwoScale.RegularMultiplicityLineSweep

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace KakeyaTwoScale

/-- The exact sweep estimate on a compact subset of an open C1 domain.
The cutoff does not enter the multiplicity constant. -/
theorem open_regular_sweep_compact (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (Fin m → ℝ) → (Fin m → ℝ))
      (U : Set (Fin m → ℝ)), IsOpen U → ContDiffOn ℝ 1 F U →
      ∀ (S : Set (Fin m → ℝ)), IsCompact S → S ⊆ U → ∀ a L : ℝ, 0 < L →
      ∀ M : ℕ,
      (∀ t ∈ Icc a (a+L), ∀ z,
        Set.encard {x : Fin m → ℝ | x ∈ U ∧ F x+t • x=z ∧
          (fderiv ℝ (fun x => F x+t • x) x).det ≠ 0} ≤ M) →
      volume S * ENNReal.ofReal (L^(m+1)) ≤
        (ENNReal.ofReal C * M) * (volume.prod volume) (differentiableLineSweep F id S a L) := by
  obtain ⟨C,hC,h⟩ := regularMultiplicityLineSweep_direction_volume m
  refine ⟨C,hC,?_⟩
  intro F U hU hF S hS hSU a L hL M hM
  obtain ⟨G,hG,he⟩ := compact_contDiff_extension F U S hU hF hS hSU
  have hdG (x) := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hid (x : Fin m → ℝ) : HasFDerivAt id
      (ContinuousLinearMap.id ℝ (Fin m → ℝ)) x := hasFDerivAt_id x
  have hsweep : differentiableLineSweep G id S a L = differentiableLineSweep F id S a L := by
    apply Set.image_congr
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    simp only [(he x hx).self_of_nhds]
  have hh := h G id (fderiv ℝ G) (fun _ => ContinuousLinearMap.id ℝ (Fin m → ℝ))
    (hG.continuous_fderiv (by norm_num)) continuous_const hdG hid S hS a L hL M ?_
  · simpa only [image_id,hsweep] using hh
  · intro t ht z
    apply (Set.encard_le_encard ?_).trans (hM t ht z)
    intro x hx
    have hxG := (he x hx.1).self_of_nhds
    have hef : (fun y => G y+t • y) =ᶠ[𝓝 x] (fun y => F y+t • y) :=
      (he x hx.1).mono (fun y hy => by change G y+t • y=F y+t • y; rw [hy])
    refine ⟨hSU hx.1,by simpa only [hxG,id_eq] using hx.2.2,?_⟩
    rw [← hef.fderiv_eq]
    change (fderiv ℝ (G+t • id) x).det ≠ 0
    rw [((hdG x).add ((hid x).const_smul t)).fderiv]
    exact hx.2.1

/-- Inner regularity passes the same compact-source bound to the whole open
source. No summation over pieces and no target measurability premise are needed. -/
theorem open_regular_sweep_volume (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (Fin m → ℝ) → (Fin m → ℝ))
      (U : Set (Fin m → ℝ)), IsOpen U → ContDiffOn ℝ 1 F U →
      ∀ a L : ℝ, 0 < L → ∀ M : ℕ,
      (∀ t ∈ Icc a (a+L), ∀ z,
        Set.encard {x : Fin m → ℝ | x ∈ U ∧ F x+t • x=z ∧
          (fderiv ℝ (fun x => F x+t • x) x).det ≠ 0} ≤ M) →
      volume U * ENNReal.ofReal (L^(m+1)) ≤
        (ENNReal.ofReal C * M) * (volume.prod volume) (differentiableLineSweep F id U a L) := by
  obtain ⟨C,hC,h⟩ := open_regular_sweep_compact m
  refine ⟨C,hC,?_⟩
  intro F U hU hF a L hL M hM
  rw [hU.measure_eq_iSup_isCompact volume]
  simp only [ENNReal.iSup_mul]
  apply iSup_le
  intro S
  apply iSup_le
  intro hSU
  apply iSup_le
  intro hS
  apply (h F U hU hF S hS hSU a L hL M hM).trans
  apply mul_le_mul le_rfl _ zero_le zero_le
  apply measure_mono
  exact image_mono (Set.prod_mono hSU Subset.rfl)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.open_regular_sweep_compact
#print axioms KakeyaTwoScale.open_regular_sweep_volume
