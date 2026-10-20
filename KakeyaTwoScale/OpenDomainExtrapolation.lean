module
public import KakeyaTwoScale.CompactC1Extension
public import KakeyaTwoScale.PolynomialSweepExtrapolation

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace KakeyaTwoScale

/-- The extrapolated slice estimate needs smoothness only near a compact
source, while regular fibers are counted on the original open domain. -/
theorem open_regular_slice_compact (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F G : (Fin m → ℝ) → (Fin m → ℝ))
      (U : Set (Fin m → ℝ)), IsOpen U → ContDiffOn ℝ 1 F U → ContDiffOn ℝ 1 G U →
      ∀ (S : Set (Fin m → ℝ)), IsCompact S → S ⊆ U → ∀ a L t₀ : ℝ, 0 < L →
      ∀ M : ℕ,
      (∀ t ∈ Icc a (a+L), ∀ z,
        Set.encard {x : Fin m → ℝ | x ∈ U ∧ F x+t • G x=z ∧
          (fderiv ℝ (fun x => F x+t • G x) x).det ≠ 0} ≤ M) →
      volume ((fun x => F x+t₀ • G x) '' S) * ENNReal.ofReal L ≤
        (ENNReal.ofReal (C*(max 1 |(t₀-a)/L|)^m) * M) *
          (volume.prod volume) (differentiableLineSweep F G S a L) := by
  obtain ⟨C,hC,h⟩ := regularMultiplicityLineSweep_slice_volume m
  refine ⟨C,hC,?_⟩
  intro F G U hU hF hG S hS hSU a L t₀ hL M hM
  obtain ⟨F',hF',heF⟩ := compact_contDiff_extension F U S hU hF hS hSU
  obtain ⟨G',hG',heG⟩ := compact_contDiff_extension G U S hU hG hS hSU
  have hdF (x) := (hF'.differentiable (by norm_num) x).hasFDerivAt
  have hdG (x) := (hG'.differentiable (by norm_num) x).hasFDerivAt
  have he (x) (hx : x ∈ S) (t : ℝ) :
      (fun y => F' y+t • G' y) =ᶠ[𝓝 x] (fun y => F y+t • G y) := by
    filter_upwards [heF x hx,heG x hx] with y hFy hGy
    rw [hFy,hGy]
  have himage : (fun x => F' x+t₀ • G' x) '' S = (fun x => F x+t₀ • G x) '' S :=
    Set.image_congr (fun x hx => (he x hx t₀).self_of_nhds)
  have hsweep : differentiableLineSweep F' G' S a L = differentiableLineSweep F G S a L := by
    apply Set.image_congr
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    exact congrArg (fun z => (z,t)) (he x hx t).self_of_nhds
  have hh := h F' G' (fderiv ℝ F') (fderiv ℝ G')
    (hF'.continuous_fderiv (by norm_num)) (hG'.continuous_fderiv (by norm_num))
    hdF hdG S hS a L t₀ hL M ?_
  · simpa only [himage,hsweep] using hh
  · intro t ht z
    apply (Set.encard_le_encard ?_).trans (hM t ht z)
    intro x hx
    refine ⟨hSU hx.1,?_,?_⟩
    · exact (he x hx.1 t).self_of_nhds.symm.trans hx.2.2
    · rw [← (he x hx.1 t).fderiv_eq]
      change (fderiv ℝ (F'+t • G') x).det ≠ 0
      rw [((hdF x).add ((hdG x).const_smul t)).fderiv]
      exact hx.2.1

/-- Extension-volume control when the extrapolated slice parametrizes the
source by the identity. Inner regularity then avoids any assertion that images
of omitted null sets are null. This is an analytic ingredient, not the nested
algebraic-neighborhood or tube-covering recurrence. -/
theorem open_regular_extension_volume (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F G : (Fin m → ℝ) → (Fin m → ℝ))
      (U : Set (Fin m → ℝ)), IsOpen U → ContDiffOn ℝ 1 F U → ContDiffOn ℝ 1 G U →
      ∀ a L t₀ : ℝ, 0 < L →
      (∀ x ∈ U, F x+t₀ • G x=x) → ∀ M : ℕ,
      (∀ t ∈ Icc a (a+L), ∀ z,
        Set.encard {x : Fin m → ℝ | x ∈ U ∧ F x+t • G x=z ∧
          (fderiv ℝ (fun x => F x+t • G x) x).det ≠ 0} ≤ M) →
      volume U * ENNReal.ofReal L ≤
        (ENNReal.ofReal (C*(max 1 |(t₀-a)/L|)^m) * M) *
          (volume.prod volume) (differentiableLineSweep F G U a L) := by
  obtain ⟨C,hC,h⟩ := open_regular_slice_compact m
  refine ⟨C,hC,?_⟩
  intro F G U hU hF hG a L t₀ hL he M hM
  rw [hU.measure_eq_iSup_isCompact volume]
  simp only [ENNReal.iSup_mul]
  apply iSup_le
  intro S
  apply iSup_le
  intro hSU
  apply iSup_le
  intro hS
  have hh := h F G U hU hF hG S hS hSU a L t₀ hL M hM
  have himage : (fun x => F x+t₀ • G x) '' S=S := by
    convert (Set.image_id S) using 1
    exact Set.image_congr (fun x hx => he x (hSU hx))
  rw [himage] at hh
  apply hh.trans
  apply mul_le_mul le_rfl _ zero_le zero_le
  exact measure_mono (image_mono (Set.prod_mono hSU Subset.rfl))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.open_regular_slice_compact
#print axioms KakeyaTwoScale.open_regular_extension_volume
