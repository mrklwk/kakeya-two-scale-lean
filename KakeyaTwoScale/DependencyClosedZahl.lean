module
public import KakeyaTwoScale.LargeScaleWedgeBands
public import KakeyaTwoScale.AllRadiusPublishedAssembly

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- The proved actual large-scale band construction, together with the
uniform bounded-scale estimate, supplies every positive-loss band contract. -/
theorem actual_dyadic_positive_bands (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1)
    (loss : ℝ) (hloss : 0<loss) :
    DyadicPositiveBandEstimate n k (zahlB (n+1) k) loss := by
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hknR : (k:ℝ)≤n+1 := by exact_mod_cast hkn
  obtain ⟨C,hC,hlarge⟩ := eventually_original_wedge_bands n k hk hkn loss hloss
  apply dyadic_positive_bands_of_eventual n k (by omega) (by omega) _ loss
    (zahlB_gt_one (by positivity) hkR hknR)
    (zahlB_le_n (by positivity) (by linarith) hknR) hloss.le
  refine ⟨C,hC.le,?_⟩
  filter_upwards [hlarge] with q hq
  intro hq1 N b u hu hsep j _hj
  exact hq hq1 N b u hu hsep j

/-- Dependency-closed published cylinder estimate: no Zahl, stopping,
visibility, partition, multilinear or geometric estimate is a hypothesis. -/
theorem published_zahl_cylinder_estimate (d k : ℕ) (hk : 2≤k) (hkd : k≤d) :
    PublishedZahlCylinderEstimate d k := by
  obtain ⟨n,rfl⟩ : ∃n, d=n+1 := ⟨d-1,by omega⟩
  exact published_zahl_of_positive_bands n k hk hkd
    (fun epsilon he => actual_dyadic_positive_bands n k hk hkd (epsilon/2) (by positivity))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_dyadic_positive_bands
#print axioms KakeyaTwoScale.published_zahl_cylinder_estimate
