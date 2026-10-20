module
public import KakeyaTwoScale.GlobalDimension
public import KakeyaTwoScale.KakeyaSelectedFamily
public import KakeyaTwoScale.FiniteBroadZahl
public import KakeyaTwoScale.EnlargedCover
public import KakeyaTwoScale.SelectedScaleTransfer
public import KakeyaTwoScale.FourRegionBounds

@[expose] public section

open MeasureTheory Filter
noncomputable section
namespace KakeyaTwoScale

/-- Genuine Kakeya containment makes the set nonempty; no measurability or
closedness is required. -/
theorem ContainsUnitSegments.nonempty {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin (n+1)))} (hK : ContainsUnitSegments K) :
    K.Nonempty := by
  obtain ⟨b,hb⟩ := hK (graphUnitDirection 0 0) (graphUnitDirection_norm 0 0)
  exact ⟨b,by simpa using hb 0 (by simp)⟩

theorem parent_enlargement_shift (n : ℕ) :
    4*(n+2:ℝ)+1 ≤ (2:ℝ)^(4*(n+2)+1) := by
  exact_mod_cast (Nat.lt_two_pow_self : 4*(n+2)+1 < 2^(4*(n+2)+1)).le

set_option maxHeartbeats 800000 in
/-- The September 10 endpoint for genuine bounded Kakeya sets. The only
unproved mathematical input is the explicitly named Zahl estimate at half
the ambient dimension; all extraction, geometry and asymptotic data are built. -/
theorem bounded_kakeya_upperBox_of_zahl (n : ℕ) (hn : 3≤n)
    (K : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hK : ContainsUnitSegments K) (hbounded : Bornology.IsBounded K)
    (Z : ZahlCapsuleEstimate (n+1) ((n+1)/2)) :
    (597/1000:ℝ)*(n+1:ℕ) ≤ upperBoxDimension K := by
  classical
  let k := (n+1)/2
  let shift := 4*(n+2)+1
  have hk : 2≤k := by dsimp [k]; omega
  have hshift : 4*(n+2:ℝ)+1 ≤ (2:ℝ)^shift := parent_enlargement_shift n
  obtain ⟨R,cU,hR,hcU,hexists⟩ := bounded_kakeya_scale_data n K hK hbounded
  let data : ∀ q, KakeyaScaleData n K R q cU := fun q => Classical.choice (hexists q)
  let U : ℕ → ℝ := fun q => selectedMass n (data q)
  let P : ℕ → Prop := fun q => selectedBroad n k (data q)
  let L := tubeChartLength n
  have hL : 0<L := tubeChartLength_pos n
  have hLone : L≤1 := tubeChartLength_le_one n
  obtain ⟨C,hC,hvol⟩ := uniform_four_region_bounds n ((2:ℝ)^shift)
  let E : ℕ → ℝ := enlargedEnvelope K L⁻¹ C
  have hE (q : ℕ) : 0<E q := enlargedEnvelope_pos hbounded hK.nonempty L⁻¹ C (inv_pos.mpr hL) hC q
  have hdr (q : ℕ) : dyadicRadius (20*q)≤dyadicRadius q := by
    unfold dyadicRadius
    apply Real.exp_le_exp.mpr
    have hlog : 0≤Real.log 2 := (Real.log_pos (by norm_num)).le
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) q]
  have hregions (q : ℕ) := hvol 0 (data q).s L hL hLone K hbounded
    (data q).G (data q).trueBase (dyadicLatticeBase n q) (dyadicLatticeSlope n q)
    (dyadicRadius (20*q)) (dyadicRadius q) (Real.exp_pos _) (hdr q) (data q).level
    (data q).base_rounding (data q).axis_containment
  obtain ⟨cN,hcN,hN⟩ := selected_narrow_scale_transfer n k R shift hk hR.le hshift
  let p : ℝ := ((n+1:ℝ)-zahlB (n+1) k)/n
  have hp : 0≤p := broad_retained_mass_exponent_nonneg n k Z
  have htransfer : BroadTransfer (n+1:ℕ) k (fun q => E (20*q)) ∨
      NarrowTransfer (n+1:ℕ) k (fun q => E (20*q)) E := by
    apply transfer_dichotomy_of_physical_scales (n+1:ℕ) k p cU cN
      (fun q => E (20*q)) E U P hp hcU hcN
    · exact Eventually.of_forall fun q => ⟨(hE _).le,(hE _).le,by
        dsimp only [U,selectedMass]
        exact mul_nonneg (pow_nonneg (Real.exp_pos _).le n) (Nat.cast_nonneg _)⟩
    · exact Eventually.of_forall fun q => (data q).retained_mass
    · intro η hη
      obtain ⟨c,hc,hB⟩ := selected_broad_scale_transfer n k Z η hη
      refine ⟨c,hc,eventually_atTop.mpr ⟨1,?_⟩⟩
      intro q hq hP
      have hb := hB q hq K R cU (data q) (E (20*q)) hP (hregions q).1
      simpa only [Nat.cast_add,Nat.cast_one] using hb
    · apply eventually_atTop.mpr ⟨shift+1,?_⟩
      intro q hq hP
      exact hN q hq K cU (data q) (E (20*q)) (E q) (hE _) (hE _) hP
        (hregions q).1 (hregions q).2.1 (hregions q).2.2.1 (hregions q).2.2.2
  apply upperBoxDimension_lower_of_envelopes (n+1) (by omega) K hbounded
    (fun q => E (20*q)) E _ htransfer
  intro D _hD hcover
  exact hcover.enlarged_neighborhoodUpper L⁻¹ C (inv_pos.mpr hL) hC

/-- Upper Minkowski dimension in the usual all-positive-radii cover convention.
The analytic premise is exactly Zahl, with no residual extraction, volume,
branch, or dimension-convention hypotheses. -/
theorem kakeya_upperMinkowski_lower_of_zahl (N : ℕ) (hN : 4≤N)
    (Z : ZahlCapsuleEstimate N (N/2))
    (K : Set (EuclideanSpace ℝ (Fin N))) (hbounded : Bornology.IsBounded K)
    (hK : ∀ u : EuclideanSpace ℝ (Fin N), ‖u‖=1 → ∃ b,
      ∀ t ∈ Set.Icc (0:ℝ) 1, b+t • u ∈ K) :
    (597/1000:ℝ)*N ≤ limsup (openBallCoverEntropy K) (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [← upperBoxDimension_eq_radius_limsup hbounded]
  cases N with
  | zero => omega
  | succ n => exact bounded_kakeya_upperBox_of_zahl n (by omega) K hK hbounded Z

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ContainsUnitSegments.nonempty
#print axioms KakeyaTwoScale.bounded_kakeya_upperBox_of_zahl
#print axioms KakeyaTwoScale.kakeya_upperMinkowski_lower_of_zahl
