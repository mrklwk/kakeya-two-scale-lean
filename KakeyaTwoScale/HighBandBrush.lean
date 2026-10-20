module
public import KakeyaTwoScale.RefinedBrushPieces
public import KakeyaTwoScale.ExtensionPlane
public import KakeyaTwoScale.BrushVolumeTools

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Actual high-band brush volume. The plane net, extension dimensions,
quarter pieces, plane-weight caps and overlap are all constructed internally.
The constants precede both scales and the complete finite tube family. -/
theorem high_band_brush_volume (n k : ℕ) (R B C : ℝ)
    (hR : 0 ≤ R) (hB : 0 < B) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
        (p : EuclideanSpace ℝ (Fin (n+1))),
      Module.finrank ℝ H=k+1 → ∀ r s : ℝ, 0 < r → r ≤ 1 → 0 < s →
      r ≤ s/(8*Real.pi) →
      ∀ {J : Type*} (G : Finset J) (b u : J → EuclideanSpace ℝ (Fin (n+1))) (w : J → ℝ),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ j ∈ G, s ≤ planeAngle H (u j) ∧ planeAngle H (u j) ≤ 2*s) →
      (∀ j ∈ G, (euclideanTube (b j) (u j) r ∩
        Metric.thickening (C*r) (affinePlane H p)).Nonempty) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      c*r^n*(r^(k+1))^theta*(∑ j ∈ G, w j) ≤
        volume.real (⋃ j ∈ G, euclideanTube (b j) (u j) r) := by
  obtain ⟨N,hnet⟩ := construct_angle_brush_pieces_with_net
    (X:=EuclideanSpace ℝ (Fin (n+1))) (C+1) (by linarith)
  obtain ⟨cv,hcv,hvol⟩ := quarter_plane_weighted_volume n (k+1) R B Real.pi hR hB Real.pi_pos.le
  refine ⟨cv/(N+1:ℝ),by positivity,?_⟩
  intro H p hdim r s hr hrone hs hrs J G b u w hb hu hw ha hmeet hcap
  by_cases hne : G.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  have henc : ∀ j ∈ G, ∃ t ∈ Set.Icc (0:ℝ) 1,
      ‖normalProjection H (segmentPoint (b j) (u j) t-p)‖ ≤ (C+1)*r := by
    intro j hj
    have hm := hmeet j hj
    rw [euclideanTube_eq_thickening] at hm
    obtain ⟨t,ht,he⟩ := tube_plane_encounter H p (b j) (u j) r (C*r) hm
    exact ⟨t,ht,by nlinarith only [he]⟩
  obtain ⟨net,assign,I,hsub,hassign,hunit,hclose,hI,hover⟩ :=
    hnet H p G b u r s hne hr hs hrs (fun j hj => ⟨hu j hj,ha j hj⟩) henc
  let pieces := assignedTubePieces G assign b u I r
  let W := assignedWeight G assign w
  have hpieces : ∀ j ∈ net, MeasurableSet (pieces j) := by
    intro j _
    exact Finset.measurableSet_biUnion _ (fun l _ => Metric.isOpen_thickening.measurableSet)
  have hpiecesub : ∀ j ∈ net, pieces j ⊆ ⋃ l ∈ G, euclideanTube (b l) (u l) r := by
    intro j hj x hx
    obtain ⟨l,hl,hx⟩ := Set.mem_iUnion₂.mp hx
    have hlG := (Finset.mem_filter.mp hl).1
    exact Set.mem_iUnion₂.mpr ⟨l,hlG,quarter_piece_subset_tube (b l) (u l) (I l) r (hI l hlG) hx⟩
  have hpiecevol : ∀ j ∈ net, cv*r^n*(r^(k+1))^theta*W j ≤ volume.real (pieces j) := by
    intro j hj
    let L := extensionSubspace H (normalDirection H (u j))
    have hdimL : Module.finrank ℝ L=(k+1)+1 := by
      rw [extensionSubspace_finrank H _ (hunit j hj).2 (hunit j hj).1,hdim]
    let S := G.filter (fun l => assign l=j)
    have hSG : S ⊆ G := Finset.filter_subset _ _
    have hangle : ∀ l ∈ S, planeAngle L (u l) ≤ Real.pi*r := by
      intro l hl
      obtain ⟨hlG,hlj⟩ := Finset.mem_filter.mp hl
      apply extension_plane_angle_bound H _ _ r (hu l hlG)
      have hv := planeAngle_speed_bounds H (u l) (hu l hlG)
      have hvpos : 0 < ‖normalProjection H (u l)‖ := by
        have hp : 0 < (2/Real.pi)*s := by positivity
        exact hp.trans_le ((mul_le_mul_of_nonneg_left (ha l hlG).1 (by positivity)).trans hv.1)
      have hcl := hclose l hlG
      rw [hlj] at hcl
      exact normal_velocity_band_approximation H (u l) (normalDirection H (u j)) r s hs hr.le
        hvpos (hv.2.trans (ha l hlG).2) hcl
    exact hvol L hdimL r hr hrone S b u w I (fun l hl => hI l (hSG hl))
      (fun l hl => hb l (hSG hl)) (fun l hl => hu l (hSG hl))
      (fun l hl => hw l (hSG hl)) hangle
      (angular_weight_cap_subset G S hSG u w r B hw hcap)
  have hsum : cv*r^n*(r^(k+1))^theta*(∑ j ∈ G, w j) ≤
      (N+1:ℝ)*volume.real (⋃ j ∈ G, euclideanTube (b j) (u j) r) := by
    calc
      _ = ∑ j ∈ net, cv*r^n*(r^(k+1))^theta*W j := by
        rw [← Finset.mul_sum,assignedWeight_total G net assign w hassign]
      _ ≤ ∑ j ∈ net, volume.real (pieces j) := Finset.sum_le_sum hpiecevol
      _ ≤ _ := piece_volume_sum_le_container volume _ (euclideanTube_union_finite G b u r)
        net pieces (N+1:ℝ) (by positivity) hpieces hpiecesub
        (fun x => (hover x).trans (by norm_num))
  have hn : 0 < (N+1:ℝ) := by positivity
  rw [show cv/(N+1:ℝ)*r^n*(r^(k+1))^theta*(∑ j ∈ G, w j)=
    (cv*r^n*(r^(k+1))^theta*(∑ j ∈ G, w j))/(N+1:ℝ) by ring]
  exact (div_le_iff₀ hn).mpr (by nlinarith only [hsum])

end KakeyaTwoScale
#print axioms KakeyaTwoScale.high_band_brush_volume
