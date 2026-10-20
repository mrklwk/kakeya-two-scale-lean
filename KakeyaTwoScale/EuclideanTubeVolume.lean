module
public import KakeyaTwoScale.ChartTubeContainment
public import KakeyaTwoScale.TubeChartSelection
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical

def tubeChartRadiusFactor (n : ℕ) : ℝ := tubeChartLength n/(2*Real.pi*(n+2:ℝ))

theorem tubeChartRadiusFactor_pos (n : ℕ) : 0 < tubeChartRadiusFactor n := by
  unfold tubeChartRadiusFactor
  exact div_pos (tubeChartLength_pos n) (by positivity)

theorem tubeChartRadiusFactor_margin (n : ℕ) : (n+2:ℝ)*tubeChartRadiusFactor n < 1 := by
  unfold tubeChartRadiusFactor
  have hL := tubeChartLength_le_one n
  have hpi := Real.pi_gt_three
  have hn : (0:ℝ)<n+2 := by positivity
  have he : (n+2:ℝ)*(tubeChartLength n/(2*Real.pi*(n+2:ℝ)))=
      ((n+2:ℝ)*tubeChartLength n)/(2*Real.pi*(n+2:ℝ)) := by ring
  rw [he]
  apply (div_lt_iff₀ (show 0 < 2*Real.pi*(n+2:ℝ) by positivity)).mpr
  nlinarith

/-- Ordinary Euclidean tube volume bound with all orientation, common-height,
rounding, strict containment and volume changes proved. The positional bound
is the source's fixed bounded-region hypothesis. Constants precede r and G.
The direction hypothesis is the exact sign-invariant angular separation. -/
theorem separated_euclidean_tubes_volume (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ {J : Type*} (G : Finset J), G.Nonempty →
      ∀ b u : J → EuclideanSpace ℝ (Fin (n+1)),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) →
      ProjectiveSeparated G u r →
      C*r^n*(G.card:ℝ)^a ≤ volume.real (⋃ j ∈ G, euclideanTube (b j) (u j) r) := by
  obtain ⟨C,hC,hgraph⟩ := separated_graph_tubes_volume n
  obtain ⟨M,hM,hselect⟩ := finite_tube_chart_selection n R hR
  let L := tubeChartLength n
  let eta := tubeChartRadiusFactor n
  have hL : 0 < L := tubeChartLength_pos n
  have heta : 0 < eta := tubeChartRadiusFactor_pos n
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  refine ⟨C*L*eta^n/(M:ℝ)^a,by positivity,?_⟩
  intro r hr J G hG b u hb hu hsep
  obtain ⟨S,hSG,hS,hcard,i,reverse,s,hinterval⟩ := hselect G hG b u hb hu
  let b' := fun j => orientedBase reverse (b j) (u j)
  let u' := fun j => orientedDirection reverse (u j)
  let bg := fun j => chartIntercept i (b' j) (u' j) s
  let vg := fun j => L • chartSlope i (u' j)
  have hunit (j) (hj : j ∈ S) : ‖u' j‖=1 := (orientedDirection_norm reverse _).trans (hu j (hSG hj))
  have hsepg : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → eta*r ≤ dist (vg j) (vg k) := by
    intro j hj k hk hjk
    have hs := oriented_angle_separation reverse (u j) (u k) r (hsep j (hSG hj) k (hSG hk) hjk).1
    have hh := rescaled_chartSlope_separation i (u' j) (u' k) (hunit j hj) (hunit k hk)
      (hinterval j hj).1 (hinterval k hk).1 hL hs
    apply le_trans ?_ hh
    dsimp [eta,tubeChartRadiusFactor,L]
    have hd : 0 < Real.pi*(n+2:ℝ) := by positivity
    have hnum : 0 < tubeChartLength n*r := mul_pos (tubeChartLength_pos n) hr
    field_simp
    nlinarith [tubeChartLength_pos n]
  let E := ⋃ j ∈ G, euclideanTube (b j) (u j) r
  have hE : MeasurableSet E := by
    exact Finset.measurableSet_biUnion _ (fun j _ => (isOpen_euclideanTube (b j) (u j) r).measurableSet)
  let F := euclideanUnsplit i ⁻¹' E
  have hF : MeasurableSet F := hE.preimage (euclideanUnsplit_measurePreserving i).measurable
  have hvolF : volume F=volume E := (euclideanUnsplit_measurePreserving i).measure_preimage hE.nullMeasurableSet
  have hfin : volume (heightAffine s L ⁻¹' F) ≠ ⊤ := by
    rw [volume_heightAffine_preimage s hL F hF,hvolF]
    exact ENNReal.mul_ne_top (by finiteness) (euclideanTube_union_finite G b u r)
  have hsub : (⋃ j ∈ S, horizontalTube (bg j) (vg j) (eta*r)) ⊆ heightAffine s L ⁻¹' F := by
    intro p hp
    obtain ⟨j,hj,hp⟩ := Set.mem_iUnion₂.mp hp
    have hmargin : (n+2:ℝ)*(eta*r) < r := by
      have hh := mul_lt_mul_of_pos_right (tubeChartRadiusFactor_margin n) hr
      dsimp [eta]; nlinarith only [hh]
    have hh := chart_graph_inside_euclideanTube i (b' j) (u' j)
      (hinterval j hj).1 hL.le (mul_nonneg heta.le hr.le) hmargin
      (hinterval j hj).2.1 (hinterval j hj).2.2 hp
    change euclideanUnsplit i (heightAffine s L p) ∈ E
    apply Set.mem_iUnion₂.mpr
    refine ⟨j,hSG hj,?_⟩
    rwa [oriented_tube_eq] at hh
  have hv := (hgraph (eta*r) (mul_pos heta hr) S hS bg vg hsepg).trans (measureReal_mono hsub hfin)
  rw [volume_real_heightAffine_preimage s hL F hF] at hv
  have hrealF : volume.real F=volume.real E := congrArg ENNReal.toReal hvolF
  rw [hrealF] at hv
  have hmass : (G.card:ℝ)^a ≤ (M:ℝ)^a*(S.card:ℝ)^a := by
    rw [← Real.mul_rpow hM'.le (Nat.cast_nonneg _)]
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num [a])
    exact_mod_cast hcard
  have hv' := mul_le_mul_of_nonneg_left hv hL.le
  have hinv : L*(L⁻¹*volume.real E)=volume.real E := by field_simp
  rw [hinv,mul_pow] at hv'
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ C*L*eta^n*r^n by positivity)
  have hfinal : C*L*eta^n*r^n*(G.card:ℝ)^a ≤ volume.real E*(M:ℝ)^a := by
    have hh := mul_le_mul_of_nonneg_right hv' (show 0 ≤ (M:ℝ)^a by positivity)
    nlinarith only [hm,hh]
  have hdiv := (div_le_iff₀ (show 0 < (M:ℝ)^a by positivity)).mpr hfinal
  convert hdiv using 1; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tubeChartRadiusFactor_pos
#print axioms KakeyaTwoScale.tubeChartRadiusFactor_margin
#print axioms KakeyaTwoScale.separated_euclidean_tubes_volume
