module
public import KakeyaTwoScale.HeightRescaling
public import KakeyaTwoScale.EuclideanCharts

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open NormedSpace

/-- Actual Euclidean unit realization of a horizontal graph slope. -/
def graphUnitDirection {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin (n+1)) := normalize (euclideanUnsplit i (1,v))

theorem graphVector_height {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ) :
    euclideanUnsplit i (1,v) i = 1 :=
  congrArg Prod.fst (euclideanSplit_unsplit i (1,v))

theorem graphVector_slope {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ) (j : Fin n) :
    euclideanUnsplit i (1,v) (i.succAbove j) = v j :=
  congrFun (congrArg Prod.snd (euclideanSplit_unsplit i (1,v))) j

theorem graphVector_ne_zero {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ) :
    euclideanUnsplit i (1,v) ≠ 0 := by
  intro he
  have hh := graphVector_height i v
  rw [he] at hh
  simp at hh

theorem graphUnitDirection_norm {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ) :
    ‖graphUnitDirection i v‖=1 := norm_normalize (graphVector_ne_zero i v)

theorem graphUnitDirection_chart {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ) :
    chartSlope i (graphUnitDirection i v)=v := by
  have hn : ‖euclideanUnsplit i (1,v)‖ ≠ 0 := norm_ne_zero_iff.mpr (graphVector_ne_zero i v)
  ext j
  simp only [chartSlope,graphUnitDirection,NormedSpace.normalize,PiLp.smul_apply,smul_eq_mul,graphVector_height,graphVector_slope,mul_one]
  field_simp

/-- A dimension-dependent rational bound suffices; constants precede scale. -/
theorem graphUnitDirection_height {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) :
    1/((n+2:ℝ)*(R+1)) ≤ graphUnitDirection i v i := by
  have hn : 0 < ‖euclideanUnsplit i (1,v)‖ := norm_pos_iff.mpr (graphVector_ne_zero i v)
  have hbound : ‖euclideanUnsplit i (1,v)‖ ≤ (n+2:ℝ)*(R+1) := by
    apply euclidean_norm_of_coordinate_bound _ _ (by positivity)
    apply (Fin.forall_iff_succAbove i (P:=fun j => |euclideanUnsplit i (1,v) j| ≤ R+1)).mpr
    constructor
    · rw [graphVector_height,abs_one]; linarith
    · intro j
      rw [graphVector_slope]
      have hj : |v j| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j
      linarith
  simp only [graphUnitDirection,NormedSpace.normalize,PiLp.smul_apply,smul_eq_mul,graphVector_height,mul_one]
  simpa only [one_div] using one_div_le_one_div_of_le hn hbound

/-- Rounding a bounded graph slope at radius at most one still has a uniform
positive height coordinate after exact Euclidean normalization. -/
theorem rounded_graphUnitDirection {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ)
    (R r : ℝ) (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (hr : 0 < r) (hrone : r ≤ 1) :
    ‖graphUnitDirection i (gridRound r v)‖=1 ∧
      1/((n+2:ℝ)*(R+2)) ≤ |graphUnitDirection i (gridRound r v) i| ∧
      dist v (chartSlope i (graphUnitDirection i (gridRound r v))) ≤ r := by
  refine ⟨graphUnitDirection_norm i _,?_,?_⟩
  · have hround : ‖gridRound r v‖ ≤ R+1 := by
      have hn := norm_le_norm_add_norm_sub v (gridRound r v)
      have hd := dist_gridRound_le hr v
      rw [dist_eq_norm] at hd
      linarith
    have hh := graphUnitDirection_height i (gridRound r v) (R+1) (by positivity) hround
    have he : R+1+1=R+2 := by ring
    rw [he] at hh
    exact hh.trans (le_abs_self _)
  · rw [graphUnitDirection_chart]
    exact dist_gridRound_le hr v

end KakeyaTwoScale
#print axioms KakeyaTwoScale.graphUnitDirection_norm
#print axioms KakeyaTwoScale.graphUnitDirection_chart
#print axioms KakeyaTwoScale.graphUnitDirection_height
#print axioms KakeyaTwoScale.rounded_graphUnitDirection
