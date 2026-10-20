module
public import KakeyaTwoScale.CellVolume
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-! Actual half-open horizontal grids. The metric on `Fin n → ℝ` is the sup
metric; no identification with Euclidean distance is silently made. -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def gridIndex {n : ℕ} (r : ℝ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => ⌊x i / r⌋

def gridCell {n : ℕ} (r : ℝ) (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  {x | ∀ i, r * k i ≤ x i ∧ x i < r * (k i + 1)}

theorem mem_gridCell_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    (x : Fin n → ℝ) (k : Fin n → ℤ) :
    x ∈ gridCell r k ↔ gridIndex r x = k := by
  simp only [gridCell, Set.mem_ofPred_eq, gridIndex, funext_iff, Int.floor_eq_iff]
  congr! 1
  rw [le_div_iff₀ hr, div_lt_iff₀ hr]
  ring_nf

theorem mem_own_gridCell {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Fin n → ℝ) :
    x ∈ gridCell r (gridIndex r x) := (mem_gridCell_iff hr x _).2 rfl

theorem gridCell_disjoint {n : ℕ} {r : ℝ} (hr : 0 < r)
    {k l : Fin n → ℤ} (hkl : k ≠ l) : Disjoint (gridCell r k) (gridCell r l) := by
  apply Set.disjoint_left.2
  intro x hx hy
  exact hkl ((mem_gridCell_iff hr x k).1 hx |>.symm.trans ((mem_gridCell_iff hr x l).1 hy))

theorem measurableSet_gridCell {n : ℕ} (r : ℝ) (k : Fin n → ℤ) :
    MeasurableSet (gridCell r k) := by
  have he : gridCell r k = ⋂ i, {x : Fin n → ℝ | r * k i ≤ x i ∧ x i < r * (k i + 1)} := by
    ext x; simp [gridCell]
  rw [he]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_Ico.preimage (measurable_pi_apply i))

/-- Integer scale ratios give a deterministic parent, independent of the point
chosen in the fine cell. This includes every dyadic scale ratio. -/
theorem gridIndex_mul_nat {n : ℕ} (r : ℝ) (m : ℕ) (x : Fin n → ℝ) :
    gridIndex (r * m) x = fun i => gridIndex r x i / (m : ℤ) := by
  funext i
  simp only [gridIndex, ← div_div, Int.floor_div_natCast]

theorem gridCell_nested {n : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hm : 0 < m) (k : Fin n → ℤ) :
    gridCell r k ⊆ gridCell (r*m) (fun i => k i / (m : ℤ)) := by
  intro x hx
  apply (mem_gridCell_iff (mul_pos hr (Nat.cast_pos.mpr hm)) x _).2
  rw [gridIndex_mul_nat, (mem_gridCell_iff hr x k).1 hx]

/-- Uniform coordinate bounds imply a genuine sup-distance diameter estimate. -/
theorem gridCell_dist_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {k : Fin n → ℤ} {x y : Fin n → ℝ}
    (hx : x ∈ gridCell r k) (hy : y ∈ gridCell r k) : dist x y ≤ r := by
  apply (dist_pi_le_iff hr).2
  intro i
  rw [Real.dist_eq, abs_le]
  have hx' := hx i
  have hy' := hy i
  constructor <;> nlinarith

theorem volume_gridCell {n : ℕ} (r : ℝ) (k : Fin n → ℤ) :
    volume (gridCell r k) = ENNReal.ofReal r ^ n := by
  have he : gridCell r k = Set.univ.pi (fun i => Set.Ico (r*k i) (r*(k i+1))) := by
    ext x
    simp [gridCell, Set.mem_pi]
  rw [he, volume_pi_pi]
  simp only [Real.volume_Ico]
  have hsub : ∀ i : Fin n, r*(k i+1)-r*k i = r := by intro i; ring
  simp [hsub]

/-- A complete coarse cell that contains a child axis lies in its rounded
parent tube. Parent rounding and cell diameter are now actual geometric bounds. -/
theorem own_gridCell_inside_parent {n : ℕ} {r : ℝ} (hr : 0 < r)
    (b v bP vP : Fin n → ℝ) (t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hb : dist b bP ≤ r) (hv : dist v vP ≤ r) :
    gridCell r (gridIndex r (segmentPoint b v t)) ⊆
      (fun x => (t,x)) ⁻¹' horizontalTube bP vP (3*r) := by
  apply cells_inside_parent b v bP vP r t ht hb hv
  intro x hx
  exact gridCell_dist_le hr.le hx (mem_own_gridCell hr _)
/-- Rounding is a concrete function, not an assumed nearby parameter. -/
def gridRound {n : ℕ} (r : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => r * gridIndex r x i

theorem gridRound_mem {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Fin n → ℝ) :
    gridRound r x ∈ gridCell r (gridIndex r x) := by
  intro i
  constructor
  · exact le_rfl
  · change r * (gridIndex r x i : ℝ) < r * ((gridIndex r x i : ℝ) + 1)
    nlinarith

theorem dist_gridRound_le {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Fin n → ℝ) :
    dist x (gridRound r x) ≤ r :=
  gridCell_dist_le hr.le (mem_own_gridCell hr x) (gridRound_mem hr x)

/-- Both the parent axis and the entire horizontal cell are explicitly
constructed. No parent-distance or point-to-cell hypothesis remains. -/
theorem gridCell_inside_rounded_parent {n : ℕ} {r : ℝ} (hr : 0 < r)
    (b v : Fin n → ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    gridCell r (gridIndex r (segmentPoint b v t)) ⊆
      (fun x => (t,x)) ⁻¹' horizontalTube (gridRound r b) (gridRound r v) (3*r) :=
  own_gridCell_inside_parent hr b v _ _ t ht (dist_gridRound_le hr b) (dist_gridRound_le hr v)

/-- Disjoint-cell counting is exactly horizontal Lebesgue volume. -/
theorem volume_gridCell_union {n : ℕ} {r : ℝ} (hr : 0 < r)
    (indices : Finset (Fin n → ℤ)) :
    volume (⋃ k ∈ indices, gridCell r k) =
      (indices.card : ℝ≥0∞) * ENNReal.ofReal r ^ n := by
  rw [measure_biUnion_finset]
  · simp [volume_gridCell]
  · intro k _ l _ hkl
    exact gridCell_disjoint hr hkl
  · intro k _
    exact measurableSet_gridCell r k

end KakeyaTwoScale
#print axioms KakeyaTwoScale.gridCell_nested
#print axioms KakeyaTwoScale.volume_gridCell
#print axioms KakeyaTwoScale.own_gridCell_inside_parent

#print axioms KakeyaTwoScale.gridCell_inside_rounded_parent
#print axioms KakeyaTwoScale.volume_gridCell_union
