module
public import KakeyaTwoScale.GraphWallBridge
public import Mathlib.Topology.Connected.Basic

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- The geometric core of the small-support obstruction: one off-wall point
and diameter less than the wall width force a connected support into one cell. -/
theorem small_connected_support_one_component {X : Type*} [PseudoMetricSpace X]
    (S Z : Set X) (hS : IsPreconnected S) {x : X} (hx : x ∈ S) (δ : ℝ)
    (hoff : x ∉ thickening δ Z) (hsmall : ∀ y ∈ S, dist x y < δ) :
    S ⊆ connectedComponentIn Zᶜ x := by
  apply hS.subset_connectedComponentIn hx
  intro y hy hyZ
  apply hoff
  exact mem_thickening_iff.mpr ⟨y,hyZ,hsmall y hy⟩

/-- Whole-set capture pays its diameter in addition to a witness's radius.
For a δ-cube this is sqrt(n)*δ; the output radius cannot simply be reused. -/
theorem whole_set_capture_radius {X : Type*} [PseudoMetricSpace X]
    (S Z : Set X) {x : X} (r d : ℝ)
    (hx : x ∈ thickening r Z) (hdiam : ∀ y ∈ S, dist y x ≤ d) :
    S ⊆ thickening (r+d) Z := by
  obtain ⟨z,hz,hxz⟩ := mem_thickening_iff.mp hx
  intro y hy
  apply mem_thickening_iff.mpr
  refine ⟨z,hz,?_⟩
  have h := add_lt_add_of_le_of_lt (hdiam y hy) hxz
  calc
    dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ < d+r := h
    _ = r+d := by ring

/-- To retain a whole connected cube outside an r-wall, find a point outside
an (r+diameter)-wall. The same cube belongs to one actual complementary cell. -/
theorem whole_set_offwall_with_margin {X : Type*} [PseudoMetricSpace X]
    (S Z : Set X) (hS : IsPreconnected S) {x : X} (hx : x ∈ S)
    (r d : ℝ) (hr : 0 < r) (hoff : x ∉ thickening (r+d) Z)
    (hdiam : ∀ y ∈ S, dist x y ≤ d) :
    S ⊆ connectedComponentIn Zᶜ x \ thickening r Z := by
  have hc := small_connected_support_one_component S Z hS hx (r+d) hoff
    (fun y hy => lt_of_le_of_lt (hdiam y hy) (by linarith))
  intro y hy
  refine ⟨hc hy,?_⟩
  intro hywall
  obtain ⟨z,hz,hyz⟩ := mem_thickening_iff.mp hywall
  apply hoff
  apply mem_thickening_iff.mpr
  refine ⟨z,hz,?_⟩
  have h := add_lt_add_of_le_of_lt (hdiam y hy) hyz
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ < d+r := h
    _ = r+d := by ring

/-- Radius update at a codimension increase, not at a cellular iteration. -/
def relativeRadiusBudget (A a b : ℝ) : ℕ → ℝ
  | 0 => A
  | i+1 => a * relativeRadiusBudget A a b i + b

/-- Uniform quantitative bound on a finite number of affine radius updates. -/
theorem relativeRadiusBudget_le (A a b : ℝ) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (i : ℕ) : relativeRadiusBudget A a b i ≤ a^i * (A + (i:ℝ)*b) := by
  induction i with
  | zero => simp [relativeRadiusBudget]
  | succ i ih =>
    have hap : 1 ≤ a^(i+1) := one_le_pow₀ ha
    have hb' : b ≤ a^(i+1)*b := by nlinarith
    calc
      _ = a * relativeRadiusBudget A a b i + b := rfl
      _ ≤ a * (a^i*(A+(i:ℝ)*b)) + b := add_le_add (mul_le_mul_of_nonneg_left ih (show 0 ≤ a by linarith)) le_rfl
      _ ≤ a^(i+1)*(A+((i+1:ℕ):ℝ)*b) := by
        rw [pow_succ] at hb' ⊢
        push_cast
        nlinarith

/-- With at most n codimension changes the radius remains independent of the
number of cubes and the cellular depth. This lemma assumes that count bound. -/
theorem relativeRadiusBudget_le_dimension (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 1 ≤ a) (hb : 0 ≤ b) {i n : ℕ} (hin : i ≤ n) :
    relativeRadiusBudget A a b i ≤ a^n * (A+(n:ℝ)*b) := by
  apply (relativeRadiusBudget_le A a b ha hb i).trans
  apply mul_le_mul
  · exact pow_le_pow_right₀ ha hin
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (show (i:ℝ) ≤ (n:ℝ) by exact_mod_cast hin) hb)
  · positivity
  · positivity

/-- The already-proved graph bridge plus a diameter payment is exactly an
affine update, a=1+L and b=L*w+d. This is algebra, not a TCI existence theorem. -/
theorem graph_radius_update (A L w d : ℝ) :
    A + L*(A+w) + d = (1+L)*A + (L*w+d) := by ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.small_connected_support_one_component
#print axioms KakeyaTwoScale.whole_set_capture_radius
#print axioms KakeyaTwoScale.relativeRadiusBudget_le
#print axioms KakeyaTwoScale.relativeRadiusBudget_le_dimension
#print axioms KakeyaTwoScale.graph_radius_update
#print axioms KakeyaTwoScale.whole_set_offwall_with_margin
