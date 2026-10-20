module
public import KakeyaTwoScale.FixedParents
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X J : Type*} [MeasurableSpace X]

 def membershipCount (family : Finset J) (sets : J → Set X) (x : X) : ℝ :=
  ∑ j ∈ family, (sets j).indicator (fun _ => (1:ℝ)) x

 theorem integrable_membershipCount (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (sets : J → Set X)
    (hm : ∀ j ∈ family, MeasurableSet (sets j)) :
    Integrable (membershipCount family sets) μ := by
  exact integrable_finsetSum family (fun j hj => (integrable_const (1:ℝ)).indicator (hm j hj))

 omit [MeasurableSpace X] in
 theorem membershipCount_eq_card [DecidableEq J]
    (family : Finset J) (sets : J → Set X) (x : X) :
    membershipCount family sets x =
      ((family.filter fun j => x ∈ sets j).card : ℝ) := by
  classical
  simp [membershipCount, Set.indicator]

 theorem integrable_card_filter [DecidableEq J]
    (μ : Measure X) [IsFiniteMeasure μ] (family : Finset J) (sets : J → Set X)
    (hm : ∀ j ∈ family, MeasurableSet (sets j)) :
    Integrable (fun x => ((family.filter fun j => x ∈ sets j).card : ℝ)) μ := by
  classical
  have he : (fun x => ((family.filter fun j => x ∈ sets j).card : ℝ)) =
      membershipCount family sets := by
    funext x
    exact (membershipCount_eq_card family sets x).symm
  rw [he]
  exact integrable_membershipCount μ family sets hm

 theorem integral_membershipCount (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (sets : J → Set X)
    (hm : ∀ j ∈ family, MeasurableSet (sets j)) :
    (∫ x, membershipCount family sets x ∂μ) = ∑ j ∈ family, μ.real (sets j) := by
  unfold membershipCount
  rw [integral_finsetSum family (fun j hj => (integrable_const (1:ℝ)).indicator (hm j hj))]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_indicator_one (hm j hj)

/-- The simultaneous-parameter averaging step for progression sets.
The probability measure can be Lebesgue measure restricted to the unit square. -/
theorem common_parameter_of_measure_lower (μ : Measure X) [IsProbabilityMeasure μ]
    (family : Finset J) (sets : J → Set X) (c : ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (sets j))
    (hc : ∀ j ∈ family, c ≤ μ.real (sets j)) :
    ∃ x : X, c*family.card ≤ membershipCount family sets x := by
  obtain ⟨x,hx⟩ := exists_integral_le (integrable_membershipCount μ family sets hm)
  refine ⟨x, le_trans ?_ hx⟩
  rw [integral_membershipCount μ family sets hm]
  calc
    c*family.card = ∑ _j ∈ family, c := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum hc

/-- Integrate the fixed-parent low-cell bound over heights. Integrability is
explicit, preventing totalized Bochner integrals from hiding a missing step. -/
theorem FixedParents.integrated_low_cells_loss
    {Child Parent Cell : Type*} [DecidableEq Child] [DecidableEq Parent]
    (F : FixedParents Child Parent) (μ : Measure X)
    (cells : X → Finset Cell) (selected : X → Cell → Finset Child)
    (covering : X → Cell → Finset Parent) (M : ℝ)
    (hs : ∀ t c, c ∈ cells t → selected t c ⊆ F.children)
    (hp : ∀ t c, c ∈ cells t → covering t c ⊆ F.parents)
    (hcover : ∀ t c, c ∈ cells t → ∀ x ∈ selected t c, F.assign x ∈ covering t c)
    (hlow : ∀ t c, c ∈ cells t → F.weight*(covering t c).card ≤ M)
    (hmass : Integrable (fun t => ∑ c ∈ cells t, F.fineCellVolume*(selected t c).card) μ)
    (hvol : Integrable (fun t => F.coarseCellVolume*(cells t).card) μ) :
    (∫ t, ∑ c ∈ cells t, F.fineCellVolume*(selected t c).card ∂μ) ≤
      2*M*(∫ t, F.coarseCellVolume*(cells t).card ∂μ) := by
  rw [← integral_const_mul]
  apply integral_mono hmass (hvol.const_mul _)
  intro t
  exact F.low_cells_loss (cells t) (selected t) (covering t) M
    (hs t) (hp t) (hcover t) (hlow t)
end KakeyaTwoScale
#print axioms KakeyaTwoScale.integral_membershipCount
#print axioms KakeyaTwoScale.common_parameter_of_measure_lower
#print axioms KakeyaTwoScale.FixedParents.integrated_low_cells_loss
