module
public import KakeyaTwoScale.DualSlopeAvoidance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A preceding rational sums-differences estimate, with its multiplicative
constant and exponent explicit. This is a predicate, not an axiom. -/
def FiniteSDBound (R : Finset ℚ) (β C : ℝ) : Prop :=
  ∀ G : Finset ArithmeticPoint,
    Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint) →
    ∀ N : ℝ, 0 ≤ N → (∀ r ∈ R, ((G.image (arithmeticProjection r)).card : ℝ) ≤ N) →
      (G.card : ℝ) ≤ C*N^β

def affineSlope (b r : ℚ) : ℚ := b*(r+1)-1
def affinePoint (b : ℚ) (z : ArithmeticPoint) : ArithmeticPoint := (z.1+(b-1)*z.2,b*z.2)

theorem affine_projection (b r : ℚ) (z : ArithmeticPoint) :
    arithmeticProjection r (affinePoint b z) = arithmeticProjection (affineSlope b r) z := by
  dsimp [arithmeticProjection, affinePoint, affineSlope]
  ring

theorem affine_difference (b : ℚ) (z : ArithmeticPoint) :
    arithmeticProjection (-1) (affinePoint b z) = arithmeticProjection (-1) z := by
  dsimp [arithmeticProjection, affinePoint]
  ring

theorem affinePoint_injective (b : ℚ) (hb : b ≠ 0) : Function.Injective (affinePoint b) := by
  intro z w he
  have hy := congrArg Prod.snd he
  change b*z.2=b*w.2 at hy
  have hy' := mul_left_cancel₀ hb hy
  have hx := congrArg Prod.fst he
  dsimp [affinePoint] at hx
  apply Prod.ext _ hy'
  rw [hy'] at hx
  exact add_right_cancel hx

/-- Affine slope changes fixing -1 preserve BOTH the exponent and the exact
multiplicative constant of the preceding sums-differences estimate. -/
theorem FiniteSDBound.affine {R : Finset ℚ} {β C : ℝ} (h : FiniteSDBound R β C)
    (b : ℚ) (hb : b ≠ 0) : FiniteSDBound (R.image (affineSlope b)) β C := by
  intro G hdiff N hN hproj
  have hdiff' : Set.InjOn (arithmeticProjection (-1)) (↑(G.image (affinePoint b)) : Set ArithmeticPoint) := by
    intro x hx y hy he
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    rw [affine_difference,affine_difference] at he
    exact congrArg (affinePoint b) (hdiff hz hw he)
  have hp : ∀ r ∈ R, (((G.image (affinePoint b)).image (arithmeticProjection r)).card : ℝ) ≤ N := by
    intro r hr
    have he : (G.image (affinePoint b)).image (arithmeticProjection r) =
        G.image (arithmeticProjection (affineSlope b r)) := by
      rw [Finset.image_image]
      congr 1
      funext z
      exact affine_projection b r z
    rw [he]
    exact hproj _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
  have hh := h (G.image (affinePoint b)) hdiff' N hN hp
  have hc := Finset.card_image_of_injective G (affinePoint_injective b hb)
  simpa only [hc] using hh

/-- A whole finite proper slope set can avoid arbitrary finite exceptions
by ONE common affine change. This retains an actual preceding SD estimate. -/
theorem exists_affine_slopes_avoiding (R F : Finset ℚ)
    (hproper : ∀ r ∈ R, r ≠ -1) :
    ∃ b : ℚ, b ≠ 0 ∧ ∀ r ∈ R, affineSlope b r ∉ F ∧ affineSlope b r ≠ -1 := by
  let bad := insert 0 ((R.product F).image (fun p => (p.2+1)/(p.1+1)))
  obtain ⟨b,hb⟩ := Infinite.exists_notMem_finset bad
  have hb0 : b ≠ 0 := by intro he; subst b; simp [bad] at hb
  refine ⟨b,hb0,?_⟩
  intro r hr
  have hr1 : r+1 ≠ 0 := by intro he; apply hproper r hr; linarith
  constructor
  · intro hF
    apply hb
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(r,affineSlope b r),Finset.mem_product.mpr ⟨hr,hF⟩,?_⟩
    apply (div_eq_iff hr1).mpr
    dsimp [affineSlope]
    ring
  · intro he
    have hz : b*(r+1)=0 := by dsimp [affineSlope] at he; linarith
    exact mul_ne_zero hb0 hr1 hz

theorem FiniteSDBound.avoid {R : Finset ℚ} {β C : ℝ} (h : FiniteSDBound R β C)
    (hproper : ∀ r ∈ R, r ≠ -1) (F : Finset ℚ) :
    ∃ R' : Finset ℚ, FiniteSDBound R' β C ∧
      (∀ r ∈ R', r ≠ -1 ∧ r ∉ F) := by
  obtain ⟨b,hb,havoid⟩ := exists_affine_slopes_avoiding R F hproper
  refine ⟨R.image (affineSlope b),h.affine b hb,?_⟩
  intro r hr
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hr
  exact ⟨(havoid q hq).2,(havoid q hq).1⟩

/-- The starting exponent 2 is proved from two distinct rational projections. -/
theorem finiteSD_two_slopes (r s : ℚ) (hrs : r ≠ s) : FiniteSDBound {r,s} 2 1 := by
  intro G _ N hN hp
  have hc : G.card ≤ (G.image (arithmeticProjection r)).card * (G.image (arithmeticProjection s)).card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun z => (arithmeticProjection r z,arithmeticProjection s z))
    · intro z hz
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
    · intro z _ w _ he
      exact two_projections_injective hrs he
  have hr := hp r (by simp)
  have hs := hp s (by simp)
  have hc' : (G.card : ℝ) ≤ (G.image (arithmeticProjection r)).card * (G.image (arithmeticProjection s)).card := by
    exact_mod_cast hc
  norm_num only [Real.rpow_two, one_mul]
  have hmul := mul_le_mul hr hs (Nat.cast_nonneg _) hN
  nlinarith

/-- Select an entire preceding SD slope set with admissible duals, preserving
its exact exponent and constant. All finite forbidden slopes are respected. -/
theorem FiniteSDBound.with_duals {R : Finset ℚ} {β C : ℝ} (h : FiniteSDBound R β C)
    (hproper : ∀ r ∈ R, r ≠ -1) (a p s : ℚ)
    (ha : a ≠ 0) (hps : p ≠ s) (hp : p ≠ -1) (hs : s ≠ -1) (F : Finset ℚ) :
    ∃ R' : Finset ℚ, FiniteSDBound R' β C ∧
      ∀ r ∈ R', r ∉ F ∧ r ≠ p ∧ r ≠ s ∧ r ≠ -1 ∧
        dualDenominator a p s r ≠ 0 ∧ dualSlope a p s r ∉ F ∧
        dualSlope a p s r ≠ r ∧ dualSlope a p s r ≠ -1 ∧ dualSlope a p s r ≠ s := by
  obtain ⟨bad,hbad⟩ := finite_dual_slope_exceptions a p s ha hps hp hs F
  obtain ⟨R',hR',havoid⟩ := h.avoid hproper bad
  exact ⟨R',hR',fun r hr => hbad r (havoid r hr).2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.affine_projection
#print axioms KakeyaTwoScale.affine_difference
#print axioms KakeyaTwoScale.affinePoint_injective
#print axioms KakeyaTwoScale.FiniteSDBound.affine
#print axioms KakeyaTwoScale.exists_affine_slopes_avoiding
#print axioms KakeyaTwoScale.FiniteSDBound.avoid
#print axioms KakeyaTwoScale.finiteSD_two_slopes
#print axioms KakeyaTwoScale.FiniteSDBound.with_duals
