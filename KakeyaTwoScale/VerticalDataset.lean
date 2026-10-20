module
public import KakeyaTwoScale.BalancedCorners

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def verticalPairEquiv (A : Type*) : (Σ _ : A, A) ≃ A × A where
  toFun v := (v.1,v.2)
  invFun v := ⟨v.1,v.2⟩
  left_inv v := by cases v; rfl
  right_inv v := by cases v; rfl

def verticalPairSet {A : Type*} (V : Finset (Σ _ : A, A)) : Finset (A × A) :=
  V.map (verticalPairEquiv A).toEmbedding

@[simp] theorem verticalPairSet_card {A : Type*} (V : Finset (Σ _ : A, A)) :
    (verticalPairSet V).card = V.card := Finset.card_map _

@[simp] theorem mem_verticalPairSet {A : Type*} (V : Finset (Σ _ : A, A)) (x y : A) :
    (x,y) ∈ verticalPairSet V ↔ Sigma.mk x y ∈ V := by
  simp [verticalPairSet,verticalPairEquiv]

theorem verticalPairSet_filter {A : Type*} (V : Finset (Σ _ : A, A))
    (p : A × A → Prop) [DecidablePred p] :
    verticalPairSet (V.filter (fun v => p (v.1,v.2))) = (verticalPairSet V).filter p := by
  ext v
  rcases v with ⟨x,y⟩
  simp

/-- The actual pair encoding of a balanced rational vertical family. -/
def rationalBalancedPairs (G : Finset ArithmeticPoint) (slopes : List ℚ) (N : ℕ) (r : ℚ) :
    Finset (ArithmeticPoint × ArithmeticPoint) :=
  verticalPairSet (balancedVertical G (fun s => G.image (arithmeticProjection s))
    arithmeticProjection slopes N r)

theorem rationalBalancedPairs_incidence (G : Finset ArithmeticPoint) (slopes : List ℚ)
    (N : ℕ) (r : ℚ) {v : ArithmeticPoint × ArithmeticPoint}
    (hv : v ∈ rationalBalancedPairs G slopes N r) :
    v.1 ∈ G ∧ v.2 ∈ G ∧ arithmeticProjection r v.2 = arithmeticProjection r v.1 := by
  have hv' : Sigma.mk v.1 v.2 ∈ balancedVertical G (fun s => G.image (arithmeticProjection s))
      arithmeticProjection slopes N r := (mem_verticalPairSet _ _ _).mp hv
  obtain ⟨hcenter,hwing⟩ := Finset.mem_sigma.mp hv'
  have hc := popularRounds_subset (fun s => G.image (arithmeticProjection s))
    arithmeticProjection 2 slopes G hcenter
  have hw := balancedWing_subset G (arithmeticProjection r) v.1 _ hwing
  have hw' : v.2 ∈ G ∧ arithmeticProjection r v.2 = arithmeticProjection r v.1 := by
    simpa only [Finset.mem_filter] using hw
  exact ⟨hc,hw'⟩

theorem rationalBalancedPairs_card (G : Finset ArithmeticPoint) (slopes : List ℚ)
    (N : ℕ) {r : ℚ} (hr : r ∈ slopes) (hN : (G.image (arithmeticProjection r)).card ≤ N) :
    (rationalBalancedPairs G slopes N r).card =
      (popularRounds (fun s => G.image (arithmeticProjection s)) arithmeticProjection 2 slopes G).card *
      ((popularRounds (fun s => G.image (arithmeticProjection s)) arithmeticProjection 2 slopes G).card/(2*N)) := by
  rw [rationalBalancedPairs,verticalPairSet_card]
  exact balancedVertical_card G _ _ slopes N hr hN

theorem rationalBalancedPairs_equal_mass (G : Finset ArithmeticPoint) (slopes : List ℚ)
    (N : ℕ) {r s : ℚ} (hr : r ∈ slopes) (hs : s ∈ slopes)
    (hNr : (G.image (arithmeticProjection r)).card ≤ N)
    (hNs : (G.image (arithmeticProjection s)).card ≤ N) :
    (rationalBalancedPairs G slopes N r).card = (rationalBalancedPairs G slopes N s).card := by
  rw [rationalBalancedPairs_card G slopes N hr hNr,rationalBalancedPairs_card G slopes N hs hNs]

/-- Double-projection fibers have exactly the same size across the encoding. -/
theorem balanced_double_fiber_card (V : Finset (Σ _ : ArithmeticPoint, ArithmeticPoint))
    (s t : ℚ) (x y : ℚ) :
    ((verticalPairSet V).filter (fun v => arithmeticProjection s v.1 = x ∧ arithmeticProjection t v.2 = y)).card =
    (V.filter (fun v => arithmeticProjection s v.1 = x ∧ arithmeticProjection t v.2 = y)).card := by
  rw [← verticalPairSet_filter,verticalPairSet_card]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.verticalPairSet_card
#print axioms KakeyaTwoScale.mem_verticalPairSet
#print axioms KakeyaTwoScale.verticalPairSet_filter
#print axioms KakeyaTwoScale.rationalBalancedPairs_incidence
#print axioms KakeyaTwoScale.rationalBalancedPairs_card
#print axioms KakeyaTwoScale.rationalBalancedPairs_equal_mass
#print axioms KakeyaTwoScale.balanced_double_fiber_card
