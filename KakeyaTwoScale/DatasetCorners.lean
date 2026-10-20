module
public import KakeyaTwoScale.NodeNuRefinement

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def sigmaPairSet {A : Type*} (Q : Finset (A × A)) : Finset (Σ _ : A, A) :=
  Q.map (verticalPairEquiv A).symm.toEmbedding

@[simp] theorem sigmaPairSet_card {A : Type*} (Q : Finset (A × A)) :
    (sigmaPairSet Q).card = Q.card := Finset.card_map _

@[simp] theorem mem_sigmaPairSet {A : Type*} (Q : Finset (A × A)) (x y : A) :
    Sigma.mk x y ∈ sigmaPairSet Q ↔ (x,y) ∈ Q := by
  simp [sigmaPairSet,verticalPairEquiv]

def selectedPairCorners (G : Finset ArithmeticPoint) (sl : List ℚ) (N : ℕ)
    (p s : ℚ) (U Q : Finset (ArithmeticPoint × ArithmeticPoint)) : Finset ArithmeticCorner :=
  let R := popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G
  let l := R.card/(2*N)
  wingCorners R
    (fun x => (balancedWing G (arithmeticProjection p) x l).filter (fun y => (x,y) ∈ U))
    (fun x => (balancedWing G (arithmeticProjection s) x l).filter (fun y => (x,y) ∈ Q))

/-- Exact retained corner mass from actual pair subsets. No independent
choices are made for the second wing after Q has been fixed. -/
theorem selectedPairCorners_retention (G : Finset ArithmeticPoint) (sl : List ℚ) (N : ℕ)
    (p s : ℚ) (hp : p ∈ sl) (hs : s ∈ sl)
    (hNp : (G.image (arithmeticProjection p)).card ≤ N)
    (hNs : (G.image (arithmeticProjection s)).card ≤ N)
    (U Q : Finset (ArithmeticPoint × ArithmeticPoint))
    (hU : U ⊆ rationalBalancedPairs G sl N p) (hQ : Q ⊆ rationalBalancedPairs G sl N s) :
    let l := (popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G).card/(2*N)
    l*U.card ≤ (selectedPairCorners G sl N p s U Q).card +
      l*((rationalBalancedPairs G sl N s).card-Q.card) := by
  let T := fun r => G.image (arithmeticProjection r)
  let R := popularRounds T arithmeticProjection 2 sl G
  let l := R.card/(2*N)
  let W := fun x => (balancedWing G (arithmeticProjection p) x l).filter (fun y => (x,y) ∈ U)
  have hQ' : sigmaPairSet Q ⊆ balancedVertical G T arithmeticProjection sl N s := by
    intro v hv
    have hx := hQ ((mem_sigmaPairSet Q v.1 v.2).mp hv)
    exact (mem_verticalPairSet _ v.1 v.2).mp hx
  have h := balanced_corner_retention G T arithmeticProjection sl N hp hs hNp hNs W
    (fun _ _ => Finset.filter_subset _ _) (sigmaPairSet Q) hQ'
  have he : wingEdges R W = sigmaPairSet U := by
    ext v
    constructor
    · intro hv
      obtain ⟨_,hw⟩ := Finset.mem_sigma.mp hv
      exact (mem_sigmaPairSet U v.1 v.2).mpr (Finset.mem_filter.mp hw).2
    · intro hv
      have hu := (mem_sigmaPairSet U v.1 v.2).mp hv
      have hv' := (mem_verticalPairSet _ v.1 v.2).mp (hU hu)
      obtain ⟨hc,hw⟩ := Finset.mem_sigma.mp hv'
      exact Finset.mem_sigma.mpr ⟨hc,Finset.mem_filter.mpr ⟨hw,hu⟩⟩
  change l*(wingEdges R W).card ≤ _ at h
  rw [he,sigmaPairSet_card,sigmaPairSet_card] at h
  simpa only [selectedPairCorners, rationalBalancedPairs, verticalPairSet_card,
    mem_sigmaPairSet] using h

 theorem selectedPairCorners_incidence (G : Finset ArithmeticPoint) (sl : List ℚ) (N : ℕ)
    (p s : ℚ) (U Q : Finset (ArithmeticPoint × ArithmeticPoint)) :
    selectedPairCorners G sl N p s U Q ⊆ arithmeticCorners G p s ∧
      ∀ c ∈ selectedPairCorners G sl N p s U Q, (c.1,c.2.1) ∈ U ∧ (c.1,c.2.2) ∈ Q := by
  constructor
  · apply wingCorners_subset_arithmetic
    · exact popularRounds_subset _ _ _ _ _
    · intro x _ y hy
      have h := balancedWing_subset G (arithmeticProjection p) x _ (Finset.mem_filter.mp hy).1
      simpa only [Finset.mem_filter] using h
    · intro x _ y hy
      have h := balancedWing_subset G (arithmeticProjection s) x _ (Finset.mem_filter.mp hy).1
      simpa only [Finset.mem_filter] using h
  · intro c hc
    obtain ⟨_,hl,hr⟩ := Finset.mem_sigma.mp hc |>.imp_right Finset.mem_product.mp
    exact ⟨(Finset.mem_filter.mp hl).2,(Finset.mem_filter.mp hr).2⟩

/-- The uniform selection predicate makes every constructed corner good;
there is no further corner deletion hidden in the final good-corner filter. -/
theorem selectedPairCorners_good (G : Finset ArithmeticPoint) (sl : List ℚ) (N : ℕ)
    (p s t : ℚ) (U Q V : Finset (ArithmeticPoint × ArithmeticPoint)) (L : ℕ)
    (hsmall : ∀ v ∈ U,
      (V.filter (fun w => (arithmeticProjection s w.1,arithmeticProjection t w.2) =
        (arithmeticProjection s v.1,arithmeticProjection t v.2))).card ≤ L) :
    goodCorners (selectedPairCorners G sl N p s U Q) V s t L =
      selectedPairCorners G sl N p s U Q := by
  apply Finset.filter_eq_self.mpr
  intro c hc
  have hu := (selectedPairCorners_incidence G sl N p s U Q).2 c hc |>.1
  have h := hsmall (c.1,c.2.1) hu
  simpa only [verticalDoubleFiber,Prod.mk.injEq] using h

/-- A numerical deletion budget suffices for positive actual corner mass. -/
theorem selectedPairCorners_mass (G : Finset ArithmeticPoint) (sl : List ℚ) (N : ℕ)
    (p s : ℚ) (hp : p ∈ sl) (hs : s ∈ sl)
    (hNp : (G.image (arithmeticProjection p)).card ≤ N)
    (hNs : (G.image (arithmeticProjection s)).card ≤ N)
    (U Q : Finset (ArithmeticPoint × ArithmeticPoint))
    (hU : U ⊆ rationalBalancedPairs G sl N p) (hQ : Q ⊆ rationalBalancedPairs G sl N s)
    (E : ℕ) (hE : E ≤ U.card)
    (hbudget : 2*((rationalBalancedPairs G sl N s).card-Q.card) ≤ E) :
    let l := (popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G).card/(2*N)
    l*E ≤ 2*(selectedPairCorners G sl N p s U Q).card := by
  have h := selectedPairCorners_retention G sl N p s hp hs hNp hNs U Q hU hQ
  dsimp only at *
  have h1 := Nat.mul_le_mul_left
    ((popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G).card/(2*N)) hE
  have h2 := Nat.mul_le_mul_left
    ((popularRounds (fun r => G.image (arithmeticProjection r)) arithmeticProjection 2 sl G).card/(2*N)) hbudget
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sigmaPairSet_card
#print axioms KakeyaTwoScale.mem_sigmaPairSet
#print axioms KakeyaTwoScale.selectedPairCorners_retention
#print axioms KakeyaTwoScale.selectedPairCorners_incidence
#print axioms KakeyaTwoScale.selectedPairCorners_good
#print axioms KakeyaTwoScale.selectedPairCorners_mass
