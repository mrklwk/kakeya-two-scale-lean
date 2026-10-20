module
public import KakeyaTwoScale.SumDifference
public import KakeyaTwoScale.SlopeTree

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Proper, pairwise distinct rational triples. Validity is carried by every
node of the recursively constructed tree. -/
structure ProperSlopeTriple where
  r1 : ℚ
  r2 : ℚ
  r3 : ℚ
  proper1 : r1 ≠ -1
  proper2 : r2 ≠ -1
  proper3 : r3 ≠ -1
  ne12 : r1 ≠ r2
  ne13 : r1 ≠ r3
  ne23 : r2 ≠ r3
  deriving DecidableEq

def ProperSlopeTriple.forbidden (t : ProperSlopeTriple) : Finset ℚ := {t.r1,t.r2,t.r3}

section Construction
variable {R : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R β C)
  (hproper : ∀ r ∈ R, r ≠ -1)

def outerSlopeFamily (t : ProperSlopeTriple) : Finset ℚ :=
  Classical.choose (hSD.avoid hproper t.forbidden)

theorem outerSlopeFamily_spec (t : ProperSlopeTriple) :
    FiniteSDBound (outerSlopeFamily hSD hproper t) β C ∧
      ∀ r ∈ outerSlopeFamily hSD hproper t, r ≠ -1 ∧ r ∉ t.forbidden :=
  Classical.choose_spec (hSD.avoid hproper t.forbidden)

theorem outerSlopeFamily_distinct (t : ProperSlopeTriple) {r4 : ℚ}
    (hr : r4 ∈ outerSlopeFamily hSD hproper t) : r4 ≠ t.r1 ∧ r4 ≠ t.r2 ∧ r4 ≠ t.r3 := by
  have h := (outerSlopeFamily_spec hSD hproper t).2 r4 hr |>.2
  simpa [ProperSlopeTriple.forbidden] using h

theorem inner_exists (t : ProperSlopeTriple) (r4 : ℚ)
    (hr : r4 ∈ outerSlopeFamily hSD hproper t) :
    ∃ P : Finset ℚ, FiniteSDBound P β C ∧ ∀ r ∈ P,
      r ∉ insert r4 t.forbidden ∧ r ≠ t.r1 ∧ r ≠ t.r2 ∧ r ≠ -1 ∧
      dualDenominator (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ≠ 0 ∧
      dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ∉ insert r4 t.forbidden ∧
      dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ≠ r ∧
      dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ≠ -1 ∧
      dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ≠ t.r2 := by
  have hd := outerSlopeFamily_distinct hSD hproper t hr
  exact hSD.with_duals hproper _ _ _
    (cornerNu_coefficient_ne_zero _ _ _ hd.1 hd.2.2) t.ne12 t.proper1 t.proper2 _

def innerSlopeFamily (t : ProperSlopeTriple) (r4 : ℚ) : Finset ℚ :=
  if hr : r4 ∈ outerSlopeFamily hSD hproper t then
    Classical.choose (inner_exists hSD hproper t r4 hr)
  else ∅

theorem innerSlopeFamily_spec (t : ProperSlopeTriple) (r4 : ℚ)
    (hr : r4 ∈ outerSlopeFamily hSD hproper t) :
    FiniteSDBound (innerSlopeFamily hSD hproper t r4) β C ∧
      ∀ r ∈ innerSlopeFamily hSD hproper t r4,
      r ∉ insert r4 t.forbidden ∧ r ≠ t.r1 ∧ r ≠ t.r2 ∧ r ≠ -1 ∧
      dualDenominator (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ≠ 0 ∧
      dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ∉ insert r4 t.forbidden ∧
      dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ≠ r ∧
      dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ≠ -1 ∧
      dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r ≠ t.r2 := by
  unfold innerSlopeFamily
  rw [dite_eq_left hr]
  exact Classical.choose_spec (inner_exists hSD hproper t r4 hr)

def childSlopeTriple (t : ProperSlopeTriple) (r4 : ℚ)
    (hr4 : r4 ∈ outerSlopeFamily hSD hproper t) (r : ℚ)
    (hr : r ∈ innerSlopeFamily hSD hproper t r4) : ProperSlopeTriple := by
  have h := (innerSlopeFamily_spec hSD hproper t r4 hr4).2 r hr
  exact ⟨t.r2,r,dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2 r,
    t.proper2,h.2.2.2.1,h.2.2.2.2.2.2.2.1,
    h.2.2.1.symm,h.2.2.2.2.2.2.2.2.symm,h.2.2.2.2.2.2.1.symm⟩

def slopeChildren (t : ProperSlopeTriple) : Finset ProperSlopeTriple :=
  (outerSlopeFamily hSD hproper t).attach.biUnion fun r4 =>
    (innerSlopeFamily hSD hproper t r4.val).attach.image fun r =>
      childSlopeTriple hSD hproper t r4.val r4.property r.val r.property

def rootSlopeTriple : ProperSlopeTriple := ⟨0,1,2,by norm_num,by norm_num,by norm_num,
  by norm_num,by norm_num,by norm_num⟩

def nestedSlopeLevels : ℕ → Finset ProperSlopeTriple :=
  slopeTreeLevels {rootSlopeTriple} (slopeChildren hSD hproper)

def nodeSlopeSet (t : ProperSlopeTriple) : Finset ℚ :=
  t.forbidden ∪ outerSlopeFamily hSD hproper t ∪
    (outerSlopeFamily hSD hproper t).biUnion (fun r4 =>
      innerSlopeFamily hSD hproper t r4 ∪
      (innerSlopeFamily hSD hproper t r4).image
        (dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2))

/-- The complete global finite slope set for depth M. The construction
precedes G and N and depends only on the preceding SD data and M. -/
def nestedGlobalSlopes (M : ℕ) : Finset ℚ :=
  (Finset.range (M+1)).biUnion fun k =>
    (nestedSlopeLevels hSD hproper k).biUnion (nodeSlopeSet hSD hproper)

theorem nodeSlopeSet_subset_global (M k : ℕ) (hk : k ≤ M) (t : ProperSlopeTriple)
    (ht : t ∈ nestedSlopeLevels hSD hproper k) :
    nodeSlopeSet hSD hproper t ⊆ nestedGlobalSlopes hSD hproper M := by
  intro r hr
  exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_range.mpr (by omega),
    Finset.mem_biUnion.mpr ⟨t,ht,hr⟩⟩

theorem constructed_child_mem (k : ℕ) (t : ProperSlopeTriple)
    (ht : t ∈ nestedSlopeLevels hSD hproper k) (r4 : ℚ)
    (hr4 : r4 ∈ outerSlopeFamily hSD hproper t) (r : ℚ)
    (hr : r ∈ innerSlopeFamily hSD hproper t r4) :
    childSlopeTriple hSD hproper t r4 hr4 r hr ∈ nestedSlopeLevels hSD hproper (k+1) := by
  apply slopeTree_child_mem _ _ k ht
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨r4,hr4⟩,Finset.mem_attach _ _,?_⟩
  exact Finset.mem_image.mpr ⟨⟨r,hr⟩,Finset.mem_attach _ _,rfl⟩

theorem nodeSlopeSet_proper (t : ProperSlopeTriple) :
    ∀ r ∈ nodeSlopeSet hSD hproper t, r ≠ -1 := by
  intro r hr
  rcases Finset.mem_union.mp hr with hleft | hright
  · rcases Finset.mem_union.mp hleft with hbase | houter
    · simp only [ProperSlopeTriple.forbidden,Finset.mem_insert,Finset.mem_singleton] at hbase
      rcases hbase with rfl | rfl | rfl
      · exact t.proper1
      · exact t.proper2
      · exact t.proper3
    · exact ((outerSlopeFamily_spec hSD hproper t).2 r houter).1
  · obtain ⟨r4,hr4,hr⟩ := Finset.mem_biUnion.mp hright
    rcases Finset.mem_union.mp hr with hi | hd
    · exact ((innerSlopeFamily_spec hSD hproper t r4 hr4).2 r hi).2.2.2.1
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hd
      exact ((innerSlopeFamily_spec hSD hproper t r4 hr4).2 q hq).2.2.2.2.2.2.2.1

theorem nestedGlobalSlopes_proper (M : ℕ) :
    ∀ r ∈ nestedGlobalSlopes hSD hproper M, r ≠ -1 := by
  intro r hr
  obtain ⟨k,_,hr⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨t,_,hr⟩ := Finset.mem_biUnion.mp hr
  exact nodeSlopeSet_proper hSD hproper t r hr

/-- Every outer, inner and dual slope needed at a node is in the fixed global
set; hence one global projection bound supplies all later local bounds. -/
theorem nodeFamilies_subset_global (M k : ℕ) (hk : k ≤ M) (t : ProperSlopeTriple)
    (ht : t ∈ nestedSlopeLevels hSD hproper k) :
    outerSlopeFamily hSD hproper t ⊆ nestedGlobalSlopes hSD hproper M ∧
      ∀ r4 ∈ outerSlopeFamily hSD hproper t,
      innerSlopeFamily hSD hproper t r4 ⊆ nestedGlobalSlopes hSD hproper M ∧
      (innerSlopeFamily hSD hproper t r4).image
        (dualSlope (1-cornerCoefficient t.r1 t.r3 r4) t.r1 t.r2) ⊆ nestedGlobalSlopes hSD hproper M := by
  have hn := nodeSlopeSet_subset_global hSD hproper M k hk t ht
  constructor
  · intro r hr
    apply hn
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hr)
  · intro r4 hr4
    constructor
    · intro r hr
      apply hn
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r4,hr4,Finset.mem_union_left _ hr⟩)
    · intro r hr
      apply hn
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r4,hr4,Finset.mem_union_right _ hr⟩)

end Construction
end KakeyaTwoScale
#print axioms KakeyaTwoScale.outerSlopeFamily_spec
#print axioms KakeyaTwoScale.outerSlopeFamily_distinct
#print axioms KakeyaTwoScale.innerSlopeFamily_spec
#print axioms KakeyaTwoScale.childSlopeTriple
#print axioms KakeyaTwoScale.nodeSlopeSet_subset_global
#print axioms KakeyaTwoScale.constructed_child_mem

#print axioms KakeyaTwoScale.nodeSlopeSet_proper
#print axioms KakeyaTwoScale.nestedGlobalSlopes_proper
#print axioms KakeyaTwoScale.nodeFamilies_subset_global
