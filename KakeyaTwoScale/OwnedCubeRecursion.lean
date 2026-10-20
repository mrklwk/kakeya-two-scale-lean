module
public import KakeyaTwoScale.GrainTreeBookkeeping

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Full original cube weights, with no chart-fragment replacement. -/
def ownedCubeMass {C : Type*} (w : C → ℝ) (S : Finset C) : ℝ := ∑ c ∈ S, w c

theorem ownedCubeMass_nonneg {C : Type*} (w : C → ℝ) (hw : ∀ c, 1 ≤ w c)
    (S : Finset C) : 0 ≤ ownedCubeMass w S :=
  Finset.sum_nonneg (fun c _ => (by norm_num : (0:ℝ)≤1).trans (hw c))

theorem ownedCubeMass_floor {C : Type*} [DecidableEq C] (w : C → ℝ)
    (hw : ∀ c, 1 ≤ w c) (S : Finset C) (hS : S.Nonempty) : 1 ≤ ownedCubeMass w S := by
  obtain ⟨c,hc⟩ := hS
  exact (hw c).trans (Finset.single_le_sum
    (fun d _ => (by norm_num : (0:ℝ)≤1).trans (hw d)) hc)

/-- A nonempty child owning only parent cubes and contracting full original
mass has strictly fewer cubes. This supplies a concrete well-founded measure. -/
theorem owned_child_card_lt {C : Type*} [DecidableEq C]
    (w : C → ℝ) (hw : ∀ c, 1 ≤ w c) {S T : Finset C}
    (hT : T.Nonempty) (hsub : T ⊆ S) {q : ℝ} (hq : q < 1)
    (hcontract : ownedCubeMass w T ≤ q*ownedCubeMass w S) : T.card < S.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro he
  subst T
  have hp := ownedCubeMass_floor w hw S hT
  nlinarith

/-- The child relation is well founded on actual cube subsets. Its mass
contraction and nonempty-child assumptions are explicit split properties. -/
theorem owned_children_wellFounded {C : Type*} [DecidableEq C]
    (w : C → ℝ) (hw : ∀ c, 1 ≤ w c)
    (children : Finset C → Finset (Finset C)) {q : ℝ} (hq : q < 1)
    (hchild : ∀ S T, T ∈ children S → T.Nonempty ∧ T ⊆ S ∧
      ownedCubeMass w T ≤ q*ownedCubeMass w S) :
    WellFounded (fun T S => T ∈ children S) := by
  apply (measure (fun S : Finset C => S.card)).wf.mono
  intro T S hT
  exact owned_child_card_lt w hw (hchild S T hT).1 (hchild S T hT).2.1 hq
    (hchild S T hT).2.2

/-- Every finite generated cellular level contracts the same original mass. -/
theorem owned_level_mass_le {C : Type*} [DecidableEq C]
    (w : C → ℝ) (root : Finset C) (children : Finset C → Finset (Finset C))
    {q : ℝ} (hq : 0 ≤ q)
    (hc : ∀ S T, T ∈ children S → ownedCubeMass w T ≤ q*ownedCubeMass w S) :
    ∀ s T, T ∈ slopeTreeLevels {root} children s →
      ownedCubeMass w T ≤ q^s*ownedCubeMass w root := by
  intro s
  induction s with
  | zero =>
      intro T hT
      have he : T=root := by simpa [slopeTreeLevels] using hT
      simp [he]
  | succ s ih =>
      intro T hT
      obtain ⟨S,hS,hST⟩ := Finset.mem_biUnion.mp hT
      calc
        _ ≤ q*ownedCubeMass w S := hc S T hST
        _ ≤ q*(q^s*ownedCubeMass w root) := mul_le_mul_of_nonneg_left (ih S hS) hq
        _ = q^(s+1)*ownedCubeMass w root := by rw [pow_succ]; ring

/-- The B-dependent logarithmic depth bound uses full original cube weights.
The caller can substitute the actual q=C_E*B^(-d); it is not replaced by a
radius-halving bound. -/
theorem owned_nonempty_depth_le {C : Type*} [DecidableEq C]
    (w : C → ℝ) (hw : ∀ c, 1 ≤ w c) (root : Finset C) (hr : root.Nonempty)
    (children : Finset C → Finset (Finset C)) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hc : ∀ S T, T ∈ children S → ownedCubeMass w T ≤ q*ownedCubeMass w S)
    {s : ℕ} {T : Finset C} (hT : T ∈ slopeTreeLevels {root} children s) (hne : T.Nonempty) :
    (s:ℝ) ≤ Real.log (ownedCubeMass w root)/(-Real.log q) := by
  have hp : 0 < ownedCubeMass w root := lt_of_lt_of_le (by norm_num) (ownedCubeMass_floor w hw root hr)
  have hb := (ownedCubeMass_floor w hw T hne).trans (owned_level_mass_le w root children hq.le hc s T hT)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<1) hb
  rw [Real.log_one,Real.log_mul (pow_pos hq _).ne' hp.ne',Real.log_pow] at hl
  apply (le_div_iff₀ (neg_pos.mpr (Real.log_neg hq hq1))).mpr
  nlinarith

theorem owned_levels_eventually_empty {C : Type*} [DecidableEq C]
    (w : C → ℝ) (hw : ∀ c, 1 ≤ w c) (root : Finset C) (hr : root.Nonempty)
    (children : Finset C → Finset (Finset C)) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hc : ∀ S T, T ∈ children S → T.Nonempty ∧ ownedCubeMass w T ≤ q*ownedCubeMass w S)
    (s : ℕ) (hs : Real.log (ownedCubeMass w root)/(-Real.log q) < s) :
    slopeTreeLevels {root} children s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  have hne : T.Nonempty := by
    cases s with
    | zero => simpa [slopeTreeLevels] using (show T=root from by simpa [slopeTreeLevels] using hT) ▸ hr
    | succ s => obtain ⟨S,_,hST⟩ := Finset.mem_biUnion.mp hT; exact (hc S T hST).1
  have hb := owned_nonempty_depth_le w hw root hr children hq hq1
    (fun S T h => (hc S T h).2) hT hne
  linarith

/-- Exact full-mass accounting for an owned finite family of cube subsets.
No density fragment or independent favorable mass is substituted. -/
theorem owned_union_mass {C : Type*} [DecidableEq C]
    (w : C → ℝ) (F : Finset (Finset C))
    (hdis : (↑F : Set (Finset C)).PairwiseDisjoint id) :
    ownedCubeMass w (F.biUnion id) = ∑ S ∈ F, ownedCubeMass w S := by
  exact Finset.sum_biUnion hdis

/-- Stop at empty child families and carry that terminal ownership unchanged. -/
def ownedStoppedChildren {C : Type*} [DecidableEq C]
    (children : Finset C → Finset (Finset C)) (S : Finset C) : Finset (Finset C) :=
  if children S=∅ then {S} else children S

def ownedTerminalFrontier {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C)) (s : ℕ) : Finset (Finset C) :=
  slopeTreeLevels {root} (ownedStoppedChildren children) s

/-- Each carried frontier node is an actual tree node: it either has reached
the current depth or stopped at a previous depth. -/
theorem owned_frontier_trace {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C)) :
    ∀ s T, T ∈ ownedTerminalFrontier root children s →
      ∃ d ≤ s, T ∈ slopeTreeLevels {root} children d ∧ (d=s ∨ children T=∅) := by
  intro s
  induction s with
  | zero =>
      intro T hT
      exact ⟨0,le_rfl,hT,Or.inl rfl⟩
  | succ s ih =>
      intro T hT
      obtain ⟨S,hS,hST⟩ := Finset.mem_biUnion.mp hT
      obtain ⟨d,hd,hSd,hstop⟩ := ih S hS
      by_cases he : children S=∅
      · have hTS : T=S := by simpa [ownedStoppedChildren,he] using hST
        subst T
        exact ⟨d,by omega,hSd,Or.inr he⟩
      · have hTS : T ∈ children S := by simpa [ownedStoppedChildren,he] using hST
        have hds : d=s := hstop.resolve_right he
        subst d
        exact ⟨s+1,le_rfl,slopeTree_child_mem {root} children s hSd hTS,Or.inl rfl⟩

/-- An empty ordinary level turns the constructed stopped frontier into
actual terminal leaves; it does not assume a supplied leaf family. -/
theorem owned_frontier_terminal {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C)) (s : ℕ)
    (hs : slopeTreeLevels {root} children s=∅) :
    ∀ T ∈ ownedTerminalFrontier root children s, children T=∅ := by
  intro T hT
  obtain ⟨d,_,hTd,hstop⟩ := owned_frontier_trace root children s T hT
  rcases hstop with rfl | hstop
  · rw [hs] at hTd
    exact False.elim (Finset.notMem_empty _ hTd)
  · exact hstop

/-- Subset ownership propagates through every actual generated level. -/
theorem owned_level_subset_root {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C))
    (hc : ∀ S T, T ∈ children S → T ⊆ S) :
    ∀ s T, T ∈ slopeTreeLevels {root} children s → T ⊆ root := by
  intro s
  induction s with
  | zero =>
      intro T hT
      have he : T=root := by simpa [slopeTreeLevels] using hT
      simp [he]
  | succ s ih =>
      intro T hT
      obtain ⟨S,hS,hST⟩ := Finset.mem_biUnion.mp hT
      exact (hc S T hST).trans (ih S hS)

/-- Distinct generated nodes own disjoint original cubes, provided each
split supplies disjoint subfamilies. This is not assumed for whole levels. -/
theorem owned_level_disjoint {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C))
    (hsub : ∀ S T, T ∈ children S → T ⊆ S)
    (hdis : ∀ S, (↑(children S) : Set (Finset C)).PairwiseDisjoint id) :
    ∀ s, (↑(slopeTreeLevels {root} children s) : Set (Finset C)).PairwiseDisjoint id := by
  intro s
  induction s with
  | zero => simp [slopeTreeLevels,Set.PairwiseDisjoint]
  | succ s ih =>
      intro T hT U hU hTU
      obtain ⟨S,hS,hST⟩ := Finset.mem_biUnion.mp hT
      obtain ⟨R,hR,hRU⟩ := Finset.mem_biUnion.mp hU
      by_cases he : S=R
      · subst R
        exact hdis S hST hRU hTU
      · exact (ih hS hR he).mono (hsub S T hST) (hsub R U hRU)

/-- The stopped frontier has nonempty nodes, disjoint ownership, and lies
inside the original root. These properties are derived from local splits. -/
theorem owned_frontier_ownership {C : Type*} [DecidableEq C]
    (root : Finset C) (hr : root.Nonempty)
    (children : Finset C → Finset (Finset C))
    (hc : ∀ S T, T ∈ children S → T.Nonempty ∧ T ⊆ S)
    (hdis : ∀ S, (↑(children S) : Set (Finset C)).PairwiseDisjoint id) (s : ℕ) :
    (∀ T ∈ ownedTerminalFrontier root children s, T.Nonempty ∧ T ⊆ root) ∧
    (↑(ownedTerminalFrontier root children s) : Set (Finset C)).PairwiseDisjoint id := by
  have hsub : ∀ S T, T ∈ ownedStoppedChildren children S → T ⊆ S := by
    intro S T hT
    by_cases he : children S=∅
    · have hTS : T=S := by simpa [ownedStoppedChildren,he] using hT
      simp [hTS]
    · exact (hc S T (by simpa [ownedStoppedChildren,he] using hT)).2
  have hds : ∀ S, (↑(ownedStoppedChildren children S) : Set (Finset C)).PairwiseDisjoint id := by
    intro S
    by_cases he : children S=∅
    · simp [ownedStoppedChildren,he,Set.PairwiseDisjoint]
    · simpa [ownedStoppedChildren,he] using hdis S
  refine ⟨?_,owned_level_disjoint root (ownedStoppedChildren children) hsub hds s⟩
  intro T hT
  refine ⟨?_,owned_level_subset_root root (ownedStoppedChildren children) hsub s T hT⟩
  obtain ⟨d,_,hTd,_⟩ := owned_frontier_trace root children s T hT
  cases d with
  | zero =>
      have he : T=root := by simpa [slopeTreeLevels] using hTd
      simpa [he] using hr
  | succ d =>
      obtain ⟨S,_,hST⟩ := Finset.mem_biUnion.mp hTd
      exact (hc S T hST).1

/-- Retention is paid once per actual cellular generation. Terminal nodes
are carried unchanged. The sum counts each original cube at most once. -/
theorem owned_frontier_mass_retained {C : Type*} [DecidableEq C]
    (w : C → ℝ) (hw : ∀ c, 1 ≤ w c) (root : Finset C) (hr : root.Nonempty)
    (children : Finset C → Finset (Finset C))
    (hc : ∀ S T, T ∈ children S → T.Nonempty ∧ T ⊆ S)
    (hdis : ∀ S, (↑(children S) : Set (Finset C)).PairwiseDisjoint id)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hretain : ∀ S, S.Nonempty → (children S).Nonempty →
      a*ownedCubeMass w S ≤ ∑ T ∈ children S, ownedCubeMass w T) :
    ∀ s, a^s*ownedCubeMass w root ≤
      ownedCubeMass w ((ownedTerminalFrontier root children s).biUnion id) := by
  have hstepSub : ∀ S T, T ∈ ownedStoppedChildren children S → T ⊆ S := by
    intro S T hT
    by_cases he : children S=∅
    · have hTS : T=S := by simpa [ownedStoppedChildren,he] using hT
      simp [hTS]
    · exact (hc S T (by simpa [ownedStoppedChildren,he] using hT)).2
  have hstepNe : ∀ S T, S.Nonempty → T ∈ ownedStoppedChildren children S → T.Nonempty := by
    intro S T hS hT
    by_cases he : children S=∅
    · have hTS : T=S := by simpa [ownedStoppedChildren,he] using hT
      simpa [hTS] using hS
    · exact (hc S T (by simpa [ownedStoppedChildren,he] using hT)).1
  have hstepMass : ∀ S, S.Nonempty → a*ownedCubeMass w S ≤
      ∑ T ∈ ownedStoppedChildren children S, ownedCubeMass w T := by
    intro S hS
    by_cases he : children S=∅
    · simp only [ownedStoppedChildren,he,ite_true,Finset.sum_singleton]
      exact mul_le_of_le_one_left (ownedCubeMass_nonneg w hw S) ha1
    · simpa [ownedStoppedChildren,he] using hretain S hS (Finset.nonempty_iff_ne_empty.mpr he)
  intro s
  induction s with
  | zero => simp [ownedTerminalFrontier,slopeTreeLevels]
  | succ s ih =>
      have hown := owned_frontier_ownership root hr children hc hdis s
      have hownNext := owned_frontier_ownership root hr children hc hdis (s+1)
      rw [owned_union_mass w _ hown.2] at ih
      rw [owned_union_mass w _ hownNext.2]
      have hfamily : (↑(ownedTerminalFrontier root children s) : Set (Finset C)).PairwiseDisjoint
          (ownedStoppedChildren children) := by
        intro S hS R hR hSR
        apply Finset.disjoint_left.mpr
        intro T hST hRT
        obtain ⟨c,hcT⟩ := hstepNe S T (hown.1 S hS).1 hST
        exact Finset.disjoint_left.mp (hown.2 hS hR hSR)
          (hstepSub S T hST hcT) (hstepSub R T hRT hcT)
      change a^(s+1)*ownedCubeMass w root ≤
        ∑ T ∈ (ownedTerminalFrontier root children s).biUnion (ownedStoppedChildren children), ownedCubeMass w T
      rw [Finset.sum_biUnion hfamily]
      calc
        a^(s+1)*ownedCubeMass w root = a*(a^s*ownedCubeMass w root) := by rw [pow_succ]; ring
        _ ≤ a*(∑ S ∈ ownedTerminalFrontier root children s, ownedCubeMass w S) :=
          mul_le_mul_of_nonneg_left ih ha
        _ = ∑ S ∈ ownedTerminalFrontier root children s, a*ownedCubeMass w S := Finset.mul_sum ..
        _ ≤ _ := Finset.sum_le_sum (fun S hS => hstepMass S (hown.1 S hS).1)

/-- Concrete finite terminal leaves, disjoint cube ownership, and retained
original mass at any depth above the proved contraction threshold. -/
theorem exists_owned_terminal_leaves {C : Type*} [DecidableEq C]
    (w : C → ℝ) (hw : ∀ c, 1 ≤ w c) (root : Finset C) (hr : root.Nonempty)
    (children : Finset C → Finset (Finset C)) {q a : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hc : ∀ S T, T ∈ children S → T.Nonempty ∧ T ⊆ S ∧
      ownedCubeMass w T ≤ q*ownedCubeMass w S)
    (hdis : ∀ S, (↑(children S) : Set (Finset C)).PairwiseDisjoint id)
    (hretain : ∀ S, S.Nonempty → (children S).Nonempty →
      a*ownedCubeMass w S ≤ ∑ T ∈ children S, ownedCubeMass w T)
    (s : ℕ) (hs : Real.log (ownedCubeMass w root)/(-Real.log q) < s) :
    ∃ F : Finset (Finset C),
      (∀ T ∈ F, T.Nonempty ∧ T ⊆ root ∧ children T=∅) ∧
      (↑F : Set (Finset C)).PairwiseDisjoint id ∧
      a^s*ownedCubeMass w root ≤ ownedCubeMass w (F.biUnion id) ∧
      ownedCubeMass w (F.biUnion id)=∑ T ∈ F, ownedCubeMass w T := by
  have hc' : ∀ S T, T ∈ children S → T.Nonempty ∧ T ⊆ S :=
    fun S T h => ⟨(hc S T h).1,(hc S T h).2.1⟩
  have hown := owned_frontier_ownership root hr children hc' hdis s
  have hempty := owned_levels_eventually_empty w hw root hr children hq hq1
    (fun S T h => ⟨(hc S T h).1,(hc S T h).2.2⟩) s hs
  refine ⟨ownedTerminalFrontier root children s,?_,hown.2,?_,owned_union_mass w _ hown.2⟩
  · intro T hT
    exact ⟨(hown.1 T hT).1,(hown.1 T hT).2,owned_frontier_terminal root children s hempty T hT⟩
  · exact owned_frontier_mass_retained w hw root hr children hc' hdis ha ha1 hretain s

/-- A branching budget propagates on the SAME stopped frontier used for
mass retention. Physical crossing bounds still have to supply the local
budget in their own geometric tree; no such bound is postulated as proved. -/
theorem owned_frontier_card_le {C : Type*} [DecidableEq C]
    (root : Finset C) (children : Finset C → Finset (Finset C))
    (B : ℕ) (hB : ∀ S, (children S).card ≤ B) (s : ℕ) :
    (ownedTerminalFrontier root children s).card ≤ (max B 1)^s := by
  have hs : ∀ S, (ownedStoppedChildren children S).card ≤ max B 1 := by
    intro S
    by_cases he : children S=∅
    · simp [ownedStoppedChildren,he]
    · simpa [ownedStoppedChildren,he] using (hB S).trans (le_max_left B 1)
  have hb := grainTree_level_card_le {root} (ownedStoppedChildren children) (max B 1)
    (fun _ S _ => hs S) s
  simpa [ownedTerminalFrontier] using hb

end KakeyaTwoScale
#print axioms KakeyaTwoScale.owned_children_wellFounded
#print axioms KakeyaTwoScale.owned_nonempty_depth_le
#print axioms KakeyaTwoScale.owned_levels_eventually_empty
#print axioms KakeyaTwoScale.owned_union_mass
#print axioms KakeyaTwoScale.owned_frontier_terminal
#print axioms KakeyaTwoScale.owned_frontier_ownership
#print axioms KakeyaTwoScale.owned_frontier_mass_retained
#print axioms KakeyaTwoScale.exists_owned_terminal_leaves
#print axioms KakeyaTwoScale.owned_frontier_card_le
