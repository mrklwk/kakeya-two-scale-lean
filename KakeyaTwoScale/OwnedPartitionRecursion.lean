module
public import KakeyaTwoScale.OwnedCubeRecursion

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Every nonempty literal owner fiber, with the original cube identities. -/
def ownedOwnerCells {L : Type*} [Fintype L] [DecidableEq L]
    {C : Type*} [DecidableEq C] (G : Finset C) (owner : C → L) : Finset (Finset C) :=
  (Finset.univ.image (fun label => G.filter (fun c => owner c = label))).filter Finset.Nonempty

theorem mem_ownedOwnerCells {L : Type*} [Fintype L] [DecidableEq L]
    {C : Type*} [DecidableEq C] (G : Finset C) (owner : C → L) {A : Finset C} :
    A ∈ ownedOwnerCells G owner ↔
      A.Nonempty ∧ ∃ label, A = G.filter (fun c => owner c = label) := by
  simp only [ownedOwnerCells, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨label, rfl⟩, hne⟩
    exact ⟨hne, label, rfl⟩
  · rintro ⟨hne, label, rfl⟩
    exact ⟨⟨label, rfl⟩, hne⟩

theorem ownedOwnerCells_disjoint {L : Type*} [Fintype L] [DecidableEq L]
    {C : Type*} [DecidableEq C] (G : Finset C) (owner : C → L) :
    (↑(ownedOwnerCells G owner) : Set (Finset C)).PairwiseDisjoint id := by
  intro A hA B hB hAB
  obtain ⟨_,i,rfl⟩ := (mem_ownedOwnerCells G owner).mp hA
  obtain ⟨_,j,rfl⟩ := (mem_ownedOwnerCells G owner).mp hB
  apply Finset.disjoint_left.mpr
  intro c hc hd
  have hij := (Finset.mem_filter.mp hc).2.symm.trans (Finset.mem_filter.mp hd).2
  exact hAB (hij ▸ rfl)

theorem ownedOwnerCells_union {L : Type*} [Fintype L] [DecidableEq L]
    {C : Type*} [DecidableEq C] (G : Finset C) (owner : C → L) :
    (ownedOwnerCells G owner).biUnion id = G := by
  ext c
  constructor
  · intro hc
    obtain ⟨A,hA,hc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨_,label,rfl⟩ := (mem_ownedOwnerCells G owner).mp hA
    exact (Finset.mem_filter.mp hc).1
  · intro hc
    have hm : c ∈ G.filter (fun d => owner d = owner c) := Finset.mem_filter.mpr ⟨hc,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨_, (mem_ownedOwnerCells G owner).mpr
      ⟨⟨c,hm⟩,owner c,rfl⟩,hm⟩

theorem ownedOwnerCells_mass {L : Type*} [Fintype L] [DecidableEq L]
    {C : Type*} [DecidableEq C] (G : Finset C) (owner : C → L) (w : C → ℝ) :
    (∑ A ∈ ownedOwnerCells G owner, ownedCubeMass w A) = ownedCubeMass w G := by
  rw [← owned_union_mass w _ (ownedOwnerCells_disjoint G owner), ownedOwnerCells_union]

theorem ownedOwnerCells_card_le {L : Type*} [Fintype L] [DecidableEq L]
    {C : Type*} [DecidableEq C] (G : Finset C) (owner : C → L) :
    (ownedOwnerCells G owner).card ≤ Fintype.card L := by
  exact (Finset.card_filter_le _ _).trans
    (Finset.card_image_le.trans (by simp))

/-- One actual local split, retaining the exact geometric record used for both
its owner fibers and its algebraic successor. `Data` is not reselected later. -/
structure OwnedPartitionNode {C : Type*} [DecidableEq C]
    (w : C → ℝ) (a : ℝ) (s : ℕ) (Data : Finset C → Type*)
    (Valid : ∀ A, Data A → Prop)
    (CellCert : ∀ A, Data A → Finset (Finset C) → Prop)
    (LeafCert : ∀ A, Data A → Finset C → Prop) (A : Finset C) where
  data : Data A
  valid : Valid A data
  children : Finset (Finset C)
  selected : Finset C
  split :
    (children = ∅ ∧ selected ⊆ A ∧
      ownedCubeMass w A ≤ (a * (s+1 : ℕ)) * ownedCubeMass w selected ∧
      LeafCert A data selected) ∨
    (selected = ∅ ∧
      (∀ T ∈ children, T.Nonempty ∧ T ⊆ A ∧
        ownedCubeMass w T ≤ ((2:ℝ)/2^s)*ownedCubeMass w A) ∧
      (↑children : Set (Finset C)).PairwiseDisjoint id ∧
      ownedCubeMass w A ≤ a * ∑ T ∈ children, ownedCubeMass w T ∧
      CellCert A data children)

variable {C : Type*} [DecidableEq C] {w : C → ℝ} {a : ℝ} {s : ℕ}
  {Data : Finset C → Type*} {Valid : ∀ A, Data A → Prop}
  {CellCert : ∀ A, Data A → Finset (Finset C) → Prop}
  {LeafCert : ∀ A, Data A → Finset C → Prop}

/-- Convert a labelled cellular output to the actual family of all nonempty
owner fibers. Both the record and the labels are the original local choices. -/
def OwnedPartitionNode.ofOwner {L : Type*} [Fintype L] [DecidableEq L]
    {A : Finset C} (data : Data A) (valid : Valid A data)
    (G : Finset C) (owner : C → L) (hG : G ⊆ A)
    (hretain : ownedCubeMass w A ≤ a * ownedCubeMass w G)
    (hcap : ∀ label, ownedCubeMass w (G.filter (fun c => owner c = label)) ≤
      ((2:ℝ)/2^s)*ownedCubeMass w A)
    (hcert : CellCert A data (ownedOwnerCells G owner)) :
    OwnedPartitionNode w a s Data Valid CellCert LeafCert A where
  data := data
  valid := valid
  children := ownedOwnerCells G owner
  selected := ∅
  split := Or.inr ⟨rfl, by
    intro T hT
    obtain ⟨hne,label,rfl⟩ := (mem_ownedOwnerCells G owner).mp hT
    exact ⟨hne,(Finset.filter_subset _ _).trans hG,hcap label⟩,
    ownedOwnerCells_disjoint G owner,
    by simpa only [ownedOwnerCells_mass] using hretain,hcert⟩

/-- Totalize the locally chosen nodes outside the original owned mask by no children. -/
def ownedPartitionChildren (root : Finset C)
    (node : ∀ A, A ⊆ root → A.Nonempty → OwnedPartitionNode w a s Data Valid CellCert LeafCert A)
    (A : Finset C) : Finset (Finset C) :=
  if h : A ⊆ root ∧ A.Nonempty then (node A h.1 h.2).children else ∅

def ownedPartitionSelected (root : Finset C)
    (node : ∀ A, A ⊆ root → A.Nonempty → OwnedPartitionNode w a s Data Valid CellCert LeafCert A)
    (A : Finset C) : Finset C :=
  if h : A ⊆ root ∧ A.Nonempty then (node A h.1 h.2).selected else ∅

theorem ownedPartitionChildren_node (root : Finset C)
    (node : ∀ A, A ⊆ root → A.Nonempty → OwnedPartitionNode w a s Data Valid CellCert LeafCert A)
    (A : Finset C) (hA : A ⊆ root) (hne : A.Nonempty) :
    ownedPartitionChildren root node A = (node A hA hne).children := by
  simp [ownedPartitionChildren,hA,hne]

theorem ownedPartitionSelected_node (root : Finset C)
    (node : ∀ A, A ⊆ root → A.Nonempty → OwnedPartitionNode w a s Data Valid CellCert LeafCert A)
    (A : Finset C) (hA : A ⊆ root) (hne : A.Nonempty) :
    ownedPartitionSelected root node A = (node A hA hne).selected := by
  simp [ownedPartitionSelected,hA,hne]

/-- Retrieve cellular geometry from exactly the record that generated a node's
children. This supports independent crossing budgets on this same recursion. -/
theorem ownedPartition_cellular_certificate (root : Finset C)
    (node : ∀ A, A ⊆ root → A.Nonempty → OwnedPartitionNode w a s Data Valid CellCert LeafCert A)
    (A : Finset C) (hA : A ⊆ root) (hne : A.Nonempty)
    (hchild : (ownedPartitionChildren root node A).Nonempty) :
    Valid A (node A hA hne).data ∧
      CellCert A (node A hA hne).data (ownedPartitionChildren root node A) := by
  rw [ownedPartitionChildren_node root node A hA hne] at hchild ⊢
  refine ⟨(node A hA hne).valid,?_⟩
  rcases (node A hA hne).split with hl | hc
  · rw [hl.1] at hchild
    exact (Finset.not_nonempty_empty hchild).elim
  · exact hc.2.2.2.2

/-- The constructed recursion uses every nonempty cellular owner mask, ends at
algebraic leaves, and retains full original weights. Its geometric records are
exactly the supplied local nodes; neither leaves nor ownership are postulated. -/
theorem exists_owned_partition_recursion
    (hw : ∀ c, 1 ≤ w c) (ha : 1 ≤ a) (hs : 2 ≤ s)
    (root : Finset C) (hr : root.Nonempty)
    (node : ∀ A, A ⊆ root → A.Nonempty → OwnedPartitionNode w a s Data Valid CellCert LeafCert A)
    (depth : ℕ)
    (hdepth : Real.log (ownedCubeMass w root) / (-Real.log ((2:ℝ)/2^s)) < depth) :
    let children := ownedPartitionChildren root node
    let selected := ownedPartitionSelected root node
    ∃ F : Finset (Finset C),
      F = ownedTerminalFrontier root children depth ∧
      (∀ A T, T ∈ children A → T.Nonempty ∧ T ⊆ A ∧ T.card < A.card) ∧
      (∀ A ∈ F, A.Nonempty ∧ A ⊆ root ∧ children A = ∅ ∧
        (selected A).Nonempty ∧ selected A ⊆ A ∧
        ownedCubeMass w A ≤ (a * (s+1 : ℕ)) * ownedCubeMass w (selected A)) ∧
      (∀ A ∈ F, ∃ (hA : A ⊆ root) (hne : A.Nonempty),
        Valid A (node A hA hne).data ∧
        LeafCert A (node A hA hne).data (selected A)) ∧
      (↑F : Set (Finset C)).PairwiseDisjoint id ∧
      (↑F : Set (Finset C)).PairwiseDisjoint selected ∧
      F.biUnion selected ⊆ root ∧
      ownedCubeMass w root / (a^depth * (a * (s+1 : ℕ))) ≤
        ownedCubeMass w (F.biUnion selected) ∧
      ownedCubeMass w (F.biUnion selected) = ∑ A ∈ F, ownedCubeMass w (selected A) := by
  classical
  let children := ownedPartitionChildren root node
  let selected := ownedPartitionSelected root node
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hpow : (2:ℝ) < 2^s := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hs
    norm_num at hh ⊢
    linarith
  have hq : 0 < (2:ℝ)/2^s := by positivity
  have hq1 : (2:ℝ)/2^s < 1 := (div_lt_one (by positivity)).mpr hpow
  have hc (A T) (hT : T ∈ children A) : T.Nonempty ∧ T ⊆ A ∧
      ownedCubeMass w T ≤ ((2:ℝ)/2^s)*ownedCubeMass w A := by
    dsimp [children, ownedPartitionChildren] at hT
    split_ifs at hT with hA
    · rcases (node A hA.1 hA.2).split with hleaf | hcell
      · rw [hleaf.1] at hT
        exact (Finset.notMem_empty _ hT).elim
      · exact hcell.2.1 T hT
    · exact (Finset.notMem_empty _ hT).elim
  have hd (A) : (↑(children A) : Set (Finset C)).PairwiseDisjoint id := by
    dsimp [children, ownedPartitionChildren]
    split_ifs with hA
    · rcases (node A hA.1 hA.2).split with hleaf | hcell
      · simp [hleaf.1]
      · exact hcell.2.2.1
    · simp
  have hretain (A) (_hne : A.Nonempty) (hch : (children A).Nonempty) :
      (1/a)*ownedCubeMass w A ≤ ∑ T ∈ children A, ownedCubeMass w T := by
    dsimp [children, ownedPartitionChildren] at hch ⊢
    split_ifs at hch ⊢ with hA
    · rcases (node A hA.1 hA.2).split with hleaf | hcell
      · rw [hleaf.1] at hch
        exact (Finset.not_nonempty_empty hch).elim
      · have hh : ownedCubeMass w A / a ≤ ∑ T ∈ (node A hA.1 hA.2).children, ownedCubeMass w T :=
          (div_le_iff₀ hap).mpr (by simpa only [mul_comm] using hcell.2.2.2.1)
        calc
          (1/a)*ownedCubeMass w A = ownedCubeMass w A/a := by ring
          _ ≤ _ := hh
    · exact (Finset.not_nonempty_empty hch).elim
  have hc' : ∀ A T, T ∈ children A → T.Nonempty ∧ T ⊆ A :=
    fun A T h => ⟨(hc A T h).1, (hc A T h).2.1⟩
  let F := ownedTerminalFrontier root children depth
  have hown := owned_frontier_ownership root hr children hc' hd depth
  have hempty := owned_levels_eventually_empty w hw root hr children hq hq1
    (fun A T h => ⟨(hc A T h).1, (hc A T h).2.2⟩) depth hdepth
  have hterminal := owned_frontier_terminal root children depth hempty
  have hret := owned_frontier_mass_retained w hw root hr children hc' hd
    (by positivity : (0:ℝ) ≤ 1/a) ((div_le_one hap).mpr ha) hretain depth
  have hleaf (A) (hAF : A ∈ F) : selected A ⊆ A ∧
      ownedCubeMass w A ≤ (a * (s+1 : ℕ)) * ownedCubeMass w (selected A) ∧
      LeafCert A (node A (hown.1 A hAF).2 (hown.1 A hAF).1).data (selected A) := by
    have hA := hown.1 A hAF
    have hstop : (node A hA.2 hA.1).children = ∅ := by
      simpa [children, ownedPartitionChildren, hA] using hterminal A hAF
    have hsel : selected A = (node A hA.2 hA.1).selected := by
      simp [selected, ownedPartitionSelected, hA]
    rw [hsel]
    rcases (node A hA.2 hA.1).split with hl | hh
    · exact hl.2
    · have hmass := hh.2.2.2.1
      rw [hstop, Finset.sum_empty, mul_zero] at hmass
      have hpos := ownedCubeMass_floor w hw A hA.1
      linarith
  have hselectedNe (A) (hAF : A ∈ F) : (selected A).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm := (hleaf A hAF).2.1
    have hp := ownedCubeMass_floor w hw A (hown.1 A hAF).1
    simp only [he, ownedCubeMass, Finset.sum_empty, mul_zero] at hm
    unfold ownedCubeMass at hp
    linarith
  have hsd : (↑F : Set (Finset C)).PairwiseDisjoint selected := by
    intro A hA B hB hAB
    exact (hown.2 hA hB hAB).mono (hleaf A hA).1 (hleaf B hB).1
  have hsub : F.biUnion selected ⊆ root := by
    intro c hc
    obtain ⟨A,hA,hc⟩ := Finset.mem_biUnion.mp hc
    exact (hown.1 A hA).2 ((hleaf A hA).1 hc)
  have heq : ownedCubeMass w (F.biUnion selected) = ∑ A ∈ F, ownedCubeMass w (selected A) :=
    Finset.sum_biUnion hsd
  refine ⟨F,rfl,?_,?_,?_,hown.2,hsd,hsub,?_,heq⟩
  · intro A T hT
    exact ⟨(hc A T hT).1,(hc A T hT).2.1,
      owned_child_card_lt w hw (hc A T hT).1 (hc A T hT).2.1 hq1 (hc A T hT).2.2⟩
  · intro A hA
    exact ⟨(hown.1 A hA).1,(hown.1 A hA).2,hterminal A hA,
      hselectedNe A hA,(hleaf A hA).1,(hleaf A hA).2.1⟩
  · intro A hA
    exact ⟨(hown.1 A hA).2,(hown.1 A hA).1,
      (node A (hown.1 A hA).2 (hown.1 A hA).1).valid,(hleaf A hA).2.2⟩
  · rw [heq]
    rw [owned_union_mass w F hown.2] at hret
    have hden : (0:ℝ) < (a * (s+1 : ℕ)) := by positivity
    calc
      ownedCubeMass w root / (a^depth * (a * (s+1 : ℕ))) =
          ((1/a)^depth * ownedCubeMass w root) / (a * (s+1 : ℕ)) := by
            rw [div_pow]
            field_simp
            simp
      _ ≤ (∑ A ∈ F, ownedCubeMass w A) / (a * (s+1 : ℕ)) :=
        div_le_div_of_nonneg_right hret hden.le
      _ = ∑ A ∈ F, ownedCubeMass w A / (a * (s+1 : ℕ)) := Finset.sum_div ..
      _ ≤ _ := Finset.sum_le_sum (fun A hA => (div_le_iff₀ hden).mpr
        (by simpa only [mul_comm] using (hleaf A hA).2.1))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ownedOwnerCells_mass
#print axioms KakeyaTwoScale.ownedPartition_cellular_certificate
#print axioms KakeyaTwoScale.exists_owned_partition_recursion
