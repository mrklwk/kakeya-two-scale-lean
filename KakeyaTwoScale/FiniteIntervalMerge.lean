module
public import KakeyaTwoScale.PaddedAxisIntervals

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- Construct disjoint closed intervals by repeatedly merging an overlapping
pair. The exact union and per-input containment prevent invented axial gaps. -/
theorem exists_disjoint_interval_merge (S : Finset (ℝ × ℝ)) (L δ : ℝ)
    (hvalid : ∀ a ∈ S, 0 ≤ a.1 ∧ a.1+δ ≤ a.2 ∧ a.2 ≤ L) :
    ∃ U : Finset (ℝ × ℝ), U.card ≤ S.card ∧
      (∀ a ∈ U, 0 ≤ a.1 ∧ a.1+δ ≤ a.2 ∧ a.2 ≤ L) ∧
      PairwiseDisjoint (↑U : Set (ℝ × ℝ)) (fun a => Icc a.1 a.2) ∧
      (∀ a ∈ S, ∃ b ∈ U, b.1 ≤ a.1 ∧ a.2 ≤ b.2) ∧
      (∀ b ∈ U, ∀ t ∈ Icc b.1 b.2, ∃ a ∈ S, t ∈ Icc a.1 a.2) := by
  classical
  induction S using (measure (fun T : Finset (ℝ × ℝ) => T.card)).wf.induction with
  | h S ih =>
    by_cases hd : PairwiseDisjoint (↑S : Set (ℝ × ℝ)) (fun a => Icc a.1 a.2)
    · exact ⟨S,le_rfl,hvalid,hd,fun a ha => ⟨a,ha,le_rfl,le_rfl⟩,
        fun b hb t ht => ⟨b,hb,ht⟩⟩
    · have hn : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ¬Disjoint (Icc a.1 a.2) (Icc b.1 b.2) := by
        unfold Set.PairwiseDisjoint Set.Pairwise at hd
        push Not at hd
        exact hd
      obtain ⟨a,ha,b,hb,hab,hov⟩ := hn
      obtain ⟨t,hta,htb⟩ := Set.not_disjoint_iff.mp hov
      let c : ℝ × ℝ := (min a.1 b.1,max a.2 b.2)
      let R := (S.erase a).erase b
      let V := insert c R
      have hR : ∀ z ∈ R, z ∈ S := fun z hz => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
      have habR : a ∉ R ∧ b ∉ R := by simp [R]
      have hVmem : ∀ z ∈ V, z=c ∨ z ∈ R := by intro z hz; exact Finset.mem_insert.mp hz
      have hcvalid : 0 ≤ c.1 ∧ c.1+δ ≤ c.2 ∧ c.2 ≤ L := by
        obtain ⟨ha0,haδ,haL⟩ := hvalid a ha
        obtain ⟨hb0,hbδ,hbL⟩ := hvalid b hb
        dsimp [c]
        refine ⟨le_min ha0 hb0,?_,max_le haL hbL⟩
        linarith [min_le_left a.1 b.1,le_max_left a.2 b.2]
      have hVvalid : ∀ z ∈ V, 0 ≤ z.1 ∧ z.1+δ ≤ z.2 ∧ z.2 ≤ L := by
        intro z hz
        rcases hVmem z hz with rfl | hz
        · exact hcvalid
        · exact hvalid z (hR z hz)
      have hcard : V.card < S.card := by
        have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
        have h₁ := Finset.card_erase_add_one ha
        have h₂ := Finset.card_erase_add_one hb'
        have h₃ : V.card ≤ R.card+1 := Finset.card_insert_le _ _
        dsimp [R] at h₃
        omega
      obtain ⟨U,hUcard,hUvalid,hUdis,hcover,hunion⟩ := ih V hcard hVvalid
      have hsc : ∀ z ∈ S, ∃ v ∈ V, v.1 ≤ z.1 ∧ z.2 ≤ v.2 := by
        intro z hz
        by_cases hza : z=a
        · subst z
          exact ⟨c,Finset.mem_insert_self _ _,min_le_left _ _,le_max_left _ _⟩
        by_cases hzb : z=b
        · subst z
          exact ⟨c,Finset.mem_insert_self _ _,min_le_right _ _,le_max_right _ _⟩
        exact ⟨z,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzb,
          Finset.mem_erase.mpr ⟨hza,hz⟩⟩),le_rfl,le_rfl⟩
      have hvc : ∀ v ∈ V, ∀ s ∈ Icc v.1 v.2, ∃ z ∈ S, s ∈ Icc z.1 z.2 := by
        intro v hv s hs
        rcases hVmem v hv with rfl | hv
        · have he : Icc a.1 a.2 ∪ Icc b.1 b.2 = Icc c.1 c.2 :=
            Set.Icc_union_Icc' (htb.1.trans hta.2) (hta.1.trans htb.2)
          rw [← he] at hs
          rcases hs with hs | hs
          · exact ⟨a,ha,hs⟩
          · exact ⟨b,hb,hs⟩
        · exact ⟨v,hR v hv,hs⟩
      refine ⟨U,hUcard.trans hcard.le,hUvalid,hUdis,?_,?_⟩
      · intro z hz
        obtain ⟨v,hv,hvz,hzv⟩ := hsc z hz
        obtain ⟨u,hu,huv,hvu⟩ := hcover v hv
        exact ⟨u,hu,huv.trans hvz,hzv.trans hvu⟩
      · intro u hu s hs
        obtain ⟨v,hv,hsv⟩ := hunion u hu s hs
        exact hvc v hv s hsv

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_disjoint_interval_merge
