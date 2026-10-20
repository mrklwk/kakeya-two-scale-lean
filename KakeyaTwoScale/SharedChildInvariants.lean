module
public import KakeyaTwoScale.FamilySharedCapLocalization

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A consistent label on finitely witnessed records extends to a genuine
record-label function, so the next state need not label tuple occurrences. -/
theorem exists_record_label {T P G : Type*} [DecidableEq T]
    (Y : Finset T) (piece : T → P) (label : T → G) (fallback : G)
    (hc : ∀ y ∈ Y, ∀ z ∈ Y, piece y=piece z → label y=label z) :
    ∃ origin : P → G, ∀ y ∈ Y, origin (piece y)=label y := by
  classical
  have hex : ∀ t : P, ∃ g : G, ∀ y ∈ Y, piece y=t → g=label y := by
    intro t
    by_cases h : ∃ y ∈ Y, piece y=t
    · obtain ⟨z,hz,hzt⟩ := h
      exact ⟨label z,fun y hy hyt => hc z hz y hy (hzt.trans hyt.symm)⟩
    · exact ⟨fallback,fun y hy hyt => False.elim (h ⟨y,hy,hyt⟩)⟩
  choose origin ho using hex
  exact ⟨origin,fun y hy => ho (piece y) y hy rfl⟩

/-- Disjoint parent geometry and one common cap color yield disjoint actual
children across the entire original tube, including children from different
parents. The record retains its parent identity. -/
theorem shared_children_disjoint {n : ℕ} {P : Type*}
    (parents : Set P) (b u : P → EuclideanSpace ℝ (Fin n)) (L : P → ℝ)
    {ell width : ℝ} (hell : 0 < ell) (hu : ∀ t ∈ parents, ‖u t‖=1)
    (hL : ∀ t ∈ parents, ell ≤ L t) (color : Fin 3)
    (hd : PairwiseDisjoint parents (fun t => flatCylinder (b t) (u t) (L t) width)) :
    PairwiseDisjoint {s : P×ℝ | s.1 ∈ parents ∧ s.2 ∈ cappedStarts (L s.1) ell color}
      (fun s => flatCylinder (b s.1+s.2 • u s.1) (u s.1) ell width) := by
  intro s hs t ht hne
  by_cases he : s.1=t.1
  · have ha : s.2 ≠ t.2 := fun h => hne (Prod.ext he h)
    have hh := prescribed_length_cylinders_disjoint (width:=width) (b s.1) (u s.1) hell (hu s.1 hs.1)
      color hs.2 (by simpa only [he,Finset.mem_coe] using ht.2) ha
    dsimp only [Function.onFun] at hh ⊢
    simpa only [he] using hh
  · have hsub (s : P×ℝ) (hs : s.1 ∈ parents ∧ s.2 ∈ cappedStarts (L s.1) ell color) :
        flatCylinder (b s.1+s.2 • u s.1) (u s.1) ell width ⊆ flatCylinder (b s.1) (u s.1) (L s.1) width := by
      have hb := cappedStarts_bounds hell (hL s.1 hs.1) color hs.2
      rintro x ⟨a,ha0,haell,hai,hax⟩
      have he : b s.1+(s.2+a) • u s.1=(b s.1+s.2 • u s.1)+a • u s.1 := by module
      exact ⟨s.2+a,by linarith [hb.1],by linarith [hb.2],
        by simpa only [he] using hai,by simpa only [he] using hax⟩
    exact (hd hs.1 ht.1 he).mono (hsub s hs) (hsub t ht)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_record_label
#print axioms KakeyaTwoScale.shared_children_disjoint
