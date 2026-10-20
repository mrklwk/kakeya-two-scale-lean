module
public import KakeyaTwoScale.FrozenStateBalance

@[expose] public section

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- Concrete normalized reset on actual shared records. Its two count inputs
are exactly the geometric cut and whole-grain restriction outputs. -/
theorem actual_normalized_reset {n k : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    (S S' : FrozenGeometryState n k T C O) (cube : T → C) (cubes : Finset C)
    (lift : S'.Grain → S.Grain) {p q : ℝ} (hb : S.Balanced cube cubes p)
    (hne : S.tuples.Nonempty) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ho : ∀ y ∈ S'.tuples, ∀ j, S'.origin j (S'.parent y j)=S'.grain (cube y))
    {X : ℝ} (hX : 0 ≤ X) (j : Fin k)
    (hglobal : (S'.count j:ℝ) ≤ X*S.count j)
    (hfiber : ∀ g, (grainRecordCount S'.tuples cube (lift ∘ S'.grain) (fun y => S'.parent y j) g:ℝ) ≤
      X*grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g) :
    (S'.count j:ℝ) ≤ 2*X*S.count j*(((S'.grains cube).card:ℝ)/(S.grains cube).card)^q := by
  classical
  have hh : (0:ℝ) < (S.grains cube).card := by
    exact_mod_cast Finset.card_pos.mpr (hne.image _)
  have hlocal (g : S.Grain) :
      (grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g:ℝ) ≤
        2*S.count j/(S.grains cube).card := by
    by_cases hg : g ∈ S.grains cube
    · exact (hb g hg).2 j |>.2
    · have he : S.tuples.filter (fun y => S.grain (cube y)=g)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨hy,he⟩ := Finset.mem_filter.mp hy
        exact hg (Finset.mem_image.mpr ⟨y,hy,he⟩)
      simp only [grainRecordCount,he,Finset.image_empty,Finset.card_empty,Nat.cast_zero]
      positivity
  have himage : (S'.records j).image (S'.origin j) = S'.grains cube := by
    ext g
    simp only [records,grains,Finset.mem_image,Function.comp_apply]
    constructor
    · rintro ⟨t,⟨y,hy,rfl⟩,hg⟩
      exact ⟨y,hy,(ho y hy j).symm.trans hg⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨S'.parent y j,⟨y,hy,rfl⟩,ho y hy j⟩
  have hh' := upper_budget_reset (S'.records j) (S'.origin j) lift (A:=2)
    (by norm_num) hX (Nat.cast_nonneg _) hh hq hq1 hglobal (by
      intro g hg
      have he := grain_record_image_fiber S'.tuples cube (lift ∘ S'.grain)
        (fun y => S'.parent y j) (lift ∘ S'.origin j)
        (fun y hy => congrArg lift (ho y hy j)) g
      have he' : ((S'.records j).filter (fun t => lift (S'.origin j t)=g)).card =
          grainRecordCount S'.tuples cube (lift ∘ S'.grain) (fun y => S'.parent y j) g := by
        exact congrArg Finset.card he
      rw [he']
      exact (hfiber g).trans (by
        have h := mul_le_mul_of_nonneg_left (hlocal g) hX
        convert h using 1
        ring))
  simpa only [count,himage] using hh'

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.actual_normalized_reset
