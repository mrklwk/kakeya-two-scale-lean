module
public import KakeyaTwoScale.ShortComponentTerminal
public import KakeyaTwoScale.FrozenGeometryState
public import KakeyaTwoScale.SelectedAncestorSurvival

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
attribute [local instance] Classical.propDecidable

/-- The all-short bound applies to the stored filtered original tuple relation
inside a full archive. Original tuple identity proves injectivity; the counted
physical sets are the unchanged archived grain records. No lower family count
or bound on all cubes in a grain is used. -/
theorem exists_filtered_terminal_bound (n : ℕ) (Cstar : ℝ) :
    ∃ cap : ℕ, 0 < cap ∧ ∀ {T O : Type} [DecidableEq T] {k : ℕ},
      ∀ (S : FrozenGeometryState n k T (Fin n → ℤ) O) (Y₀ : Finset T)
        (cube : T → Fin n → ℤ) (tube : T → Fin k → O)
        (cubes : Finset (Fin n → ℤ)) (δ : ℝ), 0 < δ →
      S.Valid Y₀ cube tube (fun q => WithLp.ofLp ⁻¹' gridCell δ q) δ →
      (∀ y ∈ Y₀, ∀ z ∈ Y₀, cube y=cube z → (∀ j, tube y j=tube z j) → y=z) →
      (∀ j, S.length δ j ≤ Cstar*δ) → 0 < k →
      ∀ (p : ℝ), 1/(k:ℝ) ≤ p → ∀ (Z : Finset T), Z ⊆ S.tuples →
      ∀ g : S.Grain,
        tupleCubeMass (Z.filter fun y => S.grain (cube y)=g) cube cubes p ≤
          (∏ j, (cap:ℝ)*(grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g:ℝ))^p := by
  classical
  obtain ⟨cap,hcap,hterminal⟩ := exists_short_component_terminal_bound n Cstar
  refine ⟨cap,hcap,?_⟩
  intro T O inst k S Y₀ cube tube cubes δ hδ hv hinj hshort hk p hp Z hZS g
  let Y := Z.filter fun y => S.grain (cube y)=g
  let pieces := fun j => (S.tuples.filter fun y => S.grain (cube y)=g).image (fun y => S.parent y j)
  have hY : Y ⊆ S.tuples := fun y hy => hZS (Finset.mem_filter.mp hy).1
  have hp0 : 0 < p := (div_pos zero_lt_one (by exact_mod_cast hk : (0:ℝ)<k)).trans_le hp
  by_cases hne : Y.Nonempty
  · apply hterminal Y hne cube cubes S.parent pieces S.base S.axis
      (fun j _ => S.length δ j) δ hδ hv.2.1 (fun j _ _ => hshort j)
    · intro y hy j
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hY hy,(Finset.mem_filter.mp hy).2⟩)
    · exact fun y hy j => hv.2.2.2.2.1 y (hY hy) j
    · intro y hy z hz hcube hpiece
      apply hinj y (hv.1 (hY hy)) z (hv.1 (hY hz)) hcube
      intro j
      exact (hv.2.2.1 y (hY hy) j).symm.trans
        ((congrArg (S.original j) (congrFun hpiece j)).trans (hv.2.2.1 z (hY hz) j))
    · exact hk
    · exact hp
  · have he : Y=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change tupleCubeMass Y cube cubes p ≤ _
    simp only [he,tupleCubeMass,ParentLevel.capacity,Finset.filter_empty,Finset.card_empty,
      Nat.cast_zero,Real.zero_rpow hp0.ne',Finset.sum_const_zero]
    positivity

/-- The input identity criterion is inherited by every archived subrelation;
selected tuples are never reconstructed from accidental intersections. -/
theorem selected_original_tuple_identity {n k : ℕ} {T C O : Type}
    (S : FrozenGeometryState n k T C O) (Y₀ Z : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (hv : S.Valid Y₀ cube tube Q δ) (hZ : Z ⊆ S.tuples)
    (hinj : ∀ y ∈ Y₀, ∀ z ∈ Y₀, cube y=cube z → (∀ j, tube y j=tube z j) → y=z) :
    ∀ y ∈ Z, ∀ z ∈ Z, cube y=cube z → S.parent y=S.parent z → y=z := by
  intro y hy z hz hc hp
  apply hinj y (hv.1 (hZ hy)) z (hv.1 (hZ hz)) hc
  intro j
  exact (hv.2.2.1 y (hZ hy) j).symm.trans
    ((congrArg (S.original j) (congrFun hp j)).trans (hv.2.2.1 z (hZ hz) j))

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_filtered_terminal_bound
#print axioms KakeyaTwoScale.FrozenGeometryState.selected_original_tuple_identity
