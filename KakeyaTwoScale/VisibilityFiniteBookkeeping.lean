module
public import KakeyaTwoScale.ActualSignedVisibilityLabels
public import KakeyaTwoScale.FullDegreeCoefficientSpace
public import KakeyaTwoScale.ActualVisibilityBank

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- A common strictly positive threshold for a finite family, including the
empty family. It is fixed before any later coefficient center. -/
theorem finite_positive_threshold {ι : Type*} [Fintype ι]
    (δ : ι → ℝ) (hδ : ∀ i, 0<δ i) : ∃ t>0, t<2 ∧ ∀ i, t≤δ i := by
  classical
  have h (s : Finset ι) : ∃ t>0, t≤1 ∧ ∀ i∈s, t≤δ i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,le_rfl,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨t,ht,ht1,hs⟩ := ih
      refine ⟨min t (δ a),lt_min ht (hδ a),(min_le_left _ _).trans ht1,?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs i hi)
  obtain ⟨t,ht,ht1,hall⟩ := h Finset.univ
  exact ⟨t,ht,ht1.trans_lt (by norm_num),fun i => hall i (Finset.mem_univ i)⟩

def visibilitySlotCount (C V M : ℝ) : ℕ := if 1<M*V then ⌈C*M⌉₊ else 0

theorem visibilitySlotCount_bound (C V M : ℝ) (hC : 0≤C) (hV : 0≤V) (hM : 0≤M) :
    (visibilitySlotCount C V M : ℝ) ≤ (C+V)*M := by
  classical
  unfold visibilitySlotCount
  split_ifs with h
  · have hh := Nat.ceil_lt_add_one (mul_nonneg hC hM)
    nlinarith
  · simp only [Nat.cast_zero]
    exact mul_nonneg (add_nonneg hC hV) hM

def finsetVisibilitySlot {N : ℕ} (F : Finset (Fin N → ℝ)) {L : ℕ} (k : Fin L) : Fin N → ℝ :=
  if h : k.val<F.card then ((Fintype.equivFin F).symm ⟨k.val,by simpa using h⟩).val else 0

theorem finsetVisibilitySlot_surjective {N L : ℕ} (F : Finset (Fin N → ℝ))
    (hL : F.card≤L) (b : F) :
    ∃ k : Fin L, k.val<F.card ∧ finsetVisibilitySlot F k=b.val := by
  classical
  let i := Fintype.equivFin F b
  have hi : i.val<F.card := by simpa using i.isLt
  let k : Fin L := ⟨i.val,hi.trans_le hL⟩
  refine ⟨k,hi,?_⟩
  have hk : k.val<F.card := hi
  rw [finsetVisibilitySlot,dite_eq_left hk]
  have he : (⟨k.val,by simpa using hi⟩ : Fin (Fintype.card F))=i := rfl
  rw [he]
  simp [i]

theorem finite_cross_closure_not_cover {ι : Type*} [Fintype ι] {d : ℕ}
    (hd : Fintype.card ι<d)
    (A : ι → Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hsep : ∀ i, Disjoint (A i) (closure (metricSphereAntipode d ⁻¹' A i))) :
    ∃ p, ∀ i, p∉A i ∧ metricSphereAntipode d p∉A i := by
  obtain ⟨p,hp⟩ := cross_closure_antipodal_pairs_not_cover hd
    (fun k => A ((Fintype.equivFin ι).symm k)) (fun k => hsep _)
  exact ⟨p,fun i => by simpa using hp (Fintype.equivFin ι i)⟩

end KakeyaTwoScale
