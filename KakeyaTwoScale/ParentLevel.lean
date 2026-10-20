module
public import KakeyaTwoScale.FixedParents
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Nat.Log

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ParentLevel
variable {Child Parent : Type*} [DecidableEq Child] [DecidableEq Parent]

def capacity (S : Finset Child) (assign : Child → Parent) (p : Parent) : ℕ :=
  (S.filter fun x => assign x=p).card

def selected (S : Finset Child) (assign : Child → Parent) (j : ℕ) : Finset Child :=
  S.filter fun x => (capacity S assign (assign x)).log2=j

omit [DecidableEq Child] in
theorem capacity_pos (S : Finset Child) (assign : Child → Parent) {x : Child}
    (hx : x∈S) : 0 < capacity S assign (assign x) := by
  apply Finset.card_pos.mpr
  exact ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩

omit [DecidableEq Child] in
theorem capacity_le (S : Finset Child) (assign : Child → Parent) (p : Parent) :
    capacity S assign p ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)

omit [DecidableEq Child] in
/-- Dyadic selection by original fiber capacities, with exact logarithmic retention. -/
theorem exists_level (S : Finset Child) (assign : Child → Parent) :
    ∃ j ≤ S.card.log2, (S.card:ℝ)/((S.card.log2+1:ℕ):ℝ) ≤
      ((selected S assign j).card:ℝ) := by
  let f : Child → ℕ := fun x => (capacity S assign (assign x)).log2
  let levels := Finset.range (S.card.log2+1)
  have hm : ∀ x∈S, f x ∈ levels := by
    intro x hx
    have hp := capacity_pos S assign hx
    have hc := capacity_le S assign (assign x)
    have hs : S.card ≠ 0 := by omega
    have ha := (Nat.le_log2 (ne_of_gt hp)).mp (le_refl (f x))
    have hb := (Nat.le_log2 hs).mpr (ha.trans hc)
    exact Finset.mem_range.mpr (by dsimp [f] at *; omega)
  have hn : levels.Nonempty := ⟨0,Finset.mem_range.mpr (by omega)⟩
  have hden : (0:ℝ)<((S.card.log2+1:ℕ):ℝ) := by positivity
  have he : levels.card • ((S.card:ℝ)/((S.card.log2+1:ℕ):ℝ)) ≤ (S.card:ℝ) := by
    simp only [levels,Finset.card_range,nsmul_eq_mul]
    exact le_of_eq (mul_div_cancel₀ _ hden.ne')
  obtain ⟨j,hj,hret⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hm hn he
  exact ⟨j,by simpa only [levels,Finset.mem_range,Nat.lt_add_one_iff] using hj,hret⟩

omit [DecidableEq Child] in
theorem selected_subset (S : Finset Child) (assign : Child → Parent) (j : ℕ) :
    selected S assign j ⊆ S := Finset.filter_subset _ _

omit [DecidableEq Child] in
/-- Every represented parent's entire original fiber survives the level selection. -/
theorem fiber_unchanged (S : Finset Child) (assign : Child → Parent) (j : ℕ)
    {p : Parent} (hp : p∈(selected S assign j).image assign) :
    (selected S assign j).filter (fun x => assign x=p) = S.filter (fun x => assign x=p) := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  have hj := (Finset.mem_filter.mp hx).2
  ext y
  simp only [selected,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hy,heq⟩
    exact ⟨⟨hy,by simpa [heq] using hj⟩,heq⟩

omit [DecidableEq Child] in
theorem capacity_band (S : Finset Child) (assign : Child → Parent) (j : ℕ)
    {p : Parent} (hp : p∈(selected S assign j).image assign) :
    2^j ≤ capacity S assign p ∧ capacity S assign p < 2^(j+1) := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  have hxs := (Finset.mem_filter.mp hx).1
  have hj := (Finset.mem_filter.mp hx).2
  have hn := ne_of_gt (capacity_pos S assign hxs)
  constructor
  · exact (Nat.le_log2 hn).mp (by omega)
  · exact (Nat.log2_lt hn).mp (by omega)

def commonWeight (fine coarse : ℝ) (j : ℕ) : ℝ := fine*(2:ℝ)^j/coarse

theorem commonWeight_pos {fine coarse : ℝ} (hf : 0<fine) (hc : 0<coarse) (j : ℕ) :
    0<commonWeight fine coarse j := by unfold commonWeight; positivity

omit [DecidableEq Child] in
theorem normalized_capacity_band (S : Finset Child) (assign : Child → Parent)
    (j : ℕ) {fine coarse : ℝ} (hf : 0<fine) (hc : 0<coarse)
    {p : Parent} (hp : p∈(selected S assign j).image assign) :
    commonWeight fine coarse j ≤ fine*(capacity S assign p)/coarse ∧
    fine*(capacity S assign p)/coarse < 2*commonWeight fine coarse j := by
  have hb := capacity_band S assign j hp
  have hlo : (2:ℝ)^j ≤ (capacity S assign p:ℝ) := by exact_mod_cast hb.1
  have hhi : (capacity S assign p:ℝ) < 2*(2:ℝ)^j := by
    have hh : (capacity S assign p:ℝ) < (2:ℝ)^(j+1) := by exact_mod_cast hb.2
    simpa [pow_succ,mul_comm] using hh
  unfold commonWeight
  constructor
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlo hf.le) hc.le
  · have hh := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hhi hf) hc
    convert hh using 1
    ring

/-- An actual fixed-parent object: capacities come from the selected children,
which contain every original child assigned to a selected parent. -/
def fixed (S : Finset Child) (assign : Child → Parent) (j : ℕ)
    (fine coarse : ℝ) (hf : 0<fine) (hc : 0<coarse) : FixedParents Child Parent where
  children := selected S assign j
  parents := (selected S assign j).image assign
  assign := assign
  assigned := fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩
  fineCellVolume := fine
  coarseCellVolume := coarse
  weight := commonWeight fine coarse j
  fine_nonneg := hf.le
  coarse_pos := hc
  weight_pos := commonWeight_pos hf hc j
  capacity_bound := by
    intro p hp
    rw [fiber_unchanged S assign j hp]
    have hb := (normalized_capacity_band S assign j hf hc hp).2
    have hh := (div_lt_iff₀ hc).mp hb
    exact hh.le

 theorem fixed_capacity_original (S : Finset Child) (assign : Child → Parent) (j : ℕ)
    (fine coarse : ℝ) (hf : 0<fine) (hc : 0<coarse)
    {p : Parent} (hp : p∈(fixed S assign j fine coarse hf hc).parents) :
    (fixed S assign j fine coarse hf hc).capacity p = capacity S assign p := by
  change ((selected S assign j).filter (fun x => assign x=p)).card = _
  rw [fiber_unchanged S assign j hp]
  rfl

/-- No dyadic level, immutable capacities, or retention bound is assumed. -/
theorem exists_fixed_level (S : Finset Child) (assign : Child → Parent)
    (fine coarse : ℝ) (hf : 0<fine) (hc : 0<coarse) :
    ∃ j ≤ S.card.log2,
      fine*(S.card:ℝ)/((S.card.log2+1:ℕ):ℝ) ≤
        fine*((fixed S assign j fine coarse hf hc).children.card:ℝ) := by
  obtain ⟨j,hj,hm⟩ := exists_level S assign
  refine ⟨j,hj,?_⟩
  simpa [fixed,mul_div_assoc] using (mul_le_mul_of_nonneg_left hm hf.le)

theorem log2_le_of_card_bound {N A : ℕ} (hN : N ≤ 2^A) : N.log2 ≤ A := by
  rw [Nat.log2_eq_log_two]
  simpa only [Nat.log_pow (by norm_num : 1<2)] using (Nat.log_mono_right (b:=2) hN)

/-- Any established exponential counting bound converts the exact loss to
its exponent plus one. For N<=2^(A*q+B), this denominator is A*q+B+1. -/
theorem exists_fixed_level_of_card_bound (S : Finset Child) (assign : Child → Parent)
    (fine coarse : ℝ) (hf : 0<fine) (hc : 0<coarse)
    (A : ℕ) (hN : S.card ≤ 2^A) :
    ∃ j ≤ A,
      fine*(S.card:ℝ)/((A+1:ℕ):ℝ) ≤
        fine*((fixed S assign j fine coarse hf hc).children.card:ℝ) := by
  obtain ⟨j,hj,hm⟩ := exists_fixed_level S assign fine coarse hf hc
  have hlog := log2_le_of_card_bound hN
  refine ⟨j,hj.trans hlog,le_trans ?_ hm⟩
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast (Nat.add_le_add_right hlog 1)

omit [DecidableEq Child] in
/-- Original nonempty families produce a nonempty retained family. -/
theorem selected_nonempty_of_retention (S : Finset Child) (assign : Child → Parent)
    (j : ℕ) (hS : S.Nonempty)
    (hret : (S.card:ℝ)/((S.card.log2+1:ℕ):ℝ) ≤ ((selected S assign j).card:ℝ)) :
    (selected S assign j).Nonempty := by
  have hcard : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hpos : (0:ℝ)<(selected S assign j).card :=
    (div_pos hcard (by positivity)).trans_le hret
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

end ParentLevel
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ParentLevel.exists_level
#print axioms KakeyaTwoScale.ParentLevel.fiber_unchanged
#print axioms KakeyaTwoScale.ParentLevel.capacity_band

#print axioms KakeyaTwoScale.ParentLevel.normalized_capacity_band
#print axioms KakeyaTwoScale.ParentLevel.fixed
#print axioms KakeyaTwoScale.ParentLevel.fixed_capacity_original
#print axioms KakeyaTwoScale.ParentLevel.exists_fixed_level

#print axioms KakeyaTwoScale.ParentLevel.log2_le_of_card_bound
#print axioms KakeyaTwoScale.ParentLevel.exists_fixed_level_of_card_bound
#print axioms KakeyaTwoScale.ParentLevel.selected_nonempty_of_retention
