module
public import KakeyaTwoScale.TupleLengthSelection

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem cube_predicate_capacity {T C : Type*} [DecidableEq T] [DecidableEq C]
    (Y : Finset T) (cube : T → C) (P : C → Prop) [DecidablePred P] (q : C) :
    ParentLevel.capacity (Y.filter fun y => P (cube y)) cube q =
      if P q then ParentLevel.capacity Y cube q else 0 := by
  classical
  unfold ParentLevel.capacity
  by_cases h : P q
  · rw [ite_eq_left h]
    congr 1
    ext y
    simp only [Finset.mem_filter]
    constructor
    · exact fun hy => ⟨hy.1.1,hy.2⟩
    · intro hy
      exact ⟨⟨hy.1,by simpa only [hy.2] using h⟩,hy.2⟩
  · rw [ite_eq_right h]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨⟨_,hP⟩,hq⟩ := Finset.mem_filter.mp hy |>.imp_left Finset.mem_filter.mp
    exact h (by simpa only [hq] using hP)

/-- Selecting whole grains preserves full current cube fibers. The actual
nonlinear mass equals the sum of the selected original grain masses. -/
theorem grain_subset_mass {T C G : Type*} [DecidableEq T] [DecidableEq C] [DecidableEq G]
    (Y : Finset T) (cube : T → C) (cubes : Finset C) (grain : C → G) (S : Finset G)
    {p : ℝ} (hp : 0 < p) :
    tupleCubeMass (Y.filter fun y => grain (cube y) ∈ S) cube cubes p =
      ∑ g ∈ S, tupleCubeMass (Y.filter fun y => grain (cube y)=g) cube cubes p := by
  classical
  unfold tupleCubeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [cube_predicate_capacity Y cube (fun q => grain q ∈ S) q]
  have hf (g : G) : ParentLevel.capacity (Y.filter fun y => grain (cube y)=g) cube q =
      if grain q=g then ParentLevel.capacity Y cube q else 0 :=
    cube_predicate_capacity Y cube (fun q => grain q=g) q
  simp_rw [hf]
  simp only [Nat.cast_ite,Nat.cast_zero]
  simp_rw [ite_pow]
  simp [Real.zero_rpow hp.ne']

/-- Actual cube capacities are unchanged whenever its grain is selected. -/
theorem selected_grain_capacity {T C G : Type*} [DecidableEq T] [DecidableEq C] [DecidableEq G]
    (Y : Finset T) (cube : T → C) (grain : C → G) (S : Finset G) {q : C}
    (hq : grain q ∈ S) :
    ParentLevel.capacity (Y.filter fun y => grain (cube y) ∈ S) cube q =
      ParentLevel.capacity Y cube q := by
  rw [cube_predicate_capacity Y cube (fun q => grain q ∈ S) q,ite_eq_left hq]

/-- Simultaneous dyadic balancing of positive real quantities on actual
finite grains, using arbitrary real weights and the exact joint-bin loss. -/
theorem joint_weighted_grain_bands {G : Type*} [DecidableEq G] {m B : ℕ}
    (S : Finset G) (quantity : G → Fin m → ℝ) (weight : G → ℝ)
    (hquantity : ∀ g ∈ S, ∀ j, 1 ≤ quantity g j ∧ quantity g j ≤ (2:ℝ)^B) :
    ∃ (band : Fin m → Fin (B+1)) (R : Finset G), R ⊆ S ∧
      (∑ g ∈ S, weight g) / (((B+1)^m:ℕ):ℝ) ≤ ∑ g ∈ R, weight g ∧
      ∀ g ∈ R, ∀ j, (2:ℝ)^(band j).val ≤ quantity g j ∧
        quantity g j < (2:ℝ)^((band j).val+1) := by
  classical
  have hex : ∀ g, ∀ j : Fin m, ∃ i : Fin (B+1), g ∈ S →
      (2:ℝ)^i.val ≤ quantity g j ∧ quantity g j < (2:ℝ)^(i.val+1) := by
    intro g j
    by_cases hg : g ∈ S
    · obtain ⟨i,hi⟩ := exists_length_band (δ:=1) (by norm_num) (hquantity g hg j).1
        (by simpa using (hquantity g hg j).2)
      exact ⟨i,fun _ => by simpa using hi⟩
    · exact ⟨0,fun h => False.elim (hg h)⟩
  choose color hc using hex
  let colors : Finset (Fin m → Fin (B+1)) := Finset.univ
  have hden : (0:ℝ) < colors.card := by simp [colors]; positivity
  have he : colors.card • ((∑ g ∈ S, weight g)/(colors.card:ℝ)) ≤ ∑ g ∈ S, weight g := by
    simp only [nsmul_eq_mul,mul_div_cancel₀ _ hden.ne']
    exact le_rfl
  obtain ⟨band,_,hret⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (s:=S) (t:=colors) (fun g _ => Finset.mem_univ (color g)) Finset.univ_nonempty he
  refine ⟨band,S.filter (fun g => color g=band),Finset.filter_subset _ _,?_,?_⟩
  · simpa [colors] using hret
  · intro g hg j
    obtain ⟨hg,heq⟩ := Finset.mem_filter.mp hg
    simpa only [heq] using hc g j hg

/-- Balance arbitrary finite grain statistics while retaining the actual
nonlinear tuple objective. All tuples of every selected grain are retained. -/
theorem actual_grain_balancing {T C G : Type*} [DecidableEq T] [DecidableEq C] [DecidableEq G]
    {m B : ℕ} (Y : Finset T) (cube : T → C) (cubes : Finset C) (grain : C → G)
    (quantity : G → Fin m → ℝ)
    (hquantity : ∀ g ∈ cubes.image grain, ∀ j,
      1 ≤ quantity g j ∧ quantity g j ≤ (2:ℝ)^B) {p : ℝ} (hp : 0 < p) :
    ∃ (band : Fin m → Fin (B+1)) (R : Finset G), R ⊆ cubes.image grain ∧
      tupleCubeMass Y cube cubes p / (((B+1)^m:ℕ):ℝ) ≤
        tupleCubeMass (Y.filter fun y => grain (cube y) ∈ R) cube cubes p ∧
      (∀ g ∈ R, ∀ j, (2:ℝ)^(band j).val ≤ quantity g j ∧
        quantity g j < (2:ℝ)^((band j).val+1)) ∧
      ∀ q ∈ cubes, grain q ∈ R →
        ParentLevel.capacity (Y.filter fun y => grain (cube y) ∈ R) cube q = ParentLevel.capacity Y cube q := by
  classical
  obtain ⟨band,R,hR,hmass,hbands⟩ := joint_weighted_grain_bands (cubes.image grain) quantity
    (fun g => tupleCubeMass (Y.filter fun y => grain (cube y)=g) cube cubes p) hquantity
  rw [cube_label_mass_eq Y cube cubes grain hp] at hmass
  rw [← grain_subset_mass Y cube cubes grain R hp] at hmass
  exact ⟨band,R,hR,hmass,hbands,fun q _ hq => selected_grain_capacity Y cube grain R hq⟩

/-- Positive factor-two balanced counts give the per-origin average bound
used by the upper reset, with an explicit constant two. -/
theorem balanced_count_average {G : Type*} (S : Finset G) (count : G → ℝ)
    {a : ℝ} (hband : ∀ g ∈ S, a ≤ count g ∧ count g ≤ 2*a) {g : G} (hg : g ∈ S) :
    count g ≤ 2*(∑ h ∈ S, count h)/(S.card:ℝ) := by
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨g,hg⟩
  have hh := Finset.sum_le_sum (fun h hh => (hband h hh).1)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  apply (le_div_iff₀ hcard).mpr
  nlinarith [(hband g hg).2]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cube_predicate_capacity
#print axioms KakeyaTwoScale.grain_subset_mass
#print axioms KakeyaTwoScale.selected_grain_capacity
#print axioms KakeyaTwoScale.joint_weighted_grain_bands
#print axioms KakeyaTwoScale.actual_grain_balancing
#print axioms KakeyaTwoScale.balanced_count_average
