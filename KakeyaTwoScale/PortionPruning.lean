module
public import KakeyaTwoScale.MeasureSelection

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical
namespace FixedParents
variable {Child Parent T : Type*} [DecidableEq Child] [DecidableEq Parent]
  [MeasurableSpace T]
variable (F : FixedParents Child Parent) (μ : Measure T) [IsFiniteMeasure μ]

/- Portions vary; the family, assignment, capacities and weight belong to F
and are never recomputed after a deletion. -/
def portionMass (I : Child → Set T) : ℝ :=
  F.fineCellVolume * ∑ x ∈ F.children, μ.real (I x)

def activeChildren (I : Child → Set T) (t : T) : Finset Child :=
  F.children.filter fun x => t ∈ I x

omit [MeasurableSpace T] in
theorem activeChildren_mono {I J : Child → Set T}
    (h : ∀ x ∈ F.children, I x ⊆ J x) (t : T) :
    F.activeChildren I t ⊆ F.activeChildren J t := by
  intro x hx
  obtain ⟨hx,ht⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,h x hx ht⟩

omit [MeasurableSpace T] in
theorem active_cap_preserved {I J : Child → Set T}
    (h : ∀ x ∈ F.children, I x ⊆ J x) (bound : ℝ)
    (hb : ∀ t p, p ∈ F.parents → (F.count (F.activeChildren J t) p : ℝ) ≤ bound) :
    ∀ t p, p ∈ F.parents → (F.count (F.activeChildren I t) p : ℝ) ≤ bound := by
  intro t
  exact F.cap_preserved (F.activeChildren_mono h t) bound (hb t)

theorem portionMass_eq_integral (I : Child → Set T)
    (hm : ∀ x ∈ F.children, MeasurableSet (I x)) :
    F.portionMass μ I = ∫ t, F.fineCellVolume * (F.activeChildren I t).card ∂μ := by
  rw [integral_const_mul]
  unfold portionMass
  congr 1
  have he : (fun t => ((F.activeChildren I t).card : ℝ)) =
      membershipCount F.children I := by
    funext t
    exact (membershipCount_eq_card F.children I t).symm
  rw [he, integral_membershipCount μ F.children I hm]

theorem portionMass_inter_loss (I J : Child → Set T)
    (hJ : ∀ x ∈ F.children, MeasurableSet (J x)) :
    F.portionMass μ (fun x => I x ∩ J x) +
      F.portionMass μ (fun x => I x \ J x) = F.portionMass μ I := by
  unfold portionMass
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun x hx => measureReal_inter_add_sdiff (hJ x hx)

/- Per-parent exceptional-set budgets aggregate against the ORIGINAL capacity.
No independence, disjointness of height sets, or surviving-child denominator is used. -/
omit [IsFiniteMeasure μ] in
theorem exceptional_budget (E : Child → Set T) (eta : ℝ)
    (hb : ∀ p ∈ F.parents,
      ∑ x ∈ F.children.filter (fun x => F.assign x = p), μ.real (E x) ≤
        eta * (F.capacity p : ℝ)) :
    F.portionMass μ E ≤ eta * F.fineCellVolume * F.children.card := by
  have hsum : ∑ x ∈ F.children, μ.real (E x) =
      ∑ p ∈ F.parents, ∑ x ∈ F.children.filter (fun x => F.assign x = p), μ.real (E x) := by
    exact (Finset.sum_fiberwise_of_maps_to F.assigned _).symm
  have hcard : (∑ p ∈ F.parents, (F.capacity p : ℝ)) = F.children.card := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise F.assigned).symm
  unfold portionMass
  rw [hsum]
  calc
    _ ≤ F.fineCellVolume * ∑ p ∈ F.parents, eta * (F.capacity p : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) F.fine_nonneg
    _ = _ := by rw [← Finset.mul_sum, hcard]; ring

/- Arithmetic pruning can be applied to portions already narrowed by earlier
steps; the discarded mass is bounded by the original exceptional-set budget. -/
theorem prune_by_parent_budget (I J : Child → Set T) (eta : ℝ)
    (hJ : ∀ x ∈ F.children, MeasurableSet (J x))
    (hb : ∀ p ∈ F.parents,
      ∑ x ∈ F.children.filter (fun x => F.assign x = p), μ.real (I x \ J x) ≤
        eta * (F.capacity p : ℝ)) :
    F.portionMass μ I - eta * F.fineCellVolume * F.children.card ≤
      F.portionMass μ (fun x => I x ∩ J x) := by
  have h := F.portionMass_inter_loss μ I J hJ
  have hbudget := F.exceptional_budget μ (fun x => I x \ J x) eta hb
  linarith

/- Exact low-cell deletion accounting for measured portions. The partition is
actual child-to-cell assignment; integrability of discarded mass is derived. -/
theorem low_cell_deletion_cost {Cell : Type*} [DecidableEq Cell]
    (D : Child → Set T) (hm : ∀ x ∈ F.children, MeasurableSet (D x))
    (cell : Child → T → Cell) (lowCells : T → Finset Cell)
    (covering : T → Cell → Finset Parent) (M V : ℝ) (hM : 0 ≤ M)
    (hcell : ∀ x ∈ F.children, ∀ t ∈ D x, cell x t ∈ lowCells t)
    (hp : ∀ t c, c ∈ lowCells t → covering t c ⊆ F.parents)
    (hcover : ∀ t c, c ∈ lowCells t → ∀ x ∈ F.children,
      t ∈ D x → cell x t = c → F.assign x ∈ covering t c)
    (hlow : ∀ t c, c ∈ lowCells t → F.weight*(covering t c).card ≤ M)
    (hvol : Integrable (fun t => F.coarseCellVolume*(lowCells t).card) μ)
    (hV : (∫ t, F.coarseCellVolume*(lowCells t).card ∂μ) ≤ V) :
    F.portionMass μ D ≤ 2*M*V := by
  have hpoint (t : T) : F.fineCellVolume*(F.activeChildren D t).card ≤
      2*M*(F.coarseCellVolume*(lowCells t).card) := by
    let selected := fun c => (F.activeChildren D t).filter (fun x => cell x t = c)
    have hmap : ∀ x ∈ F.activeChildren D t, cell x t ∈ lowCells t := by
      intro x hx
      obtain ⟨hx,ht⟩ := Finset.mem_filter.mp hx
      exact hcell x hx t ht
    have hcard : ((F.activeChildren D t).card : ℝ) =
        ∑ c ∈ lowCells t, ((selected c).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
    have hmass := F.low_cells_loss (lowCells t) selected (covering t) M
      (fun c _ => (Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      (hp t) (fun c hc x hx => by
        obtain ⟨hx,hxc⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx,hxt⟩ := Finset.mem_filter.mp hx
        exact hcover t c hc x hx hxt hxc) (hlow t)
    rw [hcard, Finset.mul_sum]
    exact hmass
  rw [F.portionMass_eq_integral μ D hm]
  calc
    _ ≤ ∫ t, 2*M*(F.coarseCellVolume*(lowCells t).card) ∂μ := by
      apply integral_mono _ (hvol.const_mul _) hpoint
      exact (integrable_card_filter μ F.children D hm).const_mul _
    _ = 2*M*(∫ t, F.coarseCellVolume*(lowCells t).card ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hV (by positivity)

def longPortions (_F : FixedParents Child Parent) (μ : Measure T) (I : Child → Set T) (eta : ℝ) (x : Child) : Set T :=
  if eta ≤ μ.real (I x) then I x else ∅

omit [IsFiniteMeasure μ] in
theorem longPortions_subset (I : Child → Set T) (eta : ℝ) (x : Child) :
    F.longPortions μ I eta x ⊆ I x := by
  unfold longPortions
  split_ifs <;> simp

omit [IsFiniteMeasure μ] in
theorem longPortions_measurable (I : Child → Set T) (eta : ℝ) {x : Child}
    (hx : MeasurableSet (I x)) : MeasurableSet (F.longPortions μ I eta x) := by
  unfold longPortions
  split_ifs <;> simp_all

omit [IsFiniteMeasure μ] in
theorem longPortions_mass_lower (I : Child → Set T) (eta : ℝ) (he : 0 ≤ eta) :
    F.portionMass μ I - eta * F.fineCellVolume * F.children.card ≤
      F.portionMass μ (F.longPortions μ I eta) := by
  have hb : ∀ x ∈ F.children, μ.real (I x) ≤ eta + μ.real (F.longPortions μ I eta x) := by
    intro x _
    unfold longPortions
    split_ifs with hx
    · linarith
    · simp only [measureReal_empty, add_zero]
      exact le_of_lt (lt_of_not_ge hx)
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) F.fine_nonneg
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  unfold portionMass
  nlinarith

omit [IsFiniteMeasure μ] in
theorem longPortions_mass_of_nonempty (I : Child → Set T) (eta : ℝ) {x : Child}
    (hx : (F.longPortions μ I eta x).Nonempty) :
    eta ≤ μ.real (F.longPortions μ I eta x) := by
  unfold longPortions at hx ⊢
  split_ifs with h
  · exact h
  · simp [h] at hx

/- Three actual portion deletions preserve the source's U/4 budget. -/
omit [IsFiniteMeasure μ] in
theorem final_portion_mass (I₀ I₁ I₂ : Child → Set T)
    (hstart : 3*(F.fineCellVolume*F.children.card)/8 ≤ F.portionMass μ I₀)
    (hfirst : F.portionMass μ I₀ - (F.fineCellVolume*F.children.card)/100 ≤ F.portionMass μ I₁)
    (hsecond : F.portionMass μ I₁ - 2*(F.fineCellVolume*F.children.card)/100 ≤ F.portionMass μ I₂) :
    (F.fineCellVolume*F.children.card)/4 ≤
      F.portionMass μ (F.longPortions μ I₂ (1/100)) := by
  have ht := F.longPortions_mass_lower μ I₂ (1/100) (by norm_num)
  have hU : 0 ≤ F.fineCellVolume*F.children.card := mul_nonneg F.fine_nonneg (by positivity)
  nlinarith
end FixedParents
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FixedParents.exceptional_budget
#print axioms KakeyaTwoScale.FixedParents.prune_by_parent_budget
#print axioms KakeyaTwoScale.FixedParents.active_cap_preserved
#print axioms KakeyaTwoScale.FixedParents.final_portion_mass

#print axioms KakeyaTwoScale.FixedParents.low_cell_deletion_cost
