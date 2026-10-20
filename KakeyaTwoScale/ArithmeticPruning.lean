module
public import KakeyaTwoScale.MeasureSelection
public import KakeyaTwoScale.Exponents
public import KakeyaTwoScale.GridRegion

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- An explicit threshold coefficient depending only on the shaded-volume
constant c and the prescribed deletion fraction eta. -/
def pruningCoefficient (c eta : ℝ) : ℝ := 1 + 1/(c*(eta/2)^a)

theorem pruningCoefficient_pos {c eta : ℝ} (hc : 0 < c) (he : 0 < eta) :
    0 < pruningCoefficient c eta := by unfold pruningCoefficient; positivity

/-- The numerical heart of arithmetic pruning: the Markov upper volume and
shaded-volume lower bound force few long-exception segments. Neither volume
estimate is postulated as an axiom; both are explicit premises. -/
theorem long_exception_count_bound (N B volume cellVolume c eta : ℝ)
    (hN : 0 < N) (hB : 0 ≤ B) (hr : 0 < cellVolume)
    (hc : 0 < c) (he : 0 < eta)
    (hupper : (pruningCoefficient c eta * N^theta)*volume ≤ cellVolume*N)
    (hlower : c*cellVolume*B^a ≤ volume) :
    B ≤ eta*N/2 := by
  have ha : 0 < a := by norm_num [a]
  have hT : 0 < pruningCoefficient c eta * N^theta := by
    exact mul_pos (pruningCoefficient_pos hc he) (Real.rpow_pos_of_pos hN _)
  have hmul := (mul_le_mul_of_nonneg_left hlower hT.le).trans hupper
  have hcancel : pruningCoefficient c eta*c*(B^a*N^theta) ≤ N := by nlinarith
  have hco : 1 ≤ pruningCoefficient c eta*c*(eta/2)^a := by
    have hp : 0 < c*(eta/2)^a := by positivity
    unfold pruningCoefficient
    have hh : (1+1/(c*(eta/2)^a))*(c*(eta/2)^a) = c*(eta/2)^a+1 := by field_simp
    nlinarith
  apply (Real.rpow_le_rpow_iff hB (by positivity) ha).mp
  by_contra h
  have hpow : (eta*N/2)^a < B^a := lt_of_not_ge h
  have hid : (eta*N/2)^a * N^theta = (eta/2)^a*N := by
    rw [show eta*N/2 = (eta/2)*N by ring, Real.mul_rpow (by positivity) hN.le]
    rw [mul_assoc, ← Real.rpow_add hN]
    norm_num [a,theta]
  have hstrict := mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hN theta)
  rw [hid] at hstrict
  have hstrict' := mul_lt_mul_of_pos_left hstrict (mul_pos (pruningCoefficient_pos hc he) hc)
  have hbase := mul_le_mul_of_nonneg_right hco hN.le
  nlinarith

/-- Exceptional length accounting with the long-exception family constructed
by filtering. Lengths at most one and the count bound imply the full eta N loss. -/
theorem exceptional_length_budget {J : Type*} (family : Finset J)
    (length : J → ℝ) (eta : ℝ) (he : 0 ≤ eta)
    (hlength : ∀ j ∈ family, length j ≤ 1)
    (hlong : ((family.filter (fun j => eta/2 ≤ length j)).card : ℝ) ≤ eta*family.card/2) :
    (∑ j ∈ family, length j) ≤ eta*family.card := by
  let B := family.filter (fun j => eta/2 ≤ length j)
  have hsplit : (∑ j ∈ family, length j) = (∑ j ∈ B, length j) +
      ∑ j ∈ family.filter (fun j => ¬ eta/2 ≤ length j), length j := by
    exact (Finset.sum_filter_add_sum_filter_not family _ _).symm
  have hb : (∑ j ∈ B, length j) ≤ B.card := by
    calc
      _ ≤ ∑ _j ∈ B, (1:ℝ) := Finset.sum_le_sum fun j hj => hlength j (Finset.mem_filter.mp hj).1
      _ = _ := by simp
  have hs : (∑ j ∈ family.filter (fun j => ¬ eta/2 ≤ length j), length j) ≤ eta*family.card/2 := by
    calc
      _ ≤ ∑ _j ∈ family.filter (fun j => ¬ eta/2 ≤ length j), eta/2 :=
        Finset.sum_le_sum fun j hj => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hj).2)
      _ = ((family.filter (fun j => ¬ eta/2 ≤ length j)).card : ℝ)*(eta/2) := by simp
      _ ≤ (family.card : ℝ)*(eta/2) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_filter_le family _) (by positivity)
      _ = _ := by ring
  rw [hsplit]
  change (B.card : ℝ) ≤ eta*family.card/2 at hlong
  linarith

variable {J Cell T : Type*} [MeasurableSpace T]

def axisMultiplicity (family : Finset J) (cell : J → T → Cell) (j : J) (t : T) : ℝ :=
  membershipCount family (fun i => {t | cell i t = cell j t}) t

def multiplicityRetained (family : Finset J) (cell : J → T → Cell)
    (I : Set T) (threshold : ℝ) (j : J) : Set T :=
  I ∩ {t | axisMultiplicity family cell j t ≤ threshold}

theorem measurableSet_multiplicityRetained (family : Finset J) (cell : J → T → Cell)
    (I : Set T) (hI : MeasurableSet I) (threshold : ℝ)
    (hm : ∀ i ∈ family, ∀ j, MeasurableSet {t | cell i t = cell j t}) (j : J) :
    MeasurableSet (multiplicityRetained family cell I threshold j) := by
  apply hI.inter
  apply measurableSet_le _ measurable_const
  exact Finset.measurable_sum _ fun i hi => measurable_const.indicator (hm i hi j)

/- Removing high-multiplicity heights gives an EVERYWHERE per-cell cap,
including cells not occupied by the retained family. -/
omit [MeasurableSpace T] in
theorem multiplicityRetained_cap (family : Finset J) (cell : J → T → Cell)
    (I : Set T) (threshold : ℝ) (hT : 0 ≤ threshold) (t : T) (c : Cell) :
    ((family.filter fun j => t ∈ multiplicityRetained family cell I threshold j ∧ cell j t = c).card : ℝ) ≤ threshold := by
  let S := family.filter fun j => t ∈ multiplicityRetained family cell I threshold j ∧ cell j t = c
  by_cases hne : S.Nonempty
  · obtain ⟨j,hj⟩ := hne
    obtain ⟨_,ht,hjc⟩ := Finset.mem_filter.mp hj
    have hsub : S ⊆ family.filter (fun i => cell i t = cell j t) := by
      intro i hi
      obtain ⟨hi,_,hic⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hi,hic.trans hjc.symm⟩
    have hcard : (S.card : ℝ) ≤ ((family.filter fun i => cell i t = cell j t).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hc := ht.2
    change axisMultiplicity family cell j t ≤ threshold at hc
    unfold axisMultiplicity at hc
    rw [membershipCount_eq_card] at hc
    exact hcard.trans hc
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    change (S.card : ℝ) ≤ threshold
    simpa [he] using hT
/-- Conditional arithmetic pruning with an explicit uniform threshold. The
only analytic premises are the Markov and shaded bounds for the SAME high
region and the constructed long-exception family. The retained sets, length
budget, measurability and everywhere cap are conclusions. -/
theorem pruning_from_volume_bounds
    (μ : Measure T) [IsProbabilityMeasure μ] (family : Finset J) (hne : family.Nonempty)
    (cell : J → T → Cell) (c eta cellVolume highVolume : ℝ)
    (hc : 0 < c) (he : 0 < eta) (hr : 0 < cellVolume)
    (hm : ∀ i ∈ family, ∀ j, MeasurableSet {t | cell i t = cell j t})
    (hupper : (pruningCoefficient c eta * (family.card:ℝ)^theta)*highVolume ≤ cellVolume*family.card)
    (hlower : c*cellVolume*
      (((family.filter fun j => eta/2 ≤ μ.real {t | pruningCoefficient c eta*(family.card:ℝ)^theta <
        axisMultiplicity family cell j t}).card : ℝ)^a) ≤ highVolume) :
    ∃ I : J → Set T,
      (∀ j, MeasurableSet (I j)) ∧
      (1-eta)*family.card ≤ ∑ j ∈ family, μ.real (I j) ∧
      ∀ t k, ((family.filter fun j => t ∈ I j ∧ cell j t = k).card : ℝ) ≤
        pruningCoefficient c eta*(family.card:ℝ)^theta := by
  let threshold := pruningCoefficient c eta*(family.card:ℝ)^theta
  let bad := fun j => {t | threshold < axisMultiplicity family cell j t}
  have hbad : ∀ j, MeasurableSet (bad j) := by
    intro j
    apply measurableSet_lt measurable_const
    exact Finset.measurable_sum _ fun i hi => measurable_const.indicator (hm i hi j)
  have hN : (0:ℝ) < family.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hcount : ((family.filter fun j => eta/2 ≤ μ.real (bad j)).card : ℝ) ≤ eta*family.card/2 :=
    long_exception_count_bound _ _ highVolume cellVolume c eta hN (by positivity) hr hc he hupper hlower
  have hlen : ∀ j ∈ family, μ.real (bad j) ≤ 1 := by
    intro j _
    simp
  have hbudget := exceptional_length_budget family (fun j => μ.real (bad j)) eta he.le hlen hcount
  let I := multiplicityRetained family cell Set.univ threshold
  have hcomp (j) : I j = (bad j)ᶜ := by
    ext t
    simp [I, multiplicityRetained, bad, not_lt]
  refine ⟨I, ?_, ?_, ?_⟩
  · intro j
    rw [hcomp]
    exact (hbad j).compl
  · have heq : (∑ j ∈ family, μ.real (I j)) = (family.card:ℝ) - ∑ j ∈ family, μ.real (bad j) := by
      simp_rw [hcomp, measureReal_compl (hbad _), probReal_univ]
      rw [Finset.sum_sub_distrib]
      simp
    rw [heq]
    nlinarith
  · exact multiplicityRetained_cap family cell Set.univ threshold
      (by dsimp [threshold]; exact mul_nonneg (pruningCoefficient_pos hc he).le (Real.rpow_nonneg (by positivity) _))

/-- The affine grid translation in the source is absorbed exactly into the
intercept and slope. It is not restricted to a stationary grid. -/
theorem affine_grid_cell_identity {n : ℕ} (b v xi zeta : Fin n → ℝ) (r t : ℝ) :
    gridIndex r (segmentPoint b v t-(xi+t • zeta)) =
      gridIndex r (segmentPoint (b-xi) (v-zeta) t) := by
  congr 1
  unfold segmentPoint
  rw [smul_sub]
  abel

/-- All cell-coincidence events required by arithmetic pruning are measurable,
including the source's uniformly affine-translated horizontal grids. -/
theorem measurable_affine_grid_coincidence {n : ℕ} (b v b' v' xi zeta : Fin n → ℝ) (r : ℝ) :
    MeasurableSet {t : ℝ |
      gridIndex r (segmentPoint b v t-(xi+t • zeta)) =
      gridIndex r (segmentPoint b' v' t-(xi+t • zeta))} := by
  simp_rw [affine_grid_cell_identity]
  apply measurableSet_eq_fun
  · exact (measurable_gridIndex r).comp
      (continuous_const.add (continuous_id.smul continuous_const)).measurable
  · exact (measurable_gridIndex r).comp
      (continuous_const.add (continuous_id.smul continuous_const)).measurable

end KakeyaTwoScale
#print axioms KakeyaTwoScale.long_exception_count_bound
#print axioms KakeyaTwoScale.exceptional_length_budget
#print axioms KakeyaTwoScale.measurableSet_multiplicityRetained
#print axioms KakeyaTwoScale.multiplicityRetained_cap

#print axioms KakeyaTwoScale.pruning_from_volume_bounds

#print axioms KakeyaTwoScale.measurable_affine_grid_coincidence
