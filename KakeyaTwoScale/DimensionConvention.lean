module
public import KakeyaTwoScale.BoundedAdmissibility
public import Mathlib.Order.LiminfLimsup

@[expose] public section

open MeasureTheory Metric Filter
noncomputable section
namespace KakeyaTwoScale

/-- Least cardinality of a finite open-ball cover at dyadic radius. For bounded
sets the infimum is attained, as proved below. -/
def dyadicCoverNumber {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
    K ⊆ ⋃ c ∈ C, ball c (dyadicRadius q) ∧ C.card ≤ m}

 theorem dyadicCoverNumber_spec {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Bornology.IsBounded K) (q : ℕ) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
      K ⊆ ⋃ c ∈ C, ball c (dyadicRadius q) ∧ C.card ≤ dyadicCoverNumber K q := by
  obtain ⟨S,_,hSf,hS⟩ := exists_finite_cover_balls_of_isCompact_closure
    hK.isCompact_closure (Real.exp_pos (-Real.log 2*q))
  exact Nat.sInf_mem (s := {m : ℕ | ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
    K ⊆ ⋃ c ∈ C, ball c (dyadicRadius q) ∧ C.card ≤ m})
    ⟨hSf.toFinset.card, hSf.toFinset, by simpa [dyadicRadius] using hS, le_rfl⟩

 theorem dyadicCoverNumber_le {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {q : ℕ} (C : Finset (EuclideanSpace ℝ (Fin n)))
    (hC : K ⊆ ⋃ c ∈ C, ball c (dyadicRadius q)) : dyadicCoverNumber K q ≤ C.card :=
  Nat.sInf_le ⟨C,hC,le_rfl⟩

/-- Normalized logarithm of minimal cover count. `max 1` assigns the empty set
value zero, agreeing with the nonnegative sInf convention in this project. -/
def dyadicCoverEntropy {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) : ℝ :=
  Real.log (max 1 (dyadicCoverNumber K q:ℝ)) / (Real.log 2*q)

 theorem dyadicCoverEntropy_nonneg {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) : 0 ≤ dyadicCoverEntropy K q :=
  div_nonneg (Real.log_nonneg (le_max_left _ _))
    (mul_nonneg (Real.log_pos (by norm_num)).le (Nat.cast_nonneg _))

 theorem dyadicCoverGrowth_of_entropy_bound {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K) {d : ℝ}
    (h : ∀ᶠ q : ℕ in atTop, dyadicCoverEntropy K q ≤ d) : DyadicCoverGrowth K d := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp (h.and (eventually_gt_atTop 0))
  refine ⟨1, by norm_num, Q, ?_⟩
  intro q hq
  obtain ⟨C,hC,hcard⟩ := dyadicCoverNumber_spec hK q
  refine ⟨C,hC,?_⟩
  have hpos : (0:ℝ) < q := by exact_mod_cast (hQ q hq).2
  have hb := (div_le_iff₀ (mul_pos (Real.log_pos (by norm_num)) hpos)).mp (hQ q hq).1
  have he := Real.exp_le_exp.mpr hb
  rw [Real.exp_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _))] at he
  have hc : (C.card:ℝ) ≤ dyadicCoverNumber K q := by exact_mod_cast hcard
  simpa [mul_assoc, mul_comm, mul_left_comm] using hc.trans ((le_max_right _ _).trans he)

 theorem DyadicCoverGrowth.entropy_eventually_le {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} {d : ℝ} (hd : 0 ≤ d)
    (H : DyadicCoverGrowth K d) {e : ℝ} (he : d < e) :
    ∀ᶠ q : ℕ in atTop, dyadicCoverEntropy K q ≤ e := by
  obtain ⟨C,hC,Q,hQ⟩ := H
  let B := max C 1
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have ht : Tendsto (fun q : ℕ => (Real.log B/Real.log 2)/(q:ℝ)) atTop (nhds 0) :=
    constant_over_nat_tendsto _
  have hev := ht.eventually (gt_mem_nhds (sub_pos.mpr he))
  filter_upwards [hev, eventually_ge_atTop Q, eventually_gt_atTop 0] with q hsmall hq hpos
  obtain ⟨S,hS,hcard⟩ := hQ q hq
  have hn : (dyadicCoverNumber K q:ℝ) ≤ S.card := by exact_mod_cast dyadicCoverNumber_le S hS
  have hExp : 1 ≤ Real.exp (Real.log 2*d*q) := Real.one_le_exp (by positivity)
  have hbexp : 1 ≤ B*Real.exp (Real.log 2*d*q) :=
    by nlinarith [show (1:ℝ) ≤ B from le_max_right _ _]
  have hb : max 1 (dyadicCoverNumber K q:ℝ) ≤ B*Real.exp (Real.log 2*d*q) := by
    apply max_le hbexp
    exact (hn.trans hcard).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hlog := Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hb
  rw [Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hp : (0:ℝ)<q := by exact_mod_cast hpos
  unfold dyadicCoverEntropy
  apply (div_le_iff₀ (mul_pos (Real.log_pos (by norm_num)) hp)).2
  have hs := (div_lt_iff₀ hp).mp hsmall
  have hl := (div_lt_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mp hs
  nlinarith

/-- Exact agreement with the normalized-log minimal-cover limsup, including the
empty-set value zero. This settles the dyadic open-ball convention. -/
theorem upperBoxDimension_eq_dyadic_limsup {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K) :
    upperBoxDimension K = limsup (dyadicCoverEntropy K) atTop := by
  obtain ⟨d,hd,hD⟩ := bounded_has_dyadicCoverGrowth hK
  have hb : IsBoundedUnder (· ≤ ·) atTop (dyadicCoverEntropy K) :=
    isBoundedUnder_of_eventually_le (hD.entropy_eventually_le hd (by linarith : d<d+1))
  have hc : IsCoboundedUnder (· ≤ ·) atTop (dyadicCoverEntropy K) :=
    isCoboundedUnder_le_of_le atTop (dyadicCoverEntropy_nonneg K)
  have hl0 : 0 ≤ limsup (dyadicCoverEntropy K) atTop := by
    apply le_limsup_of_le hb
    intro b hh
    obtain ⟨q,hq⟩ := hh.exists
    exact (dyadicCoverEntropy_nonneg K q).trans hq
  apply le_antisymm
  · apply le_of_forall_gt
    intro b hbl
    obtain ⟨e,hle,heb⟩ := exists_between hbl
    have he := (eventually_lt_of_limsup_lt hle hb).mono (fun _ h => h.le)
    apply lt_of_le_of_lt _ heb
    apply csInf_le (show BddBelow {d : ℝ | 0≤d ∧ DyadicCoverGrowth K d} from
      ⟨0,fun _ h => h.1⟩)
    exact ⟨hl0.trans hle.le, dyadicCoverGrowth_of_entropy_bound hK he⟩
  · unfold upperBoxDimension
    apply le_csInf (s := {e : ℝ | 0 ≤ e ∧ DyadicCoverGrowth K e}) ⟨d,hd,hD⟩
    intro e he
    exact (limsup_le_iff' hc hb).2 (fun b hb => he.2.entropy_eventually_le he.1 hb)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadicCoverNumber_spec
#print axioms KakeyaTwoScale.dyadicCoverGrowth_of_entropy_bound
#print axioms KakeyaTwoScale.DyadicCoverGrowth.entropy_eventually_le
#print axioms KakeyaTwoScale.upperBoxDimension_eq_dyadic_limsup
