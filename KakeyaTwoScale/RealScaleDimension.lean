module
public import KakeyaTwoScale.DimensionConvention

@[expose] public section

open MeasureTheory Metric Filter
noncomputable section
namespace KakeyaTwoScale

/-- Minimal finite open-ball cover count at radius `exp(-log(2)*t)`, where the
logarithmic scale `t` is real rather than restricted to integers. -/
def realScaleCoverNumber {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
    K ⊆ ⋃ c ∈ C, ball c (Real.exp (-Real.log 2*t)) ∧ C.card ≤ m}

def realScaleCoverEntropy {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) : ℝ :=
  Real.log (max 1 (realScaleCoverNumber K t:ℝ)) / (Real.log 2*t)

 theorem realScaleCoverEntropy_nat {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) :
    realScaleCoverEntropy K (q:ℝ) = dyadicCoverEntropy K q := rfl

 theorem realScaleCoverEntropy_nonneg {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ realScaleCoverEntropy K t :=
  div_nonneg (Real.log_nonneg (le_max_left _ _))
    (mul_nonneg (Real.log_pos (by norm_num)).le ht)

/-- Rounding a real scale upwards refines its cover. This proves that restricting
to dyadic scales does not miss any covering obstruction between scales. -/
theorem realScaleCoverNumber_le_ceil {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K) (t : ℝ) :
    realScaleCoverNumber K t ≤ dyadicCoverNumber K ⌈t⌉₊ := by
  obtain ⟨C,hC,hcard⟩ := dyadicCoverNumber_spec hK ⌈t⌉₊
  apply Nat.sInf_le
  refine ⟨C,?_,hcard⟩
  intro x hx
  obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hC hx)
  refine Set.mem_iUnion₂.mpr ⟨c,hc,ball_subset_ball ?_ hxc⟩
  apply Real.exp_le_exp.mpr
  have := Nat.le_ceil t
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [Nat.le_ceil t]

 theorem DyadicCoverGrowth.real_entropy_eventually_le {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K)
    {d : ℝ} (hd : 0 ≤ d) (H : DyadicCoverGrowth K d) {e : ℝ} (he : d < e) :
    ∀ᶠ t : ℝ in atTop, realScaleCoverEntropy K t ≤ e := by
  obtain ⟨C,hC,Q,hQ⟩ := H
  let B := max C 1
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : Tendsto (fun t : ℝ => (Real.log B/Real.log 2+d)/t) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero : Tendsto
        (fun t : ℝ => (Real.log B/Real.log 2+d)*t⁻¹) atTop (nhds (_*0)))
  have hev := ht.eventually (gt_mem_nhds (sub_pos.mpr he))
  filter_upwards [hev, eventually_ge_atTop (Q:ℝ), eventually_gt_atTop (0:ℝ)] with t hs hQle htpos
  have hq : Q ≤ ⌈t⌉₊ := by exact_mod_cast hQle.trans (Nat.le_ceil t)
  obtain ⟨S,hS,hcard⟩ := hQ ⌈t⌉₊ hq
  have hn : (realScaleCoverNumber K t:ℝ) ≤ S.card := by
    exact_mod_cast (realScaleCoverNumber_le_ceil hK t).trans (dyadicCoverNumber_le S hS)
  have hExp : 1 ≤ Real.exp (Real.log 2*d*(t+1)) := Real.one_le_exp (by positivity)
  have hbexp : 1 ≤ B*Real.exp (Real.log 2*d*(t+1)) := by
    nlinarith [show (1:ℝ) ≤ B from le_max_right _ _]
  have hround : Real.exp (Real.log 2*d*(⌈t⌉₊:ℝ)) ≤ Real.exp (Real.log 2*d*(t+1)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one htpos.le).le (mul_nonneg hl.le hd)
  have hb : max 1 (realScaleCoverNumber K t:ℝ) ≤ B*Real.exp (Real.log 2*d*(t+1)) := by
    apply max_le hbexp
    exact (hn.trans hcard).trans (mul_le_mul (le_max_left _ _) hround (Real.exp_pos _).le hB.le)
  have hlog := Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hb
  rw [Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  unfold realScaleCoverEntropy
  apply (div_le_iff₀ (mul_pos hl htpos)).2
  have hs' := (div_lt_iff₀ htpos).mp hs
  have hident : (Real.log B/Real.log 2+d)*Real.log 2 = Real.log B+d*Real.log 2 := by
    field_simp
  nlinarith [mul_lt_mul_of_pos_right hs' hl]

/-- Exact normalized-log covering convention at every positive scale:
`r = exp(-log(2)*t)` runs over all positive radii, with `t → ∞` corresponding
to `r → 0`. This is not merely a subsequence equality. -/
theorem upperBoxDimension_eq_realScale_limsup {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K) :
    upperBoxDimension K = limsup (realScaleCoverEntropy K) atTop := by
  obtain ⟨d,hd,hD⟩ := bounded_has_dyadicCoverGrowth hK
  have hb : IsBoundedUnder (· ≤ ·) atTop (realScaleCoverEntropy K) :=
    isBoundedUnder_of_eventually_le (hD.real_entropy_eventually_le hK hd (by linarith : d<d+1))
  have hc : IsCoboundedUnder (· ≤ ·) atTop (realScaleCoverEntropy K) :=
    isCoboundedUnder_le_of_eventually_le atTop
      ((eventually_ge_atTop (0:ℝ)).mono (fun t ht => realScaleCoverEntropy_nonneg K ht))
  apply le_antisymm
  · rw [upperBoxDimension_eq_dyadic_limsup hK]
    apply le_limsup_of_le hb
    intro b hh
    have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hh
    exact limsup_le_of_le
      (isCoboundedUnder_le_of_le atTop (dyadicCoverEntropy_nonneg K)) hn
  · unfold upperBoxDimension
    apply le_csInf (s := {e : ℝ | 0 ≤ e ∧ DyadicCoverGrowth K e}) ⟨d,hd,hD⟩
    intro e he
    exact (limsup_le_iff' hc hb).2 (fun b hb => he.2.real_entropy_eventually_le hK he.1 hb)

/-- Minimal number of radius-r open balls covering K. -/
def openBallCoverNumber {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
    K ⊆ ⋃ c ∈ C, ball c r ∧ C.card ≤ m}

/-- The usual upper Minkowski normalized logarithm, with empty-set value zero. -/
def openBallCoverEntropy {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) : ℝ :=
  Real.log (max 1 (openBallCoverNumber K r:ℝ)) / (-Real.log r)

 theorem map_realScaleRadius_atTop :
    map (fun t : ℝ => Real.exp (-Real.log 2*t)) atTop = nhdsWithin 0 (Set.Ioi 0) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm : map (fun t : ℝ => Real.log 2*t) atTop = atTop := by
    simpa [div_eq_mul_inv, mul_comm] using map_div_atTop_eq (Real.log 2)⁻¹ (inv_pos.mpr hl)
  calc
    map (fun t : ℝ => Real.exp (-Real.log 2*t)) atTop =
      map Real.exp (map Neg.neg (map (fun t : ℝ => Real.log 2*t) atTop)) := by
        simp only [map_map, Function.comp_def, neg_mul]
    _ = nhdsWithin 0 (Set.Ioi 0) := by rw [hm, map_neg_atTop, Real.map_exp_atBot]

/-- Exact upper-Minkowski convention equivalence at arbitrary radii r → 0+.
This uses minimal covers by open metric balls, not a dyadic-only surrogate. -/
theorem upperBoxDimension_eq_radius_limsup {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Bornology.IsBounded K) :
    upperBoxDimension K = limsup (openBallCoverEntropy K) (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [upperBoxDimension_eq_realScale_limsup hK, ← map_realScaleRadius_atTop,
    ← limsup_comp]
  apply limsup_congr
  apply Eventually.of_forall
  intro t
  simp only [Function.comp_def, openBallCoverEntropy, realScaleCoverEntropy,
    Real.log_exp, neg_mul, neg_neg]
  simp only [realScaleCoverNumber, openBallCoverNumber, neg_mul]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.realScaleCoverNumber_le_ceil
#print axioms KakeyaTwoScale.DyadicCoverGrowth.real_entropy_eventually_le
#print axioms KakeyaTwoScale.upperBoxDimension_eq_realScale_limsup

#print axioms KakeyaTwoScale.upperBoxDimension_eq_radius_limsup
