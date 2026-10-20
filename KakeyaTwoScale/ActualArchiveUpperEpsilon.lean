module
public import KakeyaTwoScale.ActualStageUpperEpsilon

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem archiveDegreeCalendar_mono (n t J0 : ℕ) (hn : 1 ≤ n) :
    Monotone (archiveDegreeCalendar n t J0) := by
  apply monotone_nat_of_le_succ
  intro r
  simp only [archiveDegreeCalendar]
  have hh : 1 ≤ 2*n := by omega
  have h := Nat.mul_le_mul_right (archiveDegreeCalendar n t J0 r) hh
  omega

namespace FixedAmbientBufferedData
@[simp] theorem toAmbient_D {n b c k A B Lh J s : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C] (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    I.toAmbient.D=I.D := by
  have h := I.ambient_eq
  subst n
  rfl
end FixedAmbientBufferedData

namespace ActualNormalizedBufferedStage
 theorem upperFactor_one_le {b c k A B Lh J s depth a : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C] {I : BufferedStageInput b c k A B Lh J s depth T C O}
    {N : Fin k → ℝ} {P U : ℝ} (Z : ActualNormalizedBufferedStage I N P U a) : 1 ≤ Z.upperFactor := by
  unfold upperFactor
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ (by norm_num)
  · exact (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans (le_max_right _ _)
end ActualNormalizedBufferedStage

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {N : Fin k → ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

def finalUpper (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : ℝ := by
  induction H with
  | zero _ _ U => exact U
  | short _ _ U => exact U
  | last _ _ _ Z => exact Z.upperFactor
  | next _ _ _ _ _ _ _ ih => exact ih
theorem finalUpper_one_le (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (hU : 1 ≤ U) : 1 ≤ H.finalUpper := by
  induction H with
  | zero => exact hU
  | short => exact hU
  | last _ _ _ Z => exact Z.upperFactor_one_le
  | next _ _ _ Z _ _ _ ih => exact ih Z.upperFactor_one_le

end ActualBufferedArchive

/-- A single threshold controls actual upper factors through the entire
constructed archive. The degree hierarchy bounds every intermediate J before
scale is varied; both analytic reset and cellular errors are charged per drop. -/
theorem eventually_actual_archive_upper (n k A M t R J0 : ℕ) (hn : 1 ≤ n)
    {epsilon tau : ℝ} (ht : 2 ≤ t) (htau : 0<tau)
    (hR : 2*(k:ℝ)/tau+k ≤ R)
    (hrate : ∀ b c : ℕ, 0<b → b+c=n →
      (M:ℝ)*(calendarRemainder b+Real.log (2*((bufferedStageOrientations b c).card:ℝ))/(b:ℝ))/
        ((b*t:ℕ)-1:ℝ)+tau*Real.log 2<epsilon) :
    ∀ᶠ q : ℕ in atTop, ∀ (B Lh b c J s fuel : ℕ) (T C O : Type)
      [DecidableEq T] [DecidableEq C]
      (N : Fin k → ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O) (P U : ℝ)
      (H : ActualBufferedArchive k A B Lh ⌊tau*(q:ℝ)⌋₊ t T C O N I P U fuel),
      b+c=n → s=b*t → (∀ j ∈ Finset.range s, I.D j=partitionBoxDegree b j) →
      B ≤ M*q → Lh ≤ q → J ≤ J0 → fuel ≤ n → 1 ≤ U →
      H.finalUpper ≤ U*Real.exp (epsilon*q*H.drops) := by
  let Jmax := archiveDegreeCalendar n t J0 n
  have hstages : ∀ᶠ q : ℕ in atTop, ∀ b c : Fin (n+1), ∀ J : Fin (Jmax+1),
      0<b.val → b.val+c.val=n →
      ∀ (B Lh depth : ℕ) (T C O : Type) [DecidableEq T] [DecidableEq C]
        (I : BufferedStageInput b.val c.val k A B Lh J.val (b.val*t) depth T C O)
        (N : Fin k → ℝ) (P U : ℝ) (Z : ActualNormalizedBufferedStage I N P U ⌊tau*(q:ℝ)⌋₊),
        (∀ j ∈ Finset.range (b.val*t), I.D j=partitionBoxDegree b.val j) →
        depth ≤ B/(b.val*t-1)+1 → B ≤ M*q → Lh ≤ q → Z.rounds ≤ R → 1 ≤ U →
        Z.upperFactor ≤ U*Real.exp (epsilon*q) := by
    apply eventually_all.mpr
    intro b
    apply eventually_all.mpr
    intro c
    apply eventually_all.mpr
    intro J
    by_cases hb : 0<b.val
    · by_cases hn' : b.val+c.val=n
      · filter_upwards [eventually_actual_stage_upper b.val c.val k A M J.val t R hb ht htau (hrate _ _ hb hn')] with q hq
        exact fun _ _ => hq
      · exact Filter.Eventually.of_forall (fun _ _ h => (hn' h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (hb h).elim)
  obtain ⟨Q,hQ⟩ := exists_nat_gt (2/tau)
  have hscale : ∀ᶠ q : ℕ in atTop, 0<q ∧ 2 ≤ tau*(q:ℝ) := by
    filter_upwards [eventually_ge_atTop Q,eventually_gt_atTop 0] with q hq hq0
    refine ⟨hq0,?_⟩
    have hqR : (Q:ℝ) ≤ q := by exact_mod_cast hq
    have h := (div_lt_iff₀ htau).mp (hQ.trans_le hqR)
    linarith
  filter_upwards [hstages,hscale] with q hq hscale
  intro B Lh b c J s fuel T C O _ _ N I P U H hdim hs hcalendar hB hLh hJinitial hfuel hU
  have ha := floor_drop_bounds hscale.2
  have stageBound {b c J s : ℕ} (I : AmbientBufferedStageData b c k A B Lh J s T C O)
      (hdim : b+c=n) (hs : s=b*t) (hcalendar : ∀ j ∈ Finset.range s, I.D j=partitionBoxDegree b j)
      (hJ : J ≤ Jmax) {P U : ℝ} (hU : 1 ≤ U)
      (Z : ActualNormalizedBufferedStage I.toInput N P U ⌊tau*(q:ℝ)⌋₊) :
      Z.upperFactor ≤ U*Real.exp (epsilon*q) := by
    have hr := (Z.actual_rounds_bound htau hscale.1 hLh ha.1 ha.2.1).trans hR
    have hrN : Z.rounds ≤ R := by exact_mod_cast hr
    subst s
    exact hq ⟨b,by omega⟩ ⟨c,by omega⟩ ⟨J,by omega⟩ I.dimension_pos hdim
      B Lh _ T C O I.toInput N P U Z hcalendar (le_refl _) hB hLh hrN hU
  have go (r : ℕ) (hr : r+fuel ≤ n) (hJ : J ≤ archiveDegreeCalendar n t J0 r) :
      H.finalUpper ≤ U*Real.exp (epsilon*q*H.drops) := by
    clear hJinitial hfuel
    induction H generalizing r with
    | zero => simp [ActualBufferedArchive.finalUpper,ActualBufferedArchive.drops]
    | short => simp [ActualBufferedArchive.finalUpper,ActualBufferedArchive.drops]
    | last I P U Z =>
      have hj := hJ.trans (archiveDegreeCalendar_mono n t J0 hn (by omega : r ≤ n))
      simpa only [ActualBufferedArchive.finalUpper,ActualBufferedArchive.drops,Nat.cast_one,mul_one] using
        stageBound I hdim hs hcalendar hj hU Z
    | @next bb cc JJ ss ff I P U Z hb ht tail ih =>
      have hj := hJ.trans (archiveDegreeCalendar_mono n t J0 hn (by omega : r ≤ n))
      have hz := stageBound I hdim hs hcalendar hj hU Z
      have hjnext := I.successorDegree_le_calendar n t J0 r hdim hs hcalendar hJ
      have hcalnext : ∀ j ∈ Finset.range ((bb-1)*t), (I.nextData Z hb t ht).D j=partitionBoxDegree (bb-1) j := by
        intro j _
        simp only [AmbientBufferedStageData.nextData,FixedAmbientBufferedData.toAmbient_D,AmbientBufferedStageData.nextFrame]
      have htail := ih (by omega) rfl hcalnext Z.upperFactor_one_le (r+1) (by omega) hjnext
      change tail.finalUpper ≤ U*Real.exp (epsilon*q*(tail.drops+1:ℕ))
      apply htail.trans
      have hm := mul_le_mul_of_nonneg_right hz (Real.exp_pos (epsilon*q*tail.drops)).le
      simp only [mul_assoc,←Real.exp_add] at hm
      simpa only [Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_comm,mul_assoc] using hm
  exact go 0 (by simpa using hfuel) hJinitial

end KakeyaTwoScale
#print axioms KakeyaTwoScale.archiveDegreeCalendar_mono
#print axioms KakeyaTwoScale.FixedAmbientBufferedData.toAmbient_D
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.upperFactor_one_le
#print axioms KakeyaTwoScale.eventually_actual_archive_upper

#print axioms KakeyaTwoScale.ActualBufferedArchive.finalUpper_one_le
