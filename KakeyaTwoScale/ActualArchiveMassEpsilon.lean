module
public import KakeyaTwoScale.ActualStageEpsilonBound
public import KakeyaTwoScale.ActualBufferedArchiveAccounting

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- Uniform retained-mass loss for the recursively constructed archive.
Only dimension/calendar precision and original cardinality/height bounds are
inputs. Actual normalization rounds are bounded internally. The threshold is
chosen before all finite geometric data and every realized stopping depth. -/
theorem eventually_actual_archive_mass_loss (n k A M t R : ℕ)
    {epsilon tau : ℝ} (ht : 2 ≤ t) (htau : 0<tau)
    (hR : 2*(k:ℝ)/tau+k ≤ R)
    (hrate : ∀ b c : ℕ, 0<b → b+c=n →
      (M:ℝ)*Real.log (2*((bufferedStageOrientations b c).card:ℝ))/((b*t:ℕ)-1:ℝ)<epsilon) :
    ∀ᶠ q : ℕ in atTop, ∀ (B Lh b c J s fuel : ℕ) (T C O : Type)
      [DecidableEq T] [DecidableEq C]
      (N : Fin k → ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O)
      (P U : ℝ)
      (H : ActualBufferedArchive k A B Lh ⌊tau*(q:ℝ)⌋₊ t T C O N I P U fuel),
      b+c=n → s=b*t → B ≤ M*q → Lh ≤ q →
      H.loss ≤ Real.exp (epsilon*q*H.drops) := by
  have hstages : ∀ᶠ q : ℕ in atTop, ∀ b c : Fin (n+1), 0<b.val → b.val+c.val=n →
      ∀ (B Lh J depth a : ℕ) (T C O : Type) [DecidableEq T] [DecidableEq C]
        (I : BufferedStageInput b.val c.val k A B Lh J (b.val*t) depth T C O)
        (N : Fin k → ℝ) (P U : ℝ) (Z : ActualNormalizedBufferedStage I N P U a),
        depth ≤ B/(b.val*t-1)+1 → B ≤ M*q → Lh ≤ q → Z.rounds ≤ R →
        Z.retentionLoss ≤ Real.exp (epsilon*q) := by
    apply eventually_all.mpr
    intro b
    apply eventually_all.mpr
    intro c
    by_cases hb : 0<b.val
    · by_cases hn : b.val+c.val=n
      · have hs : 2 ≤ b.val*t := by nlinarith
        filter_upwards [eventually_actual_stage_retention b.val c.val k A M (b.val*t) R hs (hrate _ _ hb hn)] with q hq
        exact fun _ _ => hq
      · exact Filter.Eventually.of_forall (fun _ _ h => (hn h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (hb h).elim)
  obtain ⟨Q,hQ⟩ := exists_nat_gt (2/tau)
  have hscale : ∀ᶠ q : ℕ in atTop, 0<q ∧ 2 ≤ tau*(q:ℝ) := by
    filter_upwards [eventually_ge_atTop Q,eventually_gt_atTop 0] with q hq hq0
    refine ⟨hq0,?_⟩
    have hqR : (Q:ℝ) ≤ q := by exact_mod_cast hq
    have h := (div_lt_iff₀ htau).mp (hQ.trans_le hqR)
    linarith
  filter_upwards [hstages,hscale] with q hq hscale
  intro B Lh b c J s fuel T C O _ _ N I P U H hn hs hB hLh
  have ha := floor_drop_bounds hscale.2
  have stageBound {b c J s : ℕ} (I : AmbientBufferedStageData b c k A B Lh J s T C O)
      (hn : b+c=n) (hs : s=b*t) {P U : ℝ}
      (Z : ActualNormalizedBufferedStage I.toInput N P U ⌊tau*(q:ℝ)⌋₊) :
      Z.retentionLoss ≤ Real.exp (epsilon*q) := by
    have hr := (Z.actual_rounds_bound htau hscale.1 hLh ha.1 ha.2.1).trans hR
    have hrN : Z.rounds ≤ R := by exact_mod_cast hr
    subst s
    exact hq ⟨b,by omega⟩ ⟨c,by omega⟩ I.dimension_pos hn B Lh J _ _ T C O I.toInput N P U Z (le_refl _) hB hLh hrN
  induction H with
  | zero => simp [ActualBufferedArchive.loss,ActualBufferedArchive.drops]
  | short => simp [ActualBufferedArchive.loss,ActualBufferedArchive.drops]
  | last I P U Z =>
    simpa only [ActualBufferedArchive.loss,ActualBufferedArchive.drops,Nat.cast_one,mul_one] using stageBound I hn hs Z
  | next I P U Z hb ht tail ih =>
    have htail := ih (by omega) rfl
    have hz := stageBound I hn hs Z
    change Z.retentionLoss*tail.loss ≤ Real.exp (epsilon*q*(tail.drops+1:ℕ))
    have hmul := mul_le_mul hz htail tail.loss_pos.le (Real.exp_pos _).le
    rw [←Real.exp_add] at hmul
    simpa only [Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_comm] using hmul

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_actual_archive_mass_loss
