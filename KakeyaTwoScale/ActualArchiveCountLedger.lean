module
public import KakeyaTwoScale.JointArchiveEpsilonBudget

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- One literal physical snapshot together with its incoming cumulative degree
product and actual normalized count factor. -/
structure BufferedCountSnapshot (k : ℕ) (T C O : Type) where
  snapshot : BufferedArchiveSnapshot k T C O
  prefixProduct : ℝ
  upper : ℝ

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {N : Fin k → ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O}
  {P U : ℝ} {fuel : ℕ}

/-- Exact constructor ledger: the root has the supplied P,U; each executed
stage multiplies P by its own degree and replaces U by its upperFactor.
A frozen archive adds no fictitious stage. -/
def countLedger (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    List (BufferedCountSnapshot k T C O) := by
  induction H with
  | zero I P U => exact [⟨.ofState I.W,P,U⟩]
  | short I P U => exact [⟨.ofState I.W,P,U⟩]
  | last I P U Z => exact [⟨.ofState I.W,P,U⟩,⟨.ofState Z.state,P*Z.degree,Z.upperFactor⟩]
  | next I P U Z hb ht tail ih => exact ⟨.ofState I.W,P,U⟩::ih

/-- The degrees of executed transitions, without padding frozen stages. -/
def stageDegrees (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : List ℝ := by
  induction H with
  | zero => exact []
  | short => exact []
  | last _ _ _ Z => exact [Z.degree]
  | next _ _ _ Z _ _ _ ih => exact Z.degree::ih

/-- Exact prefix products, including the incoming root product at index zero. -/
theorem countLedger_prefixProducts (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.countLedger.map BufferedCountSnapshot.prefixProduct = H.stageDegrees.scanl (·*·) P := by
  induction H with
  | zero => simp [countLedger, stageDegrees]
  | short => simp [countLedger, stageDegrees]
  | last => simp [countLedger, stageDegrees]
  | next I P U Z hb ht tail ih =>
    simpa only [countLedger,stageDegrees,List.map_cons,List.scanl_cons] using congrArg (List.cons P) ih

/-- Snapshot identity includes all physical records and tuple ownership. -/
theorem countLedger_snapshots (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.countLedger.map BufferedCountSnapshot.snapshot=H.snapshots := by
  induction H with
  | zero => rfl
  | short => rfl
  | last => rfl
  | next I P U Z hb ht tail ih => simpa only [countLedger,snapshots,List.map_cons] using congrArg (List.cons (.ofState I.W)) ih

theorem snapshot_exists_countLedger (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (X : BufferedArchiveSnapshot k T C O) (hX : X∈H.snapshots) :
    ∃ E∈H.countLedger, E.snapshot=X := by
  rw [← H.countLedger_snapshots] at hX
  exact List.mem_map.mp hX

theorem countLedger_count (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (hcount : ∀ j, (I.W.count j:ℝ) ≤ U*(N j*P)) :
    ∀ E∈H.countLedger, ∀ j,
      (E.snapshot.state.count j:ℝ) ≤ E.upper*(N j*E.prefixProduct) := by
  induction H with
  | zero I P U => simp only [countLedger,List.mem_singleton]; intro E hE; subst E; exact hcount
  | short I P U => simp only [countLedger,List.mem_singleton]; intro E hE; subst E; exact hcount
  | last I P U Z =>
    intro E hE
    change E∈[⟨.ofState I.W,P,U⟩,⟨.ofState Z.state,P*Z.degree,Z.upperFactor⟩] at hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact hcount
    · rcases List.mem_singleton.mp hE with rfl
      exact Z.total_count
  | next I P U Z hb ht tail ih =>
    intro E hE
    change E∈⟨.ofState I.W,P,U⟩::tail.countLedger at hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact hcount
    · apply ih _ E hE
      intro j
      simpa only [AmbientBufferedStageData.nextData_count] using Z.total_count j

theorem countLedger_positive (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (hP : 0<P) (hU : 1≤U) :
    ∀ E∈H.countLedger, 0<E.prefixProduct ∧ 1≤E.upper := by
  induction H with
  | zero I P U => simp only [countLedger,List.mem_singleton]; intro E hE; subst E; exact ⟨hP,hU⟩
  | short I P U => simp only [countLedger,List.mem_singleton]; intro E hE; subst E; exact ⟨hP,hU⟩
  | last I P U Z =>
    intro E hE
    change E∈[⟨.ofState I.W,P,U⟩,⟨.ofState Z.state,P*Z.degree,Z.upperFactor⟩] at hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ⟨hP,hU⟩
    · rcases List.mem_singleton.mp hE with rfl
      exact ⟨mul_pos hP Z.degree_pos,Z.upperFactor_one_le⟩
  | next I P U Z hb ht tail ih =>
    intro E hE
    change E∈⟨.ofState I.W,P,U⟩::tail.countLedger at hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ⟨hP,hU⟩
    · exact ih (mul_pos hP Z.degree_pos) Z.upperFactor_one_le E hE

theorem countLedger_upper_one_le (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (hU : 1≤U) : ∀ E∈H.countLedger, 1≤E.upper := by
  induction H with
  | zero I P U => simp only [countLedger,List.mem_singleton]; intro E hE; subst E; exact hU
  | short I P U => simp only [countLedger,List.mem_singleton]; intro E hE; subst E; exact hU
  | last I P U Z =>
    intro E hE
    change E∈[⟨.ofState I.W,P,U⟩,⟨.ofState Z.state,P*Z.degree,Z.upperFactor⟩] at hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact hU
    · rcases List.mem_singleton.mp hE with rfl
      exact Z.upperFactor_one_le
  | next I P U Z hb ht tail ih =>
    intro E hE
    change E∈⟨.ofState I.W,P,U⟩::tail.countLedger at hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact hU
    · exact ih Z.upperFactor_one_le E hE

end ActualBufferedArchive
/-- One threshold controls every actual prefix upper count factor. This is a
prefix-calendar induction, not an assumed monotonicity of finalUpper. -/
theorem eventually_actual_archive_countLedger_upper (n k A M t R J0 : ℕ) (hn : 1 ≤ n)
    {epsilon tau : ℝ} (ht : 2 ≤ t) (hepsilon : 0≤epsilon) (htau : 0<tau)
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
      ∀ E∈H.countLedger, E.upper ≤ U*Real.exp (epsilon*q*H.drops) := by
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
      ∀ E∈H.countLedger, E.upper ≤ U*Real.exp (epsilon*q*H.drops) := by
    clear hJinitial hfuel
    induction H generalizing r with
    | zero I P U =>
      simp only [ActualBufferedArchive.countLedger,List.mem_singleton]
      intro E hE
      subst E
      simp [ActualBufferedArchive.drops]
    | short I P U =>
      simp only [ActualBufferedArchive.countLedger,List.mem_singleton]
      intro E hE
      subst E
      simp [ActualBufferedArchive.drops]
    | last I P U Z =>
      have hj := hJ.trans (archiveDegreeCalendar_mono n t J0 hn (by omega : r ≤ n))
      intro E hE
      change E∈[⟨.ofState I.W,P,U⟩,⟨.ofState Z.state,P*Z.degree,Z.upperFactor⟩] at hE
      rcases List.mem_cons.mp hE with rfl | hE
      · simpa only [ActualBufferedArchive.drops,Nat.cast_one,mul_one] using
          (le_mul_of_one_le_right (show 0≤U by linarith)
            (Real.one_le_exp (show 0≤epsilon*q by positivity)))
      · rcases List.mem_singleton.mp hE with rfl
        simpa only [ActualBufferedArchive.drops,Nat.cast_one,mul_one] using
          stageBound I hdim hs hcalendar hj hU Z
    | @next bb cc JJ ss ff I P U Z hb ht tail ih =>
      have hj := hJ.trans (archiveDegreeCalendar_mono n t J0 hn (by omega : r ≤ n))
      have hz := stageBound I hdim hs hcalendar hj hU Z
      have hjnext := I.successorDegree_le_calendar n t J0 r hdim hs hcalendar hJ
      have hcalnext : ∀ j ∈ Finset.range ((bb-1)*t), (I.nextData Z hb t ht).D j=partitionBoxDegree (bb-1) j := by
        intro j _
        simp only [AmbientBufferedStageData.nextData,FixedAmbientBufferedData.toAmbient_D,AmbientBufferedStageData.nextFrame]
      have htail := ih (by omega) rfl hcalnext Z.upperFactor_one_le (r+1) (by omega) hjnext
      intro E hE
      change E∈⟨.ofState I.W,P,U⟩::tail.countLedger at hE
      rcases List.mem_cons.mp hE with rfl | hE
      · change U ≤ U*Real.exp (epsilon*q*(tail.drops+1:ℕ))
        exact le_mul_of_one_le_right (by linarith) (Real.one_le_exp (by positivity))
      · apply (htail E hE).trans
        have hm := mul_le_mul_of_nonneg_right hz (Real.exp_pos (epsilon*q*tail.drops)).le
        simp only [mul_assoc,←Real.exp_add] at hm
        simpa only [ActualBufferedArchive.drops,Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_comm,mul_assoc] using hm
  exact go 0 (by simpa using hfuel) hJinitial

/-- Precision and one scale threshold are chosen before the finite data;
the mass budget and every actual prefix upper factor fit one dyadic envelope. -/
theorem exists_actual_countLedger_epsilon_envelope (n k A M J0 : ℕ) (hn : 1 ≤ n)
    {epsilon : ℝ} (he : 0<epsilon) :
    ∃ tau : ℝ, 0<tau ∧ ∃ t : ℕ, 2 ≤ t ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (B Lh b c J s fuel : ℕ) (T C O : Type) [DecidableEq T] [DecidableEq C]
        (N : Fin k → ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O) (P U : ℝ)
        (H : ActualBufferedArchive k A B Lh ⌊tau*(q:ℝ)⌋₊ t T C O N I P U fuel),
        b+c=n → s=b*t → (∀ j ∈ Finset.range s, I.D j=partitionBoxDegree b j) →
        B ≤ M*q → Lh ≤ q → J ≤ J0 → fuel ≤ n → 1 ≤ U →
        H.loss ≤ (2:ℝ)^(epsilon*(q:ℝ)/2) ∧
        ∀ E∈H.countLedger, E.upper ≤ U*(2:ℝ)^(epsilon*(q:ℝ)/2) ∧
          H.loss*E.upper ≤ U*(2:ℝ)^(epsilon*(q:ℝ)) := by
  let e := epsilon*Real.log 2/(2*(n+1))
  have he' : 0<e := by dsimp [e]; exact div_pos (mul_pos he (Real.log_pos (by norm_num))) (by positivity)
  obtain ⟨tau,htau,t,ht,hprecision⟩ := exists_joint_archive_precision n M he'
  obtain ⟨R,hR⟩ := exists_nat_gt (2*(k:ℝ)/tau+k)
  refine ⟨tau,htau,t,ht,?_⟩
  filter_upwards [eventually_actual_archive_mass_loss n k A M t R ht htau hR.le
    (fun b c hb hdim => (hprecision b c hb hdim).1),
    eventually_actual_archive_countLedger_upper n k A M t R J0 hn ht he'.le htau hR.le
    (fun b c hb hdim => (hprecision b c hb hdim).2)] with q hmass hupper
  intro B Lh b c J s fuel T C O _ _ N I P U H hdim hs hcalendar hB hLh hJ hfuel hU
  have hm := hmass B Lh b c J s fuel T C O N I P U H hdim hs hB hLh
  have hu := hupper B Lh b c J s fuel T C O N I P U H hdim hs hcalendar hB hLh hJ hfuel hU
  have hd : (H.drops:ℝ) ≤ n := by exact_mod_cast H.drops_le.trans hfuel
  have hratio : (H.drops:ℝ)/(n+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hexp : Real.exp (e*q*H.drops) ≤ (2:ℝ)^(epsilon*(q:ℝ)/2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ epsilon*Real.log 2*(q:ℝ)/2 by positivity)
    dsimp [e]
    convert hh using 1 <;> field_simp
  have hm' := hm.trans hexp
  refine ⟨hm',?_⟩
  intro E hE
  have hu' := (hu E hE).trans (mul_le_mul_of_nonneg_left hexp (show 0 ≤ U by linarith))
  refine ⟨hu',?_⟩
  have hu0 : 0 ≤ E.upper := (by norm_num : (0:ℝ)≤1).trans (H.countLedger_upper_one_le hU E hE)
  have hh := mul_le_mul hm' hu' hu0 (by positivity)
  have hid : (2:ℝ)^(epsilon*(q:ℝ)/2)*(U*(2:ℝ)^(epsilon*(q:ℝ)/2))=
      U*(2:ℝ)^(epsilon*(q:ℝ)) := by
    calc
      _ = U*((2:ℝ)^(epsilon*(q:ℝ)/2)*(2:ℝ)^(epsilon*(q:ℝ)/2)) := by ring
      _ = U*(2:ℝ)^(epsilon*(q:ℝ)/2+epsilon*(q:ℝ)/2) := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]
      _ = _ := by rw [show epsilon*(q:ℝ)/2+epsilon*(q:ℝ)/2=epsilon*(q:ℝ) by ring]

  exact hid ▸ hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.countLedger_snapshots
#print axioms KakeyaTwoScale.ActualBufferedArchive.countLedger_count
#print axioms KakeyaTwoScale.ActualBufferedArchive.countLedger_positive

#print axioms KakeyaTwoScale.eventually_actual_archive_countLedger_upper

#print axioms KakeyaTwoScale.ActualBufferedArchive.countLedger_prefixProducts
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshot_exists_countLedger
#print axioms KakeyaTwoScale.ActualBufferedArchive.countLedger_upper_one_le
#print axioms KakeyaTwoScale.exists_actual_countLedger_epsilon_envelope
