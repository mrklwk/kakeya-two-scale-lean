module
public import KakeyaTwoScale.JointArchiveEpsilonBudget
public import KakeyaTwoScale.ActualMultilevelArchiveCheckpoint
public import KakeyaTwoScale.KakeyaPublished

@[expose] public section

open Filter
noncomputable section
namespace KakeyaTwoScale

/-- One epsilon budget, one actual archive, and one scale threshold chosen
before all finite data. Half the dyadic budget pays retained mass and half
pays the terminal upper factor. This is a geometric envelope, not the missing
multiscale or determinant-weighted analytic estimate. -/
theorem exists_actual_archive_epsilon_envelope (n k A M J0 : ℕ) (hn : 1 ≤ n)
    {epsilon : ℝ} (he : 0<epsilon) :
    ∃ tau : ℝ, 0<tau ∧ ∃ t : ℕ, 2 ≤ t ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (B Lh b c J s fuel : ℕ) (T C O : Type) [DecidableEq T] [DecidableEq C]
        (N : Fin k → ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O) (P U : ℝ)
        (H : ActualBufferedArchive k A B Lh ⌊tau*(q:ℝ)⌋₊ t T C O N I P U fuel),
        b+c=n → s=b*t → (∀ j ∈ Finset.range s, I.D j=partitionBoxDegree b j) →
        B ≤ M*q → Lh ≤ q → J ≤ J0 → fuel ≤ n → 1 ≤ U →
        H.loss ≤ (2:ℝ)^(epsilon*(q:ℝ)/2) ∧
        H.finalUpper ≤ U*(2:ℝ)^(epsilon*(q:ℝ)/2) ∧
        H.loss*H.finalUpper ≤ U*(2:ℝ)^(epsilon*(q:ℝ)) := by
  let e := epsilon*Real.log 2/(2*(n+1))
  have he' : 0<e := by dsimp [e]; exact div_pos (mul_pos he (Real.log_pos (by norm_num))) (by positivity)
  obtain ⟨tau,htau,t,ht,hprecision⟩ := exists_joint_archive_precision n M he'
  obtain ⟨R,hR⟩ := exists_nat_gt (2*(k:ℝ)/tau+k)
  refine ⟨tau,htau,t,ht,?_⟩
  filter_upwards [eventually_actual_archive_mass_loss n k A M t R ht htau hR.le
    (fun b c hb hdim => (hprecision b c hb hdim).1),
    eventually_actual_archive_upper n k A M t R J0 hn ht htau hR.le
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
  have hu' := hu.trans (mul_le_mul_of_nonneg_left hexp (show 0 ≤ U by linarith))
  refine ⟨hm',hu',?_⟩
  have hu0 : 0 ≤ H.finalUpper := (by norm_num : (0:ℝ) ≤ 1).trans (H.finalUpper_one_le hU)
  have hh := mul_le_mul hm' hu' hu0 (by positivity)
  have hid : (2:ℝ)^(epsilon*(q:ℝ)/2)*(U*(2:ℝ)^(epsilon*(q:ℝ)/2))=
      U*(2:ℝ)^(epsilon*(q:ℝ)) := by
    calc
      _ = U*((2:ℝ)^(epsilon*(q:ℝ)/2)*(2:ℝ)^(epsilon*(q:ℝ)/2)) := by ring
      _ = U*(2:ℝ)^(epsilon*(q:ℝ)/2+epsilon*(q:ℝ)/2) := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]
      _ = _ := by rw [show epsilon*(q:ℝ)/2+epsilon*(q:ℝ)/2=epsilon*(q:ℝ) by ring]

  exact hid ▸ hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_actual_archive_epsilon_envelope
#print axioms KakeyaTwoScale.kakeya_upperMinkowski_lower_of_published_zahl
