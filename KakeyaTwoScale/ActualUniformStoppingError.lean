module
public import KakeyaTwoScale.ActualUniformPrefixError

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A single precision choice pays long-prefix, short-endpoint, last-degree
and fixed packing errors in the same actual archive, uniformly in finite data. -/
theorem exists_actual_uniform_stopping_error (n k A M J0 : ℕ) (hn : 1 ≤ n)
    {epsilon : ℝ} (he : 0<epsilon) :
    ∃ eta : ℝ, 0<eta ∧ eta≤epsilon/2 ∧ ∃ tau : ℝ, 0<tau ∧ ∃ t : ℕ, 2 ≤ t ∧ ∀ K C0 Cshort Kpack : ℝ, 0<C0 → 0<Cshort → ∀ᶠ q : ℕ in atTop,
      ∀ (B Lh b c J s fuel : ℕ) (T C O : Type) [DecidableEq T] [DecidableEq C]
        (N : Fin k → ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O)
        (H : ActualBufferedArchive k A B Lh ⌊tau*(q:ℝ)⌋₊ t T C O N I 1 1 fuel),
        b+c=n → s=b*t → (∀ j ∈ Finset.range s, I.D j=partitionBoxDegree b j) →
        B ≤ M*q → Lh ≤ q → J ≤ J0 → fuel ≤ n →
        H.loss≤(2:ℝ)^(eta*(q:ℝ)/2) ∧
        (∀E∈H.countLedger, E.upper≤(2:ℝ)^(eta*(q:ℝ)/2) ∧
          H.loss*E.upper≤(2:ℝ)^(eta*(q:ℝ))) ∧
        (∀ (r : ℕ) (hr : r≤H.drops),
        Real.log K+(r:ℝ)*Real.log (C0*(H.loss*(H.entryAt r hr).upper))+
          (∑i∈Finset.range r, (i:ℝ)*Real.log (H.upperAt i))≤epsilon*(q:ℝ)*Real.log 2) ∧
        (∀ (r : ℕ) (hr : r≤H.drops),
          Real.log (Cshort*(H.loss*(H.entryAt r hr).upper))≤epsilon*(q:ℝ)*Real.log 2) ∧
        Real.log (2*H.loss)≤epsilon*(q:ℝ)*Real.log 2 ∧
        Kpack≤epsilon*(q:ℝ)*Real.log 2 := by
  obtain ⟨eta,heta,heta_le,tau,htau,t,ht,henv⟩ :=
    exists_actual_uniform_prefix_error n k A M J0 hn (show 0<epsilon/2 by positivity)
  refine ⟨eta,heta,heta_le,tau,htau,t,ht,?_⟩
  intro K C0 Cshort Kpack hC0 hCs
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  let F := max (Real.log Cshort) (max (Real.log 2) Kpack)
  obtain ⟨Q,hQ⟩ := exists_nat_gt (F/(epsilon*Real.log 2/2))
  filter_upwards [henv K C0 hC0,eventually_ge_atTop Q] with q henv hq
  have hF : F≤epsilon*(q:ℝ)*Real.log 2/2 := by
    have hqR : (Q:ℝ)≤q := by exact_mod_cast hq
    have hh := (div_lt_iff₀ (by positivity : 0<epsilon*Real.log 2/2)).mp (hQ.trans_le hqR)
    linarith
  have hbound : eta*(q:ℝ)*Real.log 2≤epsilon*(q:ℝ)*Real.log 2/2 := by
    have hh := mul_le_mul_of_nonneg_right heta_le (show 0≤(q:ℝ)*Real.log 2 by positivity)
    nlinarith only [hh]
  have hnon : 0≤epsilon*(q:ℝ)*Real.log 2 := by positivity
  intro B Lh b c J s fuel T C O _ _ N I H hdim hs hcalendar hB hLh hJ hfuel
  obtain ⟨hloss,hproducts,hlong⟩ := henv B Lh b c J s fuel T C O N I H hdim hs hcalendar hB hLh hJ hfuel
  refine ⟨hloss,hproducts,?_,?_,?_,?_⟩
  · intro r hr
    have hh := hlong r hr
    nlinarith only [hh,hnon]
  · intro r hr
    have hup := (H.countLedger_positive (by norm_num : (0:ℝ)<1) (by norm_num) _ (H.entryAt_mem r hr)).2
    have hpos : 0<H.loss*(H.entryAt r hr).upper := mul_pos H.loss_pos (by linarith)
    have hh := Real.log_le_log hpos (hproducts _ (H.entryAt_mem r hr)).2
    rw [Real.log_rpow (by norm_num : (0:ℝ)<2)] at hh
    rw [Real.log_mul hCs.ne' hpos.ne']
    have hfixed := (le_max_left (Real.log Cshort) (max (Real.log 2) Kpack)).trans hF
    linarith
  · have hh := Real.log_le_log H.loss_pos hloss
    rw [Real.log_rpow (by norm_num : (0:ℝ)<2)] at hh
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) H.loss_pos.ne']
    have hfixed := ((le_max_left (Real.log 2) Kpack).trans (le_max_right (Real.log Cshort) (max (Real.log 2) Kpack))).trans hF
    have hraw : 0≤eta*(q:ℝ)*Real.log 2 := by positivity
    nlinarith only [hh,hfixed,hbound,hraw]
  · have hfixed := ((le_max_right (Real.log 2) Kpack).trans (le_max_right (Real.log Cshort) (max (Real.log 2) Kpack))).trans hF
    linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_actual_uniform_stopping_error
