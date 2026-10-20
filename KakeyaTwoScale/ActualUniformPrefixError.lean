module
public import KakeyaTwoScale.UniformPrefixError

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Actual archive precision is chosen before calendar constants. A common
scale threshold then pays every positive-prefix logarithmic error at once. -/
theorem exists_actual_uniform_prefix_error (n k A M J0 : ℕ) (hn : 1 ≤ n)
    {epsilon : ℝ} (he : 0<epsilon) :
    ∃ eta : ℝ, 0<eta ∧ eta≤epsilon ∧ ∃ tau : ℝ, 0<tau ∧ ∃ t : ℕ, 2 ≤ t ∧ ∀ K C0 : ℝ, 0<C0 → ∀ᶠ q : ℕ in atTop,
      ∀ (B Lh b c J s fuel : ℕ) (T C O : Type) [DecidableEq T] [DecidableEq C]
        (N : Fin k → ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O)
        (H : ActualBufferedArchive k A B Lh ⌊tau*(q:ℝ)⌋₊ t T C O N I 1 1 fuel),
        b+c=n → s=b*t → (∀ j ∈ Finset.range s, I.D j=partitionBoxDegree b j) →
        B ≤ M*q → Lh ≤ q → J ≤ J0 → fuel ≤ n →
        H.loss≤(2:ℝ)^(eta*(q:ℝ)/2) ∧
        (∀E∈H.countLedger, E.upper≤(2:ℝ)^(eta*(q:ℝ)/2) ∧
          H.loss*E.upper≤(2:ℝ)^(eta*(q:ℝ))) ∧
        ∀ (r : ℕ) (hr : r≤H.drops),
        Real.log K+(r:ℝ)*Real.log (C0*(H.loss*(H.entryAt r hr).upper))+
          (∑i∈Finset.range r, (i:ℝ)*Real.log (H.upperAt i))≤epsilon*(q:ℝ)*Real.log 2 := by
  obtain ⟨eta,heta,heta_le,hscalar⟩ := uniform_prefix_error_absorption n epsilon he
  obtain ⟨tau,htau,t,ht,henv⟩ := exists_actual_countLedger_epsilon_envelope n k A M J0 hn heta
  refine ⟨eta,heta,heta_le,tau,htau,t,ht,?_⟩
  intro K C0 hC0
  obtain ⟨Q,hQ⟩ := hscalar K C0
  filter_upwards [henv,eventually_ge_atTop Q] with q henv hq
  intro B Lh b c J s fuel T C O _ _ N I H hdim hs hcalendar hB hLh hJ hfuel
  have hh := henv B Lh b c J s fuel T C O N I 1 1 H hdim hs hcalendar hB hLh hJ hfuel (by norm_num)
  have hproducts : ∀E∈H.countLedger, H.loss*E.upper≤(2:ℝ)^(eta*(q:ℝ)) := by
    intro E hE
    simpa only [one_mul] using (hh.2 E hE).2
  refine ⟨hh.1,?_,?_⟩
  · intro E hE
    simpa only [one_mul] using hh.2 E hE
  · intro r hr
    exact H.long_prefix_error_absorbed (by norm_num) (by norm_num) eta epsilon q r hr K C0 hC0
      hproducts (hQ q hq r (hr.trans (H.drops_le.trans hfuel)))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_actual_uniform_prefix_error
