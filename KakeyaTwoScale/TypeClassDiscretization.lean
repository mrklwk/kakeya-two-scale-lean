module
public import KakeyaTwoScale.TypeClassFibers
public import KakeyaTwoScale.EmpiricalSDEntropy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

def baseTypeFiber {I A B : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] [DecidableEq B] (w : I → A) (f : A → B) : Finset (I → A) :=
  (wordTypeClass w).filter (fun u => f ∘ u = f ∘ w)

theorem baseTypeFiber_nonempty {I A B : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] [DecidableEq B] (w : I → A) (f : A → B) :
    (baseTypeFiber w f).Nonempty := by
  refine ⟨w,Finset.mem_filter.mpr ⟨?_,rfl⟩⟩
  exact (mem_wordTypeClass _ _).mpr ⟨Equiv.refl I,rfl⟩

/-- Conditional entropy appears as the logarithmic size of every exact
uniform projection fiber, rather than as an assumed asymptotic. -/
theorem repeated_type_fiber_entropy_tendsto {I A B : Type*}
    [Fintype I] [Nonempty I] [DecidableEq I] [DecidableEq A] [DecidableEq B]
    (w : I → A) (f : A → B) :
    Tendsto (fun k : ℕ => Real.log ((baseTypeFiber (repeatedWord w k) f).card:ℝ)/
      ((Fintype.card I:ℝ)*k)) atTop (𝓝 (empiricalEntropy w-empiricalEntropy (f ∘ w))) := by
  have ht := (repeated_type_entropy_tendsto w).sub (repeated_type_entropy_tendsto (f ∘ w))
  apply ht.congr
  intro k
  have hprod := wordTypeClass_fiber_product (repeatedWord w k) f
  have hp : (0:ℝ) < (wordTypeClass (f ∘ repeatedWord w k)).card := by
    exact_mod_cast Finset.card_pos.mpr (wordTypeClass_nonempty _)
  have hf : (0:ℝ) < (baseTypeFiber (repeatedWord w k) f).card := by
    exact_mod_cast Finset.card_pos.mpr (baseTypeFiber_nonempty (repeatedWord w k) f)
  have he : ((wordTypeClass (f ∘ repeatedWord w k)).card:ℝ)*
      (baseTypeFiber (repeatedWord w k) f).card = (wordTypeClass (repeatedWord w k)).card := by
    exact_mod_cast hprod
  have hlog := congrArg Real.log he
  rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hf)] at hlog
  have heq : f ∘ repeatedWord w k = repeatedWord (f ∘ w) k := rfl
  rw [heq] at hlog
  rw [← sub_div]
  congr 1
  linarith

/-- Simultaneous empirical discretization on actual type classes. For a
fixed finite projection family, all logarithmic size errors and the exact
uniform-fiber assertion hold at the same arbitrarily large repetition scale. -/
theorem empirical_type_discretization {I A B J : Type*}
    [Fintype I] [Nonempty I] [DecidableEq I] [DecidableEq A] [DecidableEq B]
    (w : I → A) (F : Finset J) (proj : J → A → B) (vertical : A → B)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      |Real.log ((wordTypeClass (repeatedWord w k)).card:ℝ)/((Fintype.card I:ℝ)*k)-empiricalEntropy w| < ε ∧
      (∀ j ∈ F,
        |Real.log ((wordTypeClass (repeatedWord (proj j ∘ w) k)).card:ℝ)/((Fintype.card I:ℝ)*k)-
          empiricalEntropy (proj j ∘ w)| < ε) ∧
      |Real.log ((baseTypeFiber (repeatedWord w k) vertical).card:ℝ)/((Fintype.card I:ℝ)*k)-
        (empiricalEntropy w-empiricalEntropy (vertical ∘ w))| < ε ∧
      ∀ v ∈ wordTypeClass (vertical ∘ repeatedWord w k),
        ((wordTypeClass (repeatedWord w k)).filter (fun u => vertical ∘ u = v)).card =
          (baseTypeFiber (repeatedWord w k) vertical).card := by
  have hf : ∀ j ∈ F, ∀ᶠ k : ℕ in atTop,
      |Real.log ((wordTypeClass (repeatedWord (proj j ∘ w) k)).card:ℝ)/((Fintype.card I:ℝ)*k)-
        empiricalEntropy (proj j ∘ w)| < ε := by
    intro j _
    have h := (repeated_type_entropy_tendsto (proj j ∘ w)).eventually (Metric.ball_mem_nhds _ hε)
    simpa only [Metric.mem_ball,Real.dist_eq,empiricalEntropy] using h
  have hJ := (repeated_type_entropy_tendsto w).eventually (Metric.ball_mem_nhds _ hε)
  have hV := (repeated_type_fiber_entropy_tendsto w vertical).eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hJ,(eventually_all_finset F).mpr hf,hV] with k hk hp hv
  refine ⟨?_,hp,?_,?_⟩
  · simpa only [Metric.mem_ball,Real.dist_eq,empiricalEntropy] using hk
  · simpa only [Metric.mem_ball,Real.dist_eq,empiricalEntropy] using hv
  · intro v hv
    exact (wordTypeClass_fiber_card (repeatedWord w k) vertical hv).symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.baseTypeFiber_nonempty
#print axioms KakeyaTwoScale.repeated_type_fiber_entropy_tendsto
#print axioms KakeyaTwoScale.empirical_type_discretization
