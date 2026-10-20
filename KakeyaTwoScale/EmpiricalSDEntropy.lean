module
public import KakeyaTwoScale.TypeClassSD
public import Mathlib.Topology.Order.Lattice

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

def empiricalEntropy {I A : Type*} [Fintype I] [DecidableEq A] (w : I → A) : ℝ :=
  finiteEntropy (Finset.univ.image w) (empiricalLaw w)

/-- A genuine counting-to-entropy theorem for every finite empirical law.
Its type classes, projected type classes, asymptotics and constant removal
are all proved; no entropy inequality is supplied as a hypothesis. -/
theorem FiniteSDBound.empirical_entropy {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 0 < β) (hR : R.Nonempty)
    {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I] (w : I → ArithmeticPoint) :
    empiricalEntropy (arithmeticProjection (-1) ∘ w) ≤
      β*R.sup' hR (fun r => empiricalEntropy (arithmeticProjection r ∘ w)) := by
  let q := fun (r : ℚ) (k : ℕ) =>
    Real.log ((wordTypeClass (repeatedWord (arithmeticProjection r ∘ w) k)).card:ℝ)/
      ((Fintype.card I:ℝ)*k)
  let H := fun r => empiricalEntropy (arithmeticProjection r ∘ w)
  have hl : ∀ r : ℚ, Tendsto (q r) atTop (𝓝 (H r)) :=
    fun r => repeated_type_entropy_tendsto (arithmeticProjection r ∘ w)
  have hs := Tendsto.finset_sup'_nhds_apply hR (fun r _ => hl r)
  apply le_of_tendsto_of_tendsto (hl (-1)) (hs.const_mul β)
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
  have hI : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  let d : ℝ := (Fintype.card I:ℝ)*k
  let m := R.sup' hR (fun r => q r k)
  have hd : 0 < d := mul_pos hI hkR
  have hp (r : ℚ) : (0:ℝ) < (wordTypeClass (repeatedWord (arithmeticProjection r ∘ w) k)).card := by
    exact_mod_cast Finset.card_pos.mpr (wordTypeClass_nonempty _)
  have he (r : ℚ) : arithmeticProjection r ∘ repeatedWord w k =
      repeatedWord (arithmeticProjection r ∘ w) k := rfl
  have hb := (hSD.constant_one hβ).type_class_bound (repeatedWord w k) (Real.exp (d*m))
    (Real.exp_pos _).le (by
      intro r hr
      rw [he]
      have hq : q r k ≤ m := Finset.le_sup' (fun r => q r k) hr
      have hh : Real.log ((wordTypeClass (repeatedWord (arithmeticProjection r ∘ w) k)).card:ℝ) ≤ d*m := by
        have h := (div_le_iff₀ hd).mp hq
        nlinarith only [h]
      have hh' := Real.exp_le_exp.mpr hh
      rwa [Real.exp_log (hp r)] at hh')
  rw [he,one_mul] at hb
  have hlog := Real.log_le_log (hp (-1)) hb
  rw [Real.log_rpow (Real.exp_pos _),Real.log_exp] at hlog
  change q (-1) k ≤ β*m
  apply (div_le_iff₀ hd).mpr
  nlinarith only [hlog]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.FiniteSDBound.empirical_entropy
