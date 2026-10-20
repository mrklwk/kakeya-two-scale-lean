module
public import KakeyaTwoScale.FrozenFixedDropSuccessor

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- Construct the full frozen-family normalization, starting from a concrete
balanced exact-length state. No legal-history or successor-existence premise
is supplied. The recursive call is justified by the proved height potential.
This is a single dimension-stage theorem, not an HRZ or multilinear input. -/
theorem exists_frozen_normalization {n k A B d : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (S : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (cubes : Finset C) (center : C → EuclideanSpace ℝ (Fin n))
    {δ p q : ℝ} (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hd : 0 < d) (hv : S.Valid Y₀ cube tube Q δ) (hb : S.Balanced cube cubes p)
    (hne : S.tuples.Nonempty) (hcubes : ∀ y ∈ Y₀, cube y ∈ cubes)
    (hbound : (Y₀.card:ℝ) ≤ (2:ℝ)^B)
    (hQ : ∀ c ∈ cubes, ∀ x ∈ Q c, dist x (center c) ≤ (A:ℝ)*δ)
    (beta : Fin k → ℝ) (hbeta : ∀ j, 0 ≤ beta j)
    (hscale : S.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(S.height j))) :
    ∃ (R : ℕ) (V : FrozenGeometryState n k T C O),
      V.Valid Y₀ cube tube Q δ ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      V.tuples ⊆ S.tuples ∧ V.LowerNormalized cube beta q ∧
      R*d ≤ frozenHeightPotential d S.height ∧ (∀ j, V.height j ≤ S.height j) ∧
      V.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      tupleCubeMass S.tuples cube cubes p /
        (((3^k*(2*(A+n+5)+1)^n*(B+1)^(k+1):ℕ):ℝ)^R) ≤ tupleCubeMass V.tuples cube cubes p ∧
      (∀ j, V.normalizedCount cube q j ≤ (2:ℝ)^R *
        max (S.normalizedCount cube q j) (beta j*(2:ℝ)^(d+1))) ∧
      (∀ y ∈ V.tuples, ∀ j, V.geometry δ j (V.parent y j) ⊆ S.geometry δ j (S.parent y j)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=S.axis j (S.parent y j)) ∧
      (∃ lift : V.Grain → S.Grain, ∀ y ∈ V.tuples, lift (V.grain (cube y))=S.grain (cube y)) := by
  classical
  by_cases hstop : S.LowerNormalized cube beta q
  · refine ⟨0,S,hv,hb,hne,Finset.Subset.refl _,hstop,by simp,fun _ => le_rfl,hscale,?_,?_,fun _ _ _ => Set.Subset.refl _,fun _ _ _ => rfl,⟨id,fun _ _ => rfl⟩⟩
    · simp
    · intro j
      simp only [pow_zero,one_mul]
      exact le_max_left (S.normalizedCount cube q j) (beta j*(2:ℝ)^(d+1))
  · have hfail : ¬∀ j, 0 < S.height j → 2*beta j ≤ S.normalizedCount cube q j := by
      intro h
      exact hstop ((lower_normalized_iff S cube beta q hne).mpr h)
    push Not at hfail
    obtain ⟨i,hi,hdef⟩ := hfail
    obtain ⟨U,hUv,hUb,hUne,hUS,hUH,hdrop,hUr,hUmass,hUcount,hUgeom,hUaxis,⟨liftU,hUlift⟩⟩ :=
      exists_fixed_drop_successor (d:=d) S Y₀ cube tube Q cubes center hδ hp hp1 hq hq1 hv hb hne
        (fun y hy => hcubes y (hv.1 hy))
        ((show (S.tuples.card:ℝ) ≤ Y₀.card by exact_mod_cast Finset.card_le_card hv.1).trans hbound)
        hQ beta i hi hdef
    obtain ⟨R,V,hVv,hVb,hVne,hVU,hVstop,hR,hVH,hVr,hVmass,hVcount,hVgeom,hVaxis,⟨liftV,hVlift⟩⟩ :=
      exists_frozen_normalization U Y₀ cube tube Q cubes center hδ hp hp1 hq hq1 hd hUv hUb hUne
        hcubes hbound hQ beta hbeta hUr.le
    refine ⟨R+1,V,hVv,hVb,hVne,hVU.trans hUS,hVstop,?_,?_,hVr,?_,?_,?_,?_,?_⟩
    · nlinarith
    · intro j
      exact (hVH j).trans (by rw [hUH]; exact fixed_drop_height_mono S.height i j)
    · let L : ℝ := ((3^k*(2*(A+n+5)+1)^n*(B+1)^(k+1):ℕ):ℝ)
      have hL : 0 < L := by dsimp [L]; positivity
      have hh := (div_le_div_of_nonneg_right hUmass (pow_nonneg hL.le R)).trans hVmass
      simpa only [L,div_div,pow_succ,mul_comm] using hh
    · intro j
      have hcap : 0 ≤ beta j*(2:ℝ)^(d+1) := mul_nonneg (hbeta j) (by positivity)
      have hmax : max (U.normalizedCount cube q j) (beta j*(2:ℝ)^(d+1)) ≤
          2*max (S.normalizedCount cube q j) (beta j*(2:ℝ)^(d+1)) := by
        apply max_le
        · rcases hUcount j with h | h
          · nlinarith [le_max_left (S.normalizedCount cube q j) (beta j*(2:ℝ)^(d+1))]
          · nlinarith [le_max_right (S.normalizedCount cube q j) (beta j*(2:ℝ)^(d+1))]
        · nlinarith [le_max_right (S.normalizedCount cube q j) (beta j*(2:ℝ)^(d+1))]
      have hh := mul_le_mul_of_nonneg_left hmax (show (0:ℝ) ≤ 2^R by positivity)
      rw [pow_succ]
      exact (hVcount j).trans (by nlinarith)
    · intro y hy j
      exact (hVgeom y hy j).trans (hUgeom y (hVU hy) j)
    · intro y hy j
      exact (hVaxis y hy j).trans (hUaxis y (hVU hy) j)
    · exact ⟨liftU ∘ liftV,fun y hy => (congrArg liftU (hVlift y hy)).trans (hUlift y (hVU hy))⟩
termination_by frozenHeightPotential d S.height
decreasing_by omega

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_frozen_normalization
