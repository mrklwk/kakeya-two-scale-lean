module
public import KakeyaTwoScale.ModelSequencePrimes
public import KakeyaTwoScale.StableModelCleared

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

structure StableModelSequence {R V F P} (S : IntegerModelSequence R V F P) (T : ModelPrimeSequence S) where
  H : (i : ℕ) → Finset (ZMod (T.p i) × ZMod (T.p i))
  height_lower : ∀ᶠ i in atTop, (T.p i:ℝ)/100 ≤ ((((H i).image Prod.snd).erase 0).card:ℝ)
  fibers : ∀ᶠ i in atTop, ∀ y ∈ (H i).image Prod.snd,
    S.M i ≤ 2*((H i).filter (fun v => v.2=y)).card ∧ ((H i).filter (fun v => v.2=y)).card ≤ S.M i
  projections : ∀ᶠ i in atTop, ∀ r ∈ R,
    ((H i).image (modularLinearForm (T.p i) (slopeCoefficients r).1 (slopeCoefficients r).2)).card ≤
      ((S.G i).image (integerProjection r)).card * modelingFactor r

/-- Stable cyclic graphs are constructed from the integer sequence. Their
nonzero height counts retain a fixed positive fraction of the prime. -/
theorem exists_stable_model_sequence {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hV : 0 < V) (hP : ∀ r ∈ R, P r < V) :
    Nonempty (StableModelSequence S T) := by
  let good := fun i => ∀ r ∈ R, ((S.G i).image (integerProjection r)).card ≤ S.heightCount i
  have hg : ∀ᶠ i in atTop, good i := S.eventual_projection_bound hP
  have hex (i : ℕ) : ∃ H : Finset (ZMod (T.p i) × ZMod (T.p i)), good i →
      (3/5:ℝ)*S.heightCount i ≤ ((H.image Prod.snd).card:ℝ) ∧
      (∀ y ∈ H.image Prod.snd,
        S.M i ≤ 2*(H.filter (fun v => v.2=y)).card ∧ (H.filter (fun v => v.2=y)).card ≤ S.M i) ∧
      ∀ r ∈ R, (H.image (modularLinearForm (T.p i) (slopeCoefficients r).1 (slopeCoefficients r).2)).card ≤
        ((S.G i).image (integerProjection r)).card * modelingFactor r := by
    let : Fact (T.p i).Prime := ⟨T.prime i⟩
    by_cases hi : good i
    · obtain ⟨H,hH⟩ := exists_stable_model_cleared (T.p i) (S.G i) (S.nonempty i) R hR
        (T.lower i).le hi (T.denominators i) (S.M i) (S.uniform i)
      exact ⟨H,fun _ => hH⟩
    · exact ⟨∅,fun hh => (hi hh).elim⟩
  choose H hH using hex
  have hlarge : ∀ᶠ i in atTop, (5:ℝ) ≤ S.heightCount i :=
    (S.heightCount_tendsto hV).eventually (eventually_ge_atTop 5)
  refine ⟨⟨H,?_,?_,?_⟩⟩
  · filter_upwards [hg,hlarge,T.upper] with i hi hN hp
    have hheight := (hH i hi).1
    have he := Finset.pred_card_le_card_erase (s := (H i).image Prod.snd) (a := 0)
    have hcard : ((H i).image Prod.snd).card ≤ (((H i).image Prod.snd).erase 0).card+1 := by omega
    have hcardR : (((H i).image Prod.snd).card:ℝ) ≤ ((((H i).image Prod.snd).erase 0).card:ℝ)+1 := by exact_mod_cast hcard
    have hpR : (T.p i:ℝ) ≤ 40*(S.heightCount i:ℝ) := by exact_mod_cast hp
    linarith
  · filter_upwards [hg] with i hi
    exact (hH i hi).2.1
  · filter_upwards [hg] with i hi
    exact (hH i hi).2.2

def StableModelSequence.nonzeroHeights {R V F P} {S : IntegerModelSequence R V F P}
    {T : ModelPrimeSequence S} (U : StableModelSequence S T) (i : ℕ) : ℕ :=
  (((U.H i).image Prod.snd).erase 0).card

theorem StableModelSequence.nonzeroHeights_pos {R V F P} {S : IntegerModelSequence R V F P}
    {T : ModelPrimeSequence S} (U : StableModelSequence S T) :
    ∀ᶠ i in atTop, 0 < U.nonzeroHeights i := by
  filter_upwards [U.height_lower] with i hi
  have hp : (0:ℝ) < T.p i := by exact_mod_cast (T.prime i).pos
  have h : (0:ℝ) < U.nonzeroHeights i := (div_pos hp (by norm_num)).trans_le hi
  exact_mod_cast h

theorem StableModelSequence.nonzeroHeights_rate {R V F P} {S : IntegerModelSequence R V F P}
    {T : ModelPrimeSequence S} (U : StableModelSequence S T) :
    Tendsto (fun i => Real.log (U.nonzeroHeights i:ℝ)/(S.n i:ℝ)) atTop (𝓝 V) := by
  apply log_rate_comparable (fun i => (S.n i:ℝ)) (fun i => (T.p i:ℝ))
    (fun i => (U.nonzeroHeights i:ℝ)) V (1/100) 1 S.length_tendsto (by norm_num) (by norm_num) _ _ T.rate
  · filter_upwards [U.nonzeroHeights_pos] with i hi
    exact ⟨by exact_mod_cast S.length_pos i,by exact_mod_cast (T.prime i).pos,by exact_mod_cast hi⟩
  · filter_upwards [U.height_lower] with i hi
    let : Fact (T.p i).Prime := ⟨T.prime i⟩
    have hb : U.nonzeroHeights i ≤ T.p i := by
      simpa only [ZMod.card,nonzeroHeights] using (Finset.card_le_univ (((U.H i).image Prod.snd).erase 0))
    exact ⟨by simpa only [one_div,mul_comm (100:ℝ)⁻¹,← div_eq_mul_inv,nonzeroHeights] using hi,
      by simpa only [one_mul] using (show (U.nonzeroHeights i:ℝ) ≤ T.p i by exact_mod_cast hb)⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_stable_model_sequence
#print axioms KakeyaTwoScale.StableModelSequence.nonzeroHeights_pos
#print axioms KakeyaTwoScale.StableModelSequence.nonzeroHeights_rate
