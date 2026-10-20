module
public import KakeyaTwoScale.LogGrowth
public import KakeyaTwoScale.ModelPrime

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

def IntegerModelSequence.heightCount {R V F P} (S : IntegerModelSequence R V F P) (i : ℕ) : ℕ :=
  ((S.G i).image Prod.snd).card

theorem IntegerModelSequence.heightCount_pos {R V F P} (S : IntegerModelSequence R V F P) (i : ℕ) :
    0 < S.heightCount i := Finset.card_pos.mpr ((S.nonempty i).image _)

theorem IntegerModelSequence.heightCount_tendsto {R V F P} (S : IntegerModelSequence R V F P) (hV : 0 < V) :
    Tendsto (fun i => (S.heightCount i:ℝ)) atTop atTop := by
  apply log_rate_pos_atTop (fun i => (S.n i:ℝ)) _ V hV S.length_tendsto _ S.height_rate
  exact Eventually.of_forall (fun i => ⟨by exact_mod_cast S.length_pos i,by exact_mod_cast S.heightCount_pos i⟩)

theorem IntegerModelSequence.eventual_projection_bound {R V F P} (S : IntegerModelSequence R V F P)
    (hP : ∀ r ∈ R, P r < V) :
    ∀ᶠ i in atTop, ∀ r ∈ R, ((S.G i).image (integerProjection r)).card ≤ S.heightCount i := by
  apply (eventually_all_finset R).mpr
  intro r hr
  have h := log_rate_eventually_lt (fun i => (S.n i:ℝ))
    (fun i => (((S.G i).image (integerProjection r)).card:ℝ)) (fun i => (S.heightCount i:ℝ))
    (P r) V (hP r hr) (Eventually.of_forall (fun i =>
      ⟨by exact_mod_cast S.length_pos i,
       by exact_mod_cast Finset.card_pos.mpr ((S.nonempty i).image (integerProjection r)),
       by exact_mod_cast S.heightCount_pos i⟩)) (S.projection_rate r hr) S.height_rate
  filter_upwards [h] with i hi
  exact_mod_cast hi.le

structure ModelPrimeSequence {R V F P} (S : IntegerModelSequence R V F P) where
  p : ℕ → ℕ
  prime : ∀ i, (p i).Prime
  lower : ∀ i, 20*S.heightCount i < p i
  upper : ∀ᶠ i in atTop, p i ≤ 40*S.heightCount i
  denominators : ∀ i, ∀ r ∈ R, (r.den:ZMod (p i)) ≠ 0
  rate : Tendsto (fun i => Real.log (p i:ℝ)/(S.n i:ℝ)) atTop (𝓝 V)

/-- Comparable primes with all denominators invertible are chosen from the
actual height counts. Comparability and the prime logarithmic rate are proved. -/
theorem exists_model_prime_sequence {R V F P} (S : IntegerModelSequence R V F P) (hV : 0 < V) :
    Nonempty (ModelPrimeSequence S) := by
  let D := R.sup Rat.den
  let N := fun i => max (S.heightCount i) D
  have hN (i : ℕ) : 0 < N i := (S.heightCount_pos i).trans_le (le_max_left _ _)
  have hd (i : ℕ) (r : ℚ) (hr : r ∈ R) : r.den ≤ N i :=
    (Finset.le_sup (f := Rat.den) hr).trans (le_max_right _ _)
  choose p hp hlo hhi hden using (fun i => exists_model_prime R (N i) (hN i) (hd i))
  have hlarge : ∀ᶠ i in atTop, D ≤ S.heightCount i := by
    have h := (S.heightCount_tendsto hV).eventually (eventually_ge_atTop (D:ℝ))
    filter_upwards [h] with i hi
    exact_mod_cast hi
  have he : ∀ᶠ i in atTop, N i = S.heightCount i := by
    filter_upwards [hlarge] with i hi
    exact max_eq_left hi
  have hlower (i : ℕ) : 20*S.heightCount i < p i :=
    (Nat.mul_le_mul_left 20 (le_max_left _ _)).trans_lt (hlo i)
  have hupper : ∀ᶠ i in atTop, p i ≤ 40*S.heightCount i := by
    filter_upwards [he] with i hi
    simpa only [hi] using hhi i
  refine ⟨⟨p,hp,hlower,hupper,hden,?_⟩⟩
  apply log_rate_comparable (fun i => (S.n i:ℝ)) (fun i => (S.heightCount i:ℝ))
    (fun i => (p i:ℝ)) V 20 40 S.length_tendsto (by norm_num) (by norm_num) _ _ S.height_rate
  · exact Eventually.of_forall (fun i => ⟨by exact_mod_cast S.length_pos i,
      by exact_mod_cast S.heightCount_pos i,by exact_mod_cast (hp i).pos⟩)
  · filter_upwards [hupper] with i hi
    exact ⟨by exact_mod_cast (hlower i).le,by exact_mod_cast hi⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.IntegerModelSequence.heightCount_pos
#print axioms KakeyaTwoScale.IntegerModelSequence.heightCount_tendsto
#print axioms KakeyaTwoScale.IntegerModelSequence.eventual_projection_bound
#print axioms KakeyaTwoScale.exists_model_prime_sequence
