module
public import KakeyaTwoScale.StableModelSequences
public import KakeyaTwoScale.ProgressionLength

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

def IntegerModelSequence.halfFiberSize {R V F P} (S : IntegerModelSequence R V F P) (i : ℕ) : ℕ :=
  (S.M i+1)/2

theorem IntegerModelSequence.halfFiber_bounds {R V F P} (S : IntegerModelSequence R V F P) (i : ℕ) :
    0 < S.halfFiberSize i ∧ (S.M i:ℝ)/2 ≤ S.halfFiberSize i ∧ S.halfFiberSize i ≤ S.M i := by
  have hp := S.fiber_pos i
  have h1 : 0 < S.halfFiberSize i := by dsimp [halfFiberSize]; omega
  have h2 : S.M i ≤ 2*S.halfFiberSize i := by dsimp [halfFiberSize]; omega
  refine ⟨h1,?_,?_⟩
  · have h : (S.M i:ℝ) ≤ 2*(S.halfFiberSize i:ℝ) := by exact_mod_cast h2
    linarith
  · dsimp [halfFiberSize]
    omega

theorem IntegerModelSequence.halfFiber_rate {R V F P} (S : IntegerModelSequence R V F P) :
    Tendsto (fun i => Real.log (S.halfFiberSize i:ℝ)/(S.n i:ℝ)) atTop (𝓝 F) := by
  apply log_rate_comparable (fun i => (S.n i:ℝ)) (fun i => (S.M i:ℝ))
    (fun i => (S.halfFiberSize i:ℝ)) F (1/2) 1 S.length_tendsto (by norm_num) (by norm_num) _ _ S.fiber_rate
  · exact Eventually.of_forall (fun i => ⟨by exact_mod_cast S.length_pos i,
      by exact_mod_cast S.fiber_pos i,by exact_mod_cast (S.halfFiber_bounds i).1⟩)
  · apply Eventually.of_forall
    intro i
    have h := S.halfFiber_bounds i
    exact ⟨by linarith [h.2.1],by simpa only [one_mul] using (show (S.halfFiberSize i:ℝ) ≤ S.M i by exact_mod_cast h.2.2)⟩

theorem IntegerModelSequence.eventual_halfFiber_bounds {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V) :
    ∀ᶠ i in atTop, 3 ≤ T.p i ∧ 2 ≤ S.halfFiberSize i ∧ S.halfFiberSize i ≤ T.p i := by
  have hhalf := log_rate_pos_atTop (fun i => (S.n i:ℝ)) (fun i => (S.halfFiberSize i:ℝ))
    F hF S.length_tendsto (Eventually.of_forall (fun i => ⟨by exact_mod_cast S.length_pos i,
      by exact_mod_cast (S.halfFiber_bounds i).1⟩)) S.halfFiber_rate
  have hlarge := hhalf.eventually (eventually_ge_atTop (2:ℝ))
  obtain ⟨r,hr⟩ := hR
  filter_upwards [hlarge,S.eventual_projection_bound hP] with i hi hp
  obtain ⟨v,hv⟩ := S.nonempty i
  have hy : v.2 ∈ (S.G i).image Prod.snd := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have hM : S.M i ≤ S.heightCount i := by
    rw [← S.uniform i v.2 hy]
    exact (integer_fiber_projection_card_le (S.G i) v.2 r).trans (hp r hr)
  have hlo := T.lower i
  have hN := S.heightCount_pos i
  have hFle := (S.halfFiber_bounds i).2.2
  exact ⟨by omega,by exact_mod_cast hi,by omega⟩

theorem StableModelSequence.halfFiber_density {R V F P} {S : IntegerModelSequence R V F P}
    {T : ModelPrimeSequence S} (U : StableModelSequence S T) :
    ∀ᶠ i in atTop, ∀ y ∈ (U.H i).image Prod.snd,
      S.halfFiberSize i ≤ ((U.H i).filter (fun v => v.2=y)).card := by
  filter_upwards [U.fibers] with i hi
  intro y hy
  have hh := (hi y hy).1
  dsimp [IntegerModelSequence.halfFiberSize]
  omega

end KakeyaTwoScale
#print axioms KakeyaTwoScale.IntegerModelSequence.halfFiber_bounds
#print axioms KakeyaTwoScale.IntegerModelSequence.halfFiber_rate
#print axioms KakeyaTwoScale.IntegerModelSequence.eventual_halfFiber_bounds
#print axioms KakeyaTwoScale.StableModelSequence.halfFiber_density
