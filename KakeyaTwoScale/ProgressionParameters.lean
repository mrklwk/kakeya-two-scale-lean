module
public import KakeyaTwoScale.SzemerediAdapter
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
namespace KakeyaTwoScale
open Classical

def progressionParameters (ell : ℕ) (A : Set ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ ∀ i : Fin ell, p.1 + (i:ℝ)*p.2 ∈ A}

 theorem measurableSet_progressionParameters (ell : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) : MeasurableSet (progressionParameters ell A) := by
  have he : progressionParameters ell A =
      {p : ℝ × ℝ | 0 < p.2} ∩
        ⋂ i : Fin ell, {p : ℝ × ℝ | p.1+(i:ℝ)*p.2 ∈ A} := by
    ext p
    simp [progressionParameters]
  rw [he]
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (MeasurableSet.iInter fun i : Fin ell =>
      hA.preimage (measurable_fst.add
        ((measurable_const : Measurable (fun _ : ℝ × ℝ => (i:ℝ))).mul measurable_snd)))

/-- Dense finite samples of a measurable set yield a progression with a
positive step at least the sampling step. The sampling threshold is uniform
in the set and both real sampling parameters. -/
theorem dense_sample_progression (ell : ℕ) (density : ℝ) (hd : 0 < density) :
    ∃ N : ℕ, 0 < N ∧ ∀ (A : Set ℝ) (x y : ℝ), 0 < y →
      density*(N:ℝ) ≤ ((Finset.range N).filter fun i : ℕ => x+(i:ℝ)*y ∈ A).card →
      ∃ s h : ℝ, y ≤ h ∧ (s,h) ∈ progressionParameters ell A := by
  classical
  obtain ⟨N,hN,hSz⟩ := finite_szemeredi ell density hd
  refine ⟨N,hN,?_⟩
  intro A x y hy hcount
  let good := (Finset.range N).filter fun i : ℕ => x+(i:ℝ)*y ∈ A
  obtain ⟨s,d,hdpos,hprog⟩ := hSz good (Finset.filter_subset _ _) hcount
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hdpos
  refine ⟨x+(s:ℝ)*y, (d:ℝ)*y, ?_, ?_⟩
  · nlinarith
  · refine ⟨by positivity, ?_⟩
    intro i
    have hi := (Finset.mem_filter.mp (hprog i i.isLt)).2
    convert hi using 1
    push_cast
    ring

/-- For length at least two, positive-step progressions in [0,1]
lie in the unit parameter square. -/
theorem progressionParameters_subset_unit_square {ell : ℕ} (hell : 2 ≤ ell)
    {A : Set ℝ} (hA : A ⊆ Set.Icc 0 1) :
    progressionParameters ell A ⊆ Set.Icc (0,0) (1,1) := by
  rintro ⟨s,h⟩ ⟨hh,hp⟩
  have hs := hA (hp ⟨0,by omega⟩)
  have hsh := hA (hp ⟨1,by omega⟩)
  simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero] at hs hsh
  constructor <;> constructor <;> dsimp <;> linarith [hs.1,hs.2,hsh.1,hsh.2]
end KakeyaTwoScale
#print axioms KakeyaTwoScale.dense_sample_progression
#print axioms KakeyaTwoScale.measurableSet_progressionParameters
#print axioms KakeyaTwoScale.progressionParameters_subset_unit_square
