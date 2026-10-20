module
public import KakeyaTwoScale.ProgressionParameters
public import KakeyaTwoScale.ProgressionAreaMap

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace KakeyaTwoScale
open Classical

/-- Positive-step samples with density at least the given threshold. -/
def densePositiveSamples (N : ℕ) (density : ℝ) (A : Set ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ density*(N:ℝ) ≤
    (((Finset.range N).filter fun j : ℕ => p.1+(j:ℝ)*p.2 ∈ A).card : ℝ)}

/-- A finite Szemerédi progression has both start and step below the sampling size. -/
theorem densePositiveSamples_cover {N ell : ℕ} (hell : 2 ≤ ell) (density : ℝ)
    (hSz : ∀ B : Finset ℕ, B ⊆ Finset.range N → density*(N:ℝ) ≤ B.card →
      ∃ s d : ℕ, 0 < d ∧ ∀ j : ℕ, j < ell → s+j*d ∈ B)
    (A : Set ℝ) {p : ℝ × ℝ} (hp : p ∈ densePositiveSamples N density A) :
    ∃ s d : ℕ, s < N ∧ d < N ∧ 0 < d ∧
      (p.1+(s:ℝ)*p.2,(d:ℝ)*p.2) ∈ progressionParameters ell A := by
  let good := (Finset.range N).filter fun j : ℕ => p.1+(j:ℝ)*p.2 ∈ A
  obtain ⟨s,d,hd,hprog⟩ := hSz good (Finset.filter_subset _ _) hp.2
  have hs := (Finset.mem_filter.mp (hprog 0 (by omega))).1
  have hsd := (Finset.mem_filter.mp (hprog 1 (by omega))).1
  simp only [zero_mul, add_zero, Finset.mem_range] at hs
  simp only [one_mul, Finset.mem_range] at hsd
  refine ⟨s,d,hs,by omega,hd,?_,?_⟩
  · have hdR : (0:ℝ)<d := by exact_mod_cast hd
    exact mul_pos hdR hp.1
  · intro j
    have hj := (Finset.mem_filter.mp (hprog j j.isLt)).2
    convert hj using 1
    push_cast
    ring

/-- The finite union costs at most N² in parameter area. -/
theorem volume_densePositiveSamples_le {N ell : ℕ} (hell : 2 ≤ ell) (density : ℝ)
    (hSz : ∀ B : Finset ℕ, B ⊆ Finset.range N → density*(N:ℝ) ≤ B.card →
      ∃ s d : ℕ, 0 < d ∧ ∀ j : ℕ, j < ell → s+j*d ∈ B)
    {A : Set ℝ} (hA : MeasurableSet A) :
    volume (densePositiveSamples N density A) ≤
      (N:ENNReal)^2 * volume (progressionParameters ell A) := by
  let pieces : (Fin N × Fin N) → Set (ℝ × ℝ) := fun q =>
    if 0 < q.2.val then
      (fun p : ℝ × ℝ => (p.1+(q.1.val:ℝ)*p.2,(q.2.val:ℝ)*p.2)) ⁻¹'
        progressionParameters ell A
    else ∅
  have hsub : densePositiveSamples N density A ⊆ ⋃ q, pieces q := by
    intro p hp
    obtain ⟨s,d,hs,hd,hdp,hm⟩ := densePositiveSamples_cover hell density hSz A hp
    exact Set.mem_iUnion.mpr ⟨(⟨s,hs⟩,⟨d,hd⟩), by simpa [pieces,hdp] using hm⟩
  have hpiece (q : Fin N × Fin N) :
      volume (pieces q) ≤ volume (progressionParameters ell A) := by
    dsimp [pieces]
    split_ifs with h
    · exact volume_preimage_progressionAffine_le _ _ (by exact_mod_cast h)
        (measurableSet_progressionParameters ell hA)
    · simp
  calc
    volume (densePositiveSamples N density A) ≤ volume (⋃ q, pieces q) := measure_mono hsub
    _ ≤ ∑' q, volume (pieces q) := measure_iUnion_le pieces
    _ = ∑ q, volume (pieces q) := tsum_fintype _
    _ ≤ ∑ _q : Fin N × Fin N, volume (progressionParameters ell A) :=
      Finset.sum_le_sum fun q _ => hpiece q
    _ = (N:ENNReal)^2 * volume (progressionParameters ell A) := by
      simp [pow_two, nsmul_eq_mul, Nat.cast_mul]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.densePositiveSamples_cover
#print axioms KakeyaTwoScale.volume_densePositiveSamples_le
