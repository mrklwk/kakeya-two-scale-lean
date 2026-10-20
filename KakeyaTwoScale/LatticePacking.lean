module
public import KakeyaTwoScale.ParallelVolume
public import KakeyaTwoScale.LocalPacking
public import Mathlib.Combinatorics.Pigeonhole

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- The real point represented by an integer lattice index. -/
def latticePoint {n : ℕ} (r : ℝ) (B : Fin n → ℤ) : Fin n → ℝ :=
  fun j => r*(B j:ℝ)

theorem latticePoint_separated {n : ℕ} {r : ℝ} (hr : 0 < r)
    {B D : Fin n → ℤ} (hBD : B ≠ D) : r ≤ dist (latticePoint r B) (latticePoint r D) := by
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hBD
  have hi : (1:ℤ) ≤ |B j-D j| := by
    rcases lt_or_gt_of_ne hj with h | h
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  have hi' : (1:ℝ) ≤ |(B j:ℝ)-(D j:ℝ)| := by exact_mod_cast hi
  have hh := dist_le_pi_dist (latticePoint r B) (latticePoint r D) j
  rw [Real.dist_eq] at hh
  change |r*(B j:ℝ)-r*(D j:ℝ)| ≤ _ at hh
  rw [← mul_sub,abs_mul,abs_of_pos hr] at hh
  nlinarith

theorem latticePoint_injective {n : ℕ} {r : ℝ} (hr : 0 < r) :
    Function.Injective (latticePoint (n:=n) r) := by
  intro B D he
  by_contra hn
  have hh := latticePoint_separated hr hn
  rw [he,dist_self] at hh
  linarith

/-- Rounding a translated coarse lattice to a sufficiently fine grid
preserves all intercepts, uniformly in the translation. -/
theorem gridIndex_translated_lattice_injective {n : ℕ} {r d : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hdr : 2*d < r) (z : Fin n → ℝ) :
    Function.Injective (fun B : Fin n → ℤ => gridIndex d (latticePoint r B+z)) := by
  intro B D he
  dsimp only at he
  by_contra hn
  have hh := gridCell_dist_le hd.le
    (mem_own_gridCell hd (latticePoint r B+z))
    (show latticePoint r D+z ∈ gridCell d (gridIndex d (latticePoint r B+z)) by
      rw [he]; exact mem_own_gridCell hd _)
  rw [dist_add_right] at hh
  have hsep := latticePoint_separated hr hn
  linarith

/-- A scale-uniform bound on the number of distinct fine-grid points close
to a finite collection of actual coarse occupied cells. No packing premise
is left: lattice separation is proved above. -/
theorem lattice_projection_cell_bound (n : ℕ) (C : ℝ) :
    ∃ B : ℕ, 0 < B ∧ ∀ (r d : ℝ), 0 < r → 0 < d → r ≤ C*d →
      ∀ {J : Type*} (family : Finset J) (x : J → Fin n → ℝ)
        (y : J → Fin n → ℤ) (z : Fin n → ℝ),
      (∀ j ∈ family, dist (latticePoint d (y j)+z) (x j) ≤ d) →
      (family.image y).card ≤ B*(family.image (fun j => gridIndex r (x j))).card := by
  obtain ⟨B,hB⟩ := uniform_local_packing (X:=Fin n → ℝ) (C+1)
  refine ⟨B+1,by omega,?_⟩
  intro r d hr hd hrd J family x y z hclose
  let Y := family.image y
  let cells := family.image (fun j => gridIndex r (x j))
  have hreps : ∀ u ∈ Y, ∃ j ∈ family, y j=u := by
    intro u hu; exact Finset.mem_image.mp hu
  by_cases hne : family.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hne
    let rep := fun u => if hu : u ∈ Y then (hreps u hu).choose else j₀
    have hrep (u) (hu : u ∈ Y) : rep u ∈ family ∧ y (rep u)=u := by
      dsimp [rep]; rw [dite_eq_left hu]; exact (hreps u hu).choose_spec
    let f := fun u => gridIndex r (x (rep u))
    have hf (u) (hu : u ∈ Y) : f u ∈ cells :=
      Finset.mem_image.mpr ⟨rep u,(hrep u hu).1,rfl⟩
    have hcap (k) : (Y.filter (fun u => f u=k)).card ≤ B := by
      apply hB d hd (gridRound r (latticePoint r k)-z)
        (Y.filter (fun u => f u=k)) (latticePoint d)
      · intro u hu
        obtain ⟨hu,huk⟩ := Finset.mem_filter.mp hu
        have hcell : gridRound r (x (rep u))=latticePoint r k := by
          change latticePoint r (f u)=_; rw [huk]
        have hh := dist_gridRound_le hr (x (rep u))
        rw [hcell] at hh
        have hclose' := hclose (rep u) (hrep u hu).1
        rw [(hrep u hu).2] at hclose'
        have he : gridRound r (latticePoint r k)=latticePoint r k := by
          funext j
          simp [gridRound,gridIndex,latticePoint,hr.ne']
        rw [he]
        have hdshift : dist (latticePoint d u) (latticePoint r k-z) =
            dist (latticePoint d u+z) (latticePoint r k) := by
          rw [dist_eq_norm,dist_eq_norm]; congr 1; abel
        rw [hdshift]
        calc
          _ ≤ dist (latticePoint d u+z) (x (rep u))+dist (x (rep u)) (latticePoint r k) := dist_triangle _ _ _
          _ ≤ d+r := add_le_add hclose' hh
          _ ≤ (C+1)*d := by nlinarith
      · intro u _ v _ huv
        exact latticePoint_separated hd huv
    calc
      Y.card = ∑ k ∈ cells, (Y.filter (fun u => f u=k)).card :=
        Finset.card_eq_sum_card_fiberwise hf
      _ ≤ ∑ _k ∈ cells, (B+1) := Finset.sum_le_sum (fun k _ => (hcap k).trans (Nat.le_succ B))
      _ = (B+1)*cells.card := by simp [Nat.mul_comm]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.latticePoint_separated
#print axioms KakeyaTwoScale.latticePoint_injective
#print axioms KakeyaTwoScale.gridIndex_translated_lattice_injective
#print axioms KakeyaTwoScale.lattice_projection_cell_bound
