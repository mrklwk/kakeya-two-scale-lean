module
public import KakeyaTwoScale.FiniteRootIntervals
public import KakeyaTwoScale.NonlinearTupleSelection

@[expose] public section

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Two parity classes of half-delta-spaced starts, plus one tail interval. -/
def cappedStarts (L δ : ℝ) (color : Fin 3) : Finset ℝ := by
  classical
  exact if color.val=2 then {L-δ} else
    ((Finset.range (⌊2*(L-δ)/δ⌋₊+1)).filter (fun i => i%2=color.val)).image
      (fun i : ℕ => (i:ℝ)*δ/2)

theorem cappedStarts_bounds {L δ : ℝ} (hδ : 0 < δ) (hL : δ ≤ L)
    (color : Fin 3) {a : ℝ} (ha : a ∈ cappedStarts L δ color) : 0 ≤ a ∧ a+δ ≤ L := by
  classical
  by_cases hc : color.val=2
  · simp only [cappedStarts,hc,ite_true,Finset.mem_singleton] at ha
    subst a
    constructor <;> linarith
  · simp only [cappedStarts,hc,ite_false,Finset.mem_image,Finset.mem_filter,Finset.mem_range] at ha
    obtain ⟨i,⟨hi,_⟩,rfl⟩ := ha
    have hf := Nat.floor_le (show 0 ≤ 2*(L-δ)/δ by positivity)
    have hi' : (i:ℝ) ≤ (⌊2*(L-δ)/δ⌋₊:ℝ) := by exact_mod_cast Nat.le_of_lt_succ hi
    have hh := (le_div_iff₀ hδ).mp (hi'.trans hf)
    constructor
    · positivity
    · nlinarith

theorem cappedStarts_cover {L δ t : ℝ} (hδ : 0 < δ) (hL : δ ≤ L)
    (ht : t ∈ Ioo (0:ℝ) L) :
    ∃ color : Fin 3, ∃ a ∈ cappedStarts L δ color, t ∈ Ioo a (a+δ) := by
  classical
  have ht0 := ht.1
  by_cases hfirst : t < δ
  · refine ⟨⟨0,by omega⟩,0,?_,by simpa using And.intro ht.1 hfirst⟩
    simp only [cappedStarts,show ¬(0:ℕ)=2 by omega,ite_false]
    exact Finset.mem_image.mpr ⟨0,by simp,by simp⟩
  by_cases htail : L-δ/2 < t
  · refine ⟨⟨2,by omega⟩,L-δ,by simp [cappedStarts],?_⟩
    constructor <;> linarith [ht.2]
  let m := ⌊2*t/δ⌋₊
  have hm2 : 2 ≤ m := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    nlinarith [(le_div_iff₀ hδ).mpr (show (2:ℝ)*δ ≤ 2*t by linarith)]
  let i := m-1
  have him : i+1=m := by dsimp [i]; omega
  have hf : (m:ℝ) ≤ 2*t/δ := Nat.floor_le (by positivity)
  have hg : 2*t/δ < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have hf' := (le_div_iff₀ hδ).mp hf
  have hg' := (div_lt_iff₀ hδ).mp hg
  have he : (i:ℝ)+1=(m:ℝ) := by exact_mod_cast him
  have hiB : i ≤ ⌊2*(L-δ)/δ⌋₊ := by
    apply (Nat.le_floor_iff (show 0 ≤ 2*(L-δ)/δ by positivity)).mpr
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  refine ⟨⟨i%2,by omega⟩,(i:ℝ)*δ/2,?_,?_⟩
  · simp only [cappedStarts,show ¬i%2=2 by omega,ite_false,Finset.mem_image,Finset.mem_filter,Finset.mem_range]
    exact ⟨i,⟨by omega,rfl⟩,rfl⟩
  · constructor <;> nlinarith

theorem cappedStarts_disjoint {L δ : ℝ} (hδ : 0 < δ) (color : Fin 3) :
    PairwiseDisjoint (↑(cappedStarts L δ color) : Set ℝ) (fun a => Ioo a (a+δ)) := by
  classical
  intro a ha b hb hne
  change a ∈ cappedStarts L δ color at ha
  change b ∈ cappedStarts L δ color at hb
  by_cases hc : color.val=2
  · simp only [cappedStarts,hc,ite_true,Finset.mem_singleton] at ha hb
    exact False.elim (hne (ha.trans hb.symm))
  · simp only [cappedStarts,hc,ite_false,Finset.mem_image,Finset.mem_filter,Finset.mem_range] at ha hb
    obtain ⟨i,⟨_,hi⟩,rfl⟩ := ha
    obtain ⟨j,⟨_,hj⟩,rfl⟩ := hb
    have hij : i ≠ j := by intro h; exact hne (by rw [h])
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hn : i+2 ≤ j := by omega
      have hn' : (i:ℝ)+2 ≤ (j:ℝ) := by exact_mod_cast hn
      nlinarith [hx.2,hy.1]
    · have hn : j+2 ≤ i := by omega
      have hn' : (j:ℝ)+2 ≤ (i:ℝ) := by exact_mod_cast hn
      nlinarith [hy.2,hx.1]

/-- Every chosen color respects the original axial budget, including at the
floor L=delta. The three-color COVER may overlap; a retained color does not. -/
theorem cappedStarts_length_budget {L δ : ℝ} (hδ : 0 < δ) (hL : δ ≤ L) (color : Fin 3) :
    δ*((cappedStarts L δ color).card:ℝ) ≤ L := by
  classical
  have hv := measureReal_biUnion_finset (μ:=volume) (cappedStarts_disjoint (L:=L) hδ color)
    (fun _ _ => measurableSet_Ioo) (fun _ _ => by simp [Real.volume_Ioo])
  have hsub : (⋃ a ∈ cappedStarts L δ color, Ioo a (a+δ)) ⊆ Ioo (0:ℝ) L := by
    intro x hx
    obtain ⟨a,ha,hx⟩ := Set.mem_iUnion₂.mp hx
    have hb := cappedStarts_bounds hδ hL color ha
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hm := measureReal_mono (μ:=volume) hsub (by simp [Real.volume_Ioo])
  rw [hv,Real.volume_real_Ioo_of_le (hδ.le.trans hL),sub_zero] at hm
  have he : ∀ a : ℝ, volume.real (Ioo a (a+δ))=δ := by
    intro a
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  simpa only [he,Finset.sum_const,nsmul_eq_mul,mul_comm] using hm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cappedStarts_bounds
#print axioms KakeyaTwoScale.cappedStarts_cover
#print axioms KakeyaTwoScale.cappedStarts_disjoint
#print axioms KakeyaTwoScale.cappedStarts_length_budget
