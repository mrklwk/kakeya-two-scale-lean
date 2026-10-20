module
public import KakeyaTwoScale.InnerBallPacking

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Finite volume and actual uniform inner balls produce a finite covering.
Neither boundedness nor measurability of W is assumed. -/
theorem thickness_finite_cover {d : ℕ} (W : Set (EuclideanSpace ℝ (Fin d)))
    (r : ℝ) (hr : 0<r) (hW : volume W≠⊤)
    (hinner : ∀ x∈W, ∃ y, ball y (r/8)⊆W∩ball x r) :
    ∃ F : Finset (EuclideanSpace ℝ (Fin d)),
      (↑F : Set _)⊆W ∧ W⊆⋃ x∈F,ball x (2*r) ∧
      (F.card : ℝ≥0∞)*volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r/8))≤volume W := by
  classical
  let V := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r/8))
  have hVpos : 0<V.toReal := ENNReal.toReal_pos
    (measure_ball_pos volume 0 (by positivity : 0<r/8)).ne' measure_ball_lt_top.ne
  let good := fun F : Finset (EuclideanSpace ℝ (Fin d)) =>
    (↑F : Set _)⊆W ∧ ∀ x∈F, ∀ y∈F, x≠y → 2*r≤dist x y
  have hpack (F) (hF : good F) : (F.card : ℝ≥0∞)*V≤volume W :=
    inner_ball_packing W r hr F (fun x hx => hinner x (hF.1 hx)) hF.2
  let N := ⌈(volume W).toReal/V.toReal⌉₊
  have hbound (F) (hF : good F) : F.card≤N := by
    have hp := ENNReal.toReal_mono hW (hpack F hF)
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hp
    have hc : (F.card : ℝ)≤(volume W).toReal/V.toReal := (le_div_iff₀ hVpos).mpr hp
    exact_mod_cast hc.trans (Nat.le_ceil _)
  let P := fun k : ℕ => ∃ F, good F ∧ F.card=k
  have hzero : P 0 := ⟨∅,by simp [good],by simp⟩
  obtain ⟨F,hF,hcard⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le N) hzero
  have hmax (G) (hG : good G) : G.card≤F.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound G hG) ⟨G,hG,rfl⟩
  refine ⟨F,hF.1,?_,hpack F hF⟩
  intro x hx
  by_contra hnot
  have hdist (y) (hy : y∈F) : 2*r≤dist x y := by
    apply le_of_not_gt
    intro hxy
    exact hnot (mem_iUnion₂.mpr ⟨y,hy,hxy⟩)
  have hxF : x∉F := by
    intro hxF
    have := hdist x hxF
    simp only [dist_self] at this
    linarith
  have hg : good (insert x F) := by
    refine ⟨?_,?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hx
      · exact hF.1 hy
    · intro y hy z hz hne
      rcases Finset.mem_insert.mp hy with rfl|hyF
      · rcases Finset.mem_insert.mp hz with rfl|hzF
        · exact (hne rfl).elim
        · exact hdist z hzF
      · rcases Finset.mem_insert.mp hz with rfl|hzF
        · simpa only [dist_comm] using hdist y hyF
        · exact hF.2 y hyF z hzF hne
  have hh := hmax (insert x F) hg
  rw [Finset.card_insert_of_notMem hxF] at hh
  omega

end KakeyaTwoScale
#print axioms KakeyaTwoScale.thickness_finite_cover
