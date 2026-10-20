module
public import KakeyaTwoScale.DirectionNormalization

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def tubeChartLength (n : ℕ) : ℝ := 1/(4*(n+2:ℝ))

theorem tubeChartLength_pos (n : ℕ) : 0 < tubeChartLength n := by unfold tubeChartLength; positivity

theorem tubeChartLength_le_one (n : ℕ) : tubeChartLength n ≤ 1 := by
  unfold tubeChartLength
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]

/-- A finite, scale-independent bank of height intervals contains one full
interval inside every positively oriented segment in the bounded region. -/
theorem bounded_height_interval (R L : ℝ) (_hR : 0 ≤ R) (hL : 0 < L) :
    ∃ K : ℕ, 0 < K ∧ ∀ a v : ℝ, |a| ≤ R → 2*L ≤ v →
      ∃ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), a ≤ (k:ℝ)*L ∧ (k+1:ℝ)*L ≤ a+v := by
  let K := Nat.ceil (R/L)+2
  have hK : R/L ≤ (K:ℝ) := by
    have hh := Nat.le_ceil (R/L)
    dsimp [K]; push_cast; linarith
  refine ⟨K,by dsimp [K]; omega,?_⟩
  intro a v ha hv
  let k := Int.ceil (a/L)
  have hklo : a/L ≤ (k:ℝ) := Int.le_ceil _
  have hkhi : (k:ℝ) < a/L+1 := Int.ceil_lt_add_one _
  have hak : a/L ≤ (K:ℝ) := (div_le_div_of_nonneg_right (le_abs_self a |>.trans ha) hL.le).trans hK
  have hlow : -(K:ℝ) ≤ (k:ℝ) := by
    have hh : -(R/L) ≤ a/L := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp ha).1]) hL.le
    linarith
  have hhigh : k ≤ (K:ℤ) := Int.ceil_le.mpr (by exact_mod_cast hak)
  refine ⟨k,Finset.mem_Icc.mpr ⟨by exact_mod_cast hlow,hhigh⟩,?_,?_⟩
  · exact (div_le_iff₀ hL).mp hklo
  · have hh := (lt_div_iff₀ hL).mp (show (k:ℝ)-1 < a/L by linarith)
    nlinarith

/-- Actual chart and common-interval selection. The loss M depends only on
ambient dimension and the positional bound, before the family or width. -/
theorem finite_tube_chart_selection (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ M : ℕ, 0 < M ∧ ∀ {J : Type*} (G : Finset J), G.Nonempty →
      ∀ b u : J → EuclideanSpace ℝ (Fin (n+1)),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) →
      ∃ S : Finset J, S ⊆ G ∧ S.Nonempty ∧ G.card ≤ M*S.card ∧
      ∃ i : Fin (n+1), ∃ reverse : Bool, ∃ s : ℝ,
      ∀ j ∈ S,
        0 < (orientedDirection reverse (u j)) i ∧
        (orientedBase reverse (b j) (u j)) i ≤ s ∧
        s+tubeChartLength n ≤ (orientedBase reverse (b j) (u j)) i+
          (orientedDirection reverse (u j)) i := by
  let L := tubeChartLength n
  have hL : 0 < L := tubeChartLength_pos n
  obtain ⟨K,hK,hinterval⟩ := bounded_height_interval (R+1) L (by linarith) hL
  let codes : Finset (Fin (n+1) × Bool × ℤ) :=
    Finset.univ.product (Finset.univ.product (Finset.Icc (-(K:ℤ)) (K:ℤ)))
  have hcodes : codes.Nonempty := by
    refine ⟨(0,false,0),?_⟩
    simp [codes]
  refine ⟨codes.card,hcodes.card_pos,?_⟩
  intro J G hG b u hb hu
  have hchoose : ∀ j ∈ G, ∃ code ∈ codes,
      0 < (orientedDirection code.2.1 (u j)) code.1 ∧
      (orientedBase code.2.1 (b j) (u j)) code.1 ≤ (code.2.2:ℝ)*L ∧
      (code.2.2:ℝ)*L+L ≤ (orientedBase code.2.1 (b j) (u j)) code.1+
        (orientedDirection code.2.1 (u j)) code.1 := by
    intro j hj
    obtain ⟨i,hi⟩ := unit_large_coordinate (u j) (hu j hj)
    let reverse := decide (u j i < 0)
    have hdir : (orientedDirection reverse (u j)) i=|u j i| := by
      by_cases ht : u j i < 0
      · simp [reverse,orientedDirection,ht,abs_of_neg ht]
      · simp [reverse,orientedDirection,ht,abs_of_nonneg (le_of_not_gt ht)]
    have hdp : 0 < (orientedDirection reverse (u j)) i := by rw [hdir]; exact (by positivity : (0:ℝ)<1/(n+2:ℝ)).trans_le hi
    have hlong : 2*L ≤ (orientedDirection reverse (u j)) i := by
      rw [hdir]
      have he : 4*L=1/(n+2:ℝ) := by dsimp [L,tubeChartLength]; field_simp
      linarith
    have hbase : |(orientedBase reverse (b j) (u j)) i| ≤ R+1 := by
      have hh := PiLp.norm_apply_le (orientedBase reverse (b j) (u j)) i
      rw [Real.norm_eq_abs] at hh
      apply hh.trans
      cases reverse <;> simp only [orientedBase,Bool.false_eq_true,↓reduceIte]
      · linarith [hb j hj]
      · have hh := norm_add_le (b j) (u j)
        rw [hu j hj] at hh
        linarith [hb j hj]
    obtain ⟨k,hk,hlo,hhi⟩ := hinterval _ _ hbase hlong
    refine ⟨(i,reverse,k),by simpa [codes] using hk,hdp,hlo,?_⟩
    nlinarith only [hhi]
  let code := fun j => if hj : j ∈ G then (hchoose j hj).choose else (0,false,0)
  have hcode (j) (hj : j ∈ G) : code j ∈ codes ∧
      0 < (orientedDirection (code j).2.1 (u j)) (code j).1 ∧
      (orientedBase (code j).2.1 (b j) (u j)) (code j).1 ≤ ((code j).2.2:ℝ)*L ∧
      ((code j).2.2:ℝ)*L+L ≤ (orientedBase (code j).2.1 (b j) (u j)) (code j).1+
        (orientedDirection (code j).2.1 (u j)) (code j).1 := by
    dsimp [code]; rw [dite_eq_left hj]; exact (hchoose j hj).choose_spec
  obtain ⟨q,hq,hmax⟩ := codes.exists_max_image (fun q => (G.filter (fun j => code j=q)).card) hcodes
  let S := G.filter (fun j => code j=q)
  have hcard : G.card ≤ codes.card*S.card := by
    calc
      _ = ∑ q ∈ codes, (G.filter (fun j => code j=q)).card :=
        Finset.card_eq_sum_card_fiberwise (fun j hj => (hcode j hj).1)
      _ ≤ ∑ _q ∈ codes, S.card := Finset.sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hh
    have hz : S.card=0 := by omega
    rw [hz,mul_zero] at hcard
    have := hG.card_pos
    omega
  refine ⟨S,Finset.filter_subset _ _,hSne,hcard,q.1,q.2.1,(q.2.2:ℝ)*L,?_⟩
  intro j hj
  obtain ⟨hj,hjq⟩ := Finset.mem_filter.mp hj
  have hh := (hcode j hj).2
  rwa [hjq] at hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tubeChartLength_pos
#print axioms KakeyaTwoScale.tubeChartLength_le_one
#print axioms KakeyaTwoScale.bounded_height_interval
#print axioms KakeyaTwoScale.finite_tube_chart_selection
