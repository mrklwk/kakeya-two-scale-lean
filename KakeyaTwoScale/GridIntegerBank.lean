module
public import KakeyaTwoScale.GridCubeGeometry

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

def coordinateGridIndex {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Fin d→ℤ := fun j => ⌊(x j-a j-theta j)/h⌋

theorem mem_grid_cube_floor {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ) (hh : 0<h)
    (x : EuclideanSpace ℝ (Fin d)) :
    x∈closedGridFace a theta h (coordinateGridIndex a theta h x) (fun _=>none) := by
  intro j
  have hle := Int.floor_le ((x j-a j-theta j)/h)
  have hlt := Int.lt_floor_add_one ((x j-a j-theta j)/h)
  have he : (x j-a j-theta j)/h*h=x j-a j-theta j := div_mul_cancel₀ _ hh.ne'
  have hl := mul_le_mul_of_nonneg_right hle hh.le
  have hu := mul_lt_mul_of_pos_right hlt hh
  change a j+theta j+(⌊(x j-a j-theta j)/h⌋:ℝ)*h≤x j ∧
    x j≤a j+theta j+(⌊(x j-a j-theta j)/h⌋:ℝ)*h+h
  constructor <;> nlinarith

/-- Every occupied cube has uniformly bounded centered integer labels. The
bound applies to closed cubes as well as the canonical floor choice. -/
theorem occupied_cube_integer_bound {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (theta : Fin d→ℝ) (h : ℝ) (htheta : ∀ j, theta j∈Ioo 0 h)
    (hh : 0<h) (R : ℝ)
    (k : Fin d→ℤ) (x : EuclideanSpace ℝ (Fin d))
    (hx : x∈closedGridFace a.ofLp theta h k (fun _=>none)) (hxR : x∈closedBall a R) :
    ∀ j, -(⌈R/h⌉₊+2 : ℕ)≤(k j:ℝ) ∧ (k j:ℝ)≤(⌈R/h⌉₊+2 : ℕ) := by
  intro j
  have hcoord : |x j-a j|≤R := by
    have hp := PiLp.norm_apply_le (p := (2 : ENNReal)) (x-a) j
    have hd : dist x a≤R := hxR
    simpa only [Real.norm_eq_abs,PiLp.sub_apply,dist_eq_norm] using hp.trans hd
  have hn : R/h≤(⌈R/h⌉₊:ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hn hh.le
  have he : R/h*h=R := div_mul_cancel₀ _ hh.ne'
  have hb : gridLevel a.ofLp theta h k j≤x j ∧ x j≤gridLevel a.ofLp theta h k j+h := hx j
  have ht := htheta j
  have hab := abs_le.mp hcoord
  dsimp [gridLevel] at hb
  push_cast
  constructor <;> rw [← mul_le_mul_iff_left₀ hh] <;> nlinarith [ht.1,ht.2]


def gridIndexBank (d N : ℕ) : Finset (Fin d→ℤ) := by
  classical
  exact Finset.univ.image (fun z : Fin d→(Finset.Icc (-(N:ℤ)) N) => fun j => (z j).val)

theorem mem_gridIndexBank {d N : ℕ} (k : Fin d→ℤ) :
    k∈gridIndexBank d N ↔ ∀ j, -(N:ℤ)≤k j ∧ k j≤N := by
  classical
  constructor
  · intro hk
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hk
    intro j
    exact Finset.mem_Icc.mp (z j).property
  · intro hk
    exact Finset.mem_image.mpr ⟨fun j => ⟨k j,Finset.mem_Icc.mpr (hk j)⟩,Finset.mem_univ _,rfl⟩

def gridLabelBank (N : ℕ) : Finset ℤ := Finset.Icc (-(N:ℤ)) (N+1)

theorem gridLabelBank_nonempty (N : ℕ) : (gridLabelBank N).Nonempty := by
  refine ⟨0,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩ <;> omega

theorem gridLabelBank_card (N : ℕ) : (gridLabelBank N).card=2*N+2 := by
  rw [gridLabelBank,Int.card_Icc]
  omega

theorem gridLabelBank_mem_of_cube {d N : ℕ} (k : Fin d→ℤ) (hk : k∈gridIndexBank d N) :
    ∀ j, k j∈gridLabelBank N ∧ k j+1∈gridLabelBank N := by
  intro j
  have hb := (mem_gridIndexBank k).mp hk j
  constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega

theorem gridLabelBank_card_bound (h R : ℝ) (hh : 0<h) (hR : h≤R) :
    ((gridLabelBank (⌈R/h⌉₊+2)).card:ℝ)≤10*(R/h) := by
  rw [gridLabelBank_card]
  push_cast
  have hd : 1≤R/h := (le_div_iff₀ hh).mpr (by simpa using hR)
  have hc := Nat.ceil_lt_add_one (show 0≤R/h by linarith)
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mem_grid_cube_floor
#print axioms KakeyaTwoScale.occupied_cube_integer_bound

#print axioms KakeyaTwoScale.mem_gridIndexBank
#print axioms KakeyaTwoScale.gridLabelBank_card_bound
