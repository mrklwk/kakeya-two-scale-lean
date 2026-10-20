module
public import KakeyaTwoScale.NestedTubeVolumeInduction
public import Mathlib.Data.List.Chain

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

def nestedVolumeExponent {r : ℕ} (d : ℕ) (sigma : Fin r→ℕ) : List (Fin r)→ℕ
  | [] => 0
  | [_] => 0
  | i::j::rest => d-sigma i+nestedVolumeExponent d sigma (j::rest)

theorem nestedVolumeExponent_le {r : ℕ} (d : ℕ) (sigma : Fin r→ℕ) (levels : List (Fin r)) :
    nestedVolumeExponent d sigma levels≤d*levels.length := by
  induction levels with
  | nil => simp [nestedVolumeExponent]
  | cons i tail ih =>
    cases tail with
    | nil => simp [nestedVolumeExponent]
    | cons j rest =>
      simp only [nestedVolumeExponent,List.length_cons] at *
      nlinarith [Nat.sub_le d (sigma i)]

/-- The precise one-step scalar cancellation, including the case of a zero
remaining product. No recurrence inequality is assumed. -/
theorem nested_volume_scalar_telescope (d s N : ℕ) (hs : s+1≤d)
    (D L l rho R : ℝ) (hl : 0<l) :
    (D*L/l)^(d-s)*(rho^N*l^(d-(s+1))/R)=
      D^(d-s)*(rho^N*L^(d-s)/(l*R)) := by
  have he : d-s=(d-(s+1))+1 := by omega
  by_cases hR : R=0
  · simp [hR]
  · rw [div_pow,mul_pow,he,pow_succ l]
    field_simp

/-- Exact telescope for consecutive codimensions and the actual dilation
ratios. The remaining fixed D-power is bounded separately before scales. -/
theorem nestedVolumeWeight_telescope {r : ℕ} (d : ℕ) (sigma : Fin r→ℕ)
    (L A : Fin r→ℝ) (rho D : ℝ) (i : Fin r) (rest : List (Fin r))
    (hdata : ∀ j∈i::rest, sigma j≤d ∧ 0<L j)
    (hchain : (i::rest).IsChain (fun j k => sigma k=sigma j+1 ∧ A j=D*L j/L k)) :
    nestedVolumeWeight d sigma L A rho (i::rest)=
      D^(nestedVolumeExponent d sigma (i::rest))*
        (rho^(sigma i+rest.length)*(L i)^(d-sigma i)/(rest.map L).prod) := by
  induction rest generalizing i with
  | nil => simp [nestedVolumeWeight,nestedVolumeExponent]
  | cons j rest ih =>
    obtain ⟨⟨hcodim,hA⟩,hchain'⟩ := List.isChain_cons_cons.mp hchain
    have hj := hdata j (by simp)
    have ht := ih j (fun k hk => hdata k (List.mem_cons_of_mem i hk)) hchain'
    have hs : sigma i+1≤d := by omega
    have hN : sigma j+rest.length=sigma i+(j::rest).length := by simp only [List.length_cons]; omega
    simp only [nestedVolumeWeight,nestedVolumeExponent,List.map_cons,List.prod_cons]
    rw [ht,hA,hN,pow_add]
    have he := nested_volume_scalar_telescope d (sigma i) (sigma i+(j::rest).length)
      hs D (L i) (L j) rho ((rest.map L).prod) hj.2
    rw [← hcodim] at he
    calc
      _ = D^(nestedVolumeExponent d sigma (j::rest))*
          ((D*L i/L j)^(d-sigma i)*(rho^(sigma i+(j::rest).length)*L j^(d-sigma j)/(rest.map L).prod)) := by ring
      _ = _ := by rw [he]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.nestedVolumeExponent_le
#print axioms KakeyaTwoScale.nested_volume_scalar_telescope
#print axioms KakeyaTwoScale.nestedVolumeWeight_telescope
