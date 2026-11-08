module

public import LowHalfMul3.LambdaOneBase
public import LowHalfMul3.Coset

@[expose] public section

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

open scoped BigOperators

abbrev Row4 := Fin 4 → F₂
abbrev SliceFn := Fin 16 → F₂

def row4 (a x : Row4) : F₂ := a 0 * x 0 + a 1 * x 1 + a 2 * x 2 + a 3 * x 3

def symp4 (a b : Row4) : F₂ := a 0 * b 1 + a 1 * b 0 + a 2 * b 3 + a 3 * b 2

def betaSlice (pts : Finset (Fin 16)) (x y : SliceFn) : F₂ := ∑ n ∈ pts, x n * y n

theorem betaSlice_comm (pts : Finset (Fin 16)) (x y : SliceFn) :
    betaSlice pts x y = betaSlice pts y x := by
  simp [betaSlice, mul_comm]

theorem betaSlice_self (pts : Finset (Fin 16)) (x : SliceFn) :
    betaSlice pts x x = betaSlice pts x (fun _ => 1) := by
  simp [betaSlice, f2_mul_self]

theorem gram_apply {u v : Row4} {G : Fin 4 → Fin 4 → F₂}
    (hind : ∀ a b : F₂, a • u + b • v = 0 → a = 0 ∧ b = 0)
    (hiso : symp4 u v = 0)
    (hdiag : ∀ i, G i i = 0) (hsymm : ∀ i j, G i j = G j i)
    (hu : ∀ j, row4 u (fun i => G i j) = 0)
    (hv : ∀ j, row4 v (fun i => G i j) = 0) :
    G 0 1 = G 2 3 := by
  have hI (a b : F₂) (h0 : a * u 0 + b * v 0 = 0) (h1 : a * u 1 + b * v 1 = 0)
      (h2 : a * u 2 + b * v 2 = 0) (h3 : a * u 3 + b * v 3 = 0) :
      a = 0 ∧ b = 0 := by
    apply hind
    funext i
    fin_cases i <;> assumption
  have hP : u 0 * v 1 + u 1 * v 0 = u 2 * v 3 + u 3 * v 2 := by
    apply f2_eq_of_add_eq_zero
    simpa only [symp4, add_assoc] using hiso
  have hcol (a : Row4) (h : ∀ j, row4 a (fun i => G i j) = 0) :
      (a 1 * G 0 1 + a 2 * G 0 2 + a 3 * G 0 3 = 0) ∧
      (a 0 * G 0 1 + a 2 * G 1 2 + a 3 * G 1 3 = 0) ∧
      (a 0 * G 0 2 + a 1 * G 1 2 + a 3 * G 2 3 = 0) ∧
      (a 0 * G 0 3 + a 1 * G 1 3 + a 2 * G 2 3 = 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [row4, hdiag, hsymm 1 0, hsymm 2 0, hsymm 3 0, mul_zero, zero_add] using h 0
    · simpa only [row4, hdiag, hsymm 2 1, hsymm 3 1, mul_zero, add_zero] using h 1
    · simpa only [row4, hdiag, hsymm 3 2, mul_zero, add_zero] using h 2
    · simpa only [row4, hdiag, mul_zero, add_zero] using h 3
  obtain ⟨u0, u1, u2, u3⟩ := hcol u hu
  obtain ⟨v0, v1, v2, v3⟩ := hcol v hv
  exact (gram_finite _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI u0 u1 u2 u3 v0 v1 v2 v3 hP).1

theorem kernel_symp4 {u v w z : Row4}
    (hind : ∀ a b : F₂, a • u + b • v = 0 → a = 0 ∧ b = 0)
    (hiso : symp4 u v = 0) (huw : row4 u w = 0) (hvw : row4 v w = 0)
    (huz : row4 u z = 0) (hvz : row4 v z = 0) : symp4 w z = 0 := by
  let G (i j : Fin 4) : F₂ := w i * z j + z i * w j
  have hrow (a : Row4) (hw : row4 a w = 0) (hz : row4 a z = 0) (j : Fin 4) :
      row4 a (fun i => G i j) = 0 := by
    calc
      _ = row4 a w * z j + row4 a z * w j := by unfold row4 G; ring
      _ = 0 := by simp [hw, hz]
  have hG := gram_apply (G := G) hind hiso
    (fun i => by simp [G, mul_comm, CharTwo.add_self_eq_zero])
    (fun i j => by unfold G; ring) (hrow u huw huz) (hrow v hvw hvz)
  have hz : G 0 1 + G 2 3 = 0 := by rw [hG, CharTwo.add_self_eq_zero]
  simpa only [G, symp4, add_assoc, mul_comm (z 0), mul_comm (z 2)] using hz

theorem slice_product_parity {pts : Finset (Fin 16)} {u v : Row4}
    {Y : Fin 4 → SliceFn} {r s : SliceFn} {a b : F₂}
    (hind : ∀ α β : F₂, α • u + β • v = 0 → α = 0 ∧ β = 0)
    (hiso : symp4 u v = 0)
    (hu : ∀ n ∈ pts, row4 u (fun i => Y i n) = s n + a)
    (hv : ∀ n ∈ pts, row4 v (fun i => Y i n) = r n + b)
    (hrad : ∀ i, betaSlice pts (Y i) (fun _ => 1) = 0 ∧
      betaSlice pts (Y i) r = 0 ∧ betaSlice pts (Y i) s = 0) :
    betaSlice pts (Y 0) (Y 1) + betaSlice pts (Y 2) (Y 3) = 0 := by
  have hrow (w : Row4) (R : SliceFn) (c : F₂)
      (he : ∀ n ∈ pts, row4 w (fun i => Y i n) = R n + c)
      (hR : ∀ j, betaSlice pts (Y j) R = 0) (j : Fin 4) :
      row4 w (fun i => betaSlice pts (Y i) (Y j)) = 0 := by
    calc
      _ = ∑ n ∈ pts, row4 w (fun i => Y i n) * Y j n := by
        simp only [row4, betaSlice, add_mul, Finset.mul_sum, Finset.sum_add_distrib,
          mul_assoc]
      _ = betaSlice pts R (Y j) + c * betaSlice pts (Y j) (fun _ => 1) := by
        calc
          _ = ∑ n ∈ pts, (R n + c) * Y j n :=
            Finset.sum_congr rfl fun n hn => by rw [he n hn]
          _ = _ := by simp [betaSlice, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by rw [betaSlice_comm pts R (Y j), hR j, (hrad j).1, mul_zero, add_zero]
  have he := gram_apply (G := fun i j => betaSlice pts (Y i) (Y j)) hind hiso
    (fun i => by rw [betaSlice_self, (hrad i).1])
    (fun i j => betaSlice_comm pts (Y i) (Y j))
    (hrow u s a hu (fun j => (hrad j).2.2)) (hrow v r b hv (fun j => (hrad j).2.1))
  rw [he, CharTwo.add_self_eq_zero]

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
