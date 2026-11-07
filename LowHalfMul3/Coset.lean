module

public import LowHalfMul3.LambdaThree

@[expose] public section

/-!
# The general coset lemma (Lemmas B3a and B3b of `lambda3_proof.tex`)

We prove one statement for an arbitrary *coset base* `A ⊆ ANF 6`
(`CosetBase A`):

* `A` is a subspace containing all affine functions;
* the derivatives of every `X ∈ A` along `a₂` and `b₂` are constant;
* the **carry pairing** `β(u, v) = ∑_{y ∈ U} u(y) v(y)` (sum over the 16 points
  with `a₂ = b₂ = 0`; for functions of degree `≤ 2` this is the
  `a₀a₁b₀b₁`-coefficient of `uv`) has `1`, `a₀` and `b₀` in its radical on `A`.

**Theorem (`coset_obstruction`).** If `CosetBase A`, `f, h ∈ A` and `g = fh`,
then no `F, H ∈ A + ⟨g⟩` satisfy `FH ∈ z₂ + A + ⟨g⟩`. Also `z₂ ∉ A + ⟨g⟩`
(`coset_z2_not_mem`).

For `Q ⊆ Λ²(U)` of any dimension, `V(Q)` is a coset base (`cosetBase_V4`); this
gives `B3Claim` (`b3Claim`). The hypotheses are exactly the ones used by the
paper's proofs, so the same theorem serves the inside-`U` branch of `λ = 2`
(base `V(S)`, `S = Q + ⟨Z₁⟩ ⊆ Λ²(U)`) and, through the radical hypotheses, the
core-cubic branch of `λ = 1` (base `Aff + ⟨P₀, Z₁, c⟩`).

Proof structure, all at the level of truth tables:

* **B3a** (`coset_B3a`): from `FH + z₂ + C + σ fh = 0` the derivatives along
  `a₂, b₂` give two linear relations `Σ_k U_{ik} x_k = b₀ + κ₁, a₀ + κ₂` with
  `x = (H, F, h, f)` and the `2 × 4` matrix `U` of external coefficients; the
  second derivative gives `det₀₁ U = det₂₃ U`; summing over `U` gives the carry
  condition `β(F, H) + σ β(f, h) = 1`. Pairing the relations with each `x_l`
  gives `U G = 0` for the Gram matrix `G` of `β`, and the finite lemma
  `gram_finite` (Plücker duality, 2¹⁴ cases) gives `β(H, F) = β(h, f)` and
  `σ = 1`: contradiction.
* **B3b** (`coset_B3b`): `k (F' + fh) + z₂ + v = 0` is excluded by
  differentiating along `a₂, b₂` (a nonzero derivative of `k` reduces to B3a;
  otherwise the external parts of `f, h` are dependent and an affine function
  would vanish on the zero set of another).
* **Proposition B3** (`coset_obstruction`): the four cases of the coefficients
  of `g` in `F, H`.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-! ## The carry pairing on `U` -/

/-- The 16 points of `F₂⁶` with `a₂ = b₂ = 0`. -/
def upt (n : Fin 16) : Fin 6 → F₂ :=
  ![bitF n.val 0, bitF n.val 1, 0, bitF n.val 2, bitF n.val 3, 0]

/-- The carry pairing `β(u, v) = ∑_{y ∈ U} u(y) v(y)`. -/
def cp (u v : (Fin 6 → F₂) → F₂) : F₂ := ∑ n : Fin 16, u (upt n) * v (upt n)

/-- The constant function `1`. -/
def one6 : (Fin 6 → F₂) → F₂ := fun _ => 1

theorem cp_comm (u v : (Fin 6 → F₂) → F₂) : cp u v = cp v u := by
  simp only [cp, mul_comm]

theorem f2_mul_self (a : F₂) : a * a = a := by revert a; decide

theorem cp_self (u : (Fin 6 → F₂) → F₂) : cp u u = cp u one6 := by
  simp only [cp, one6, mul_one, f2_mul_self]

theorem cp_lin4 {a b c d κ : F₂} {u1 u2 u3 u4 r : (Fin 6 → F₂) → F₂}
    (h : ∀ x, a * u1 x + b * u2 x + c * u3 x + d * u4 x = r x + κ) (w : (Fin 6 → F₂) → F₂) :
    a * cp u1 w + b * cp u2 w + c * cp u3 w + d * cp u4 w = cp r w + κ * cp one6 w := by
  simp only [cp, one6, one_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  linear_combination (w (upt n)) * h (upt n)

set_option maxRecDepth 100000 in
theorem carry_mobius_termwise : ∀ t : Finset (Fin 6),
    (∑ n : Fin 16, ∏ i ∈ t, upt n i) = if t = {0, 1, 3, 4} then 1 else 0 := by
  unfold upt bitF
  decide

/-- **Möbius inversion on `U`.** `β(p, 1)` is the carry coefficient of `p`. -/
theorem cp_one_eq_coeff (p : ANF 6) : cp (eval p) one6 = p.coeff carryMonomial := by
  have hiff : ∀ s : Monomial 6, (s.vars = {0, 1, 3, 4}) ↔ (s = carryMonomial) := by
    intro s
    constructor
    · intro h; exact Monomial.ext (h.trans rfl)
    · intro h; rw [h]; rfl
  calc cp (eval p) one6
      = ∑ s ∈ p.coeff.support, p.coeff s * ∑ n : Fin 16, ∏ i ∈ s.vars, upt n i := by
        simp only [cp, one6, mul_one, eval_eq_sum_support]
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = ∑ s ∈ p.coeff.support, if s = carryMonomial then p.coeff s else 0 := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [carry_mobius_termwise, hiff, mul_ite, mul_one, mul_zero]
    _ = p.coeff carryMonomial := by
        rw [Finset.sum_ite_eq']
        split_ifs with hmem
        · rfl
        · exact (Finsupp.notMem_support_iff.mp hmem).symm

theorem cp_one_eq_zero_of_deg3 {p : ANF 6} (hp : DegreeLE 3 p) : cp (eval p) one6 = 0 := by
  rw [cp_one_eq_coeff]
  exact hp _ (by rw [carryMonomial_card]; norm_num)

theorem cp_z2 : cp (eval (lowMul3 2)) one6 = 1 := by
  rw [cp_one_eq_coeff, coeff_lowMul3_two_carry]

/-! ## Coset bases -/

/-- A space on which the coset argument runs. -/
structure CosetBase (A : Submodule F₂ (ANF 6)) : Prop where
  affine_le : affine 6 ≤ A
  derivA : ∀ X ∈ A, ∀ x, deriv dirA2 (eval X) x = deriv dirA2 (eval X) 0
  derivB : ∀ X ∈ A, ∀ x, deriv dirB2 (eval X) x = deriv dirB2 (eval X) 0
  rad1 : ∀ X ∈ A, cp (eval X) one6 = 0
  radA : ∀ X ∈ A, cp (eval X) (fun y => y 0) = 0
  radB : ∀ X ∈ A, cp (eval X) (fun y => y 3) = 0

theorem f2_shift_aux (a b : F₂) : a = b + (a + b) := by revert a b; decide

theorem CosetBase.shiftA {A : Submodule F₂ (ANF 6)} (hA : CosetBase A) {X : ANF 6}
    (hX : X ∈ A) : ∃ c : F₂, ∀ x, eval X (shiftBy dirA2 x) = eval X x + c :=
  ⟨deriv dirA2 (eval X) 0, fun x => by
    rw [← hA.derivA X hX x]; exact f2_shift_aux _ _⟩

theorem CosetBase.shiftB {A : Submodule F₂ (ANF 6)} (hA : CosetBase A) {X : ANF 6}
    (hX : X ∈ A) : ∃ c : F₂, ∀ x, eval X (shiftBy dirB2 x) = eval X x + c :=
  ⟨deriv dirB2 (eval X) 0, fun x => by
    rw [← hA.derivB X hX x]; exact f2_shift_aux _ _⟩

theorem z2_shiftA (x : Fin 6 → F₂) :
    eval (lowMul3 2) (shiftBy dirA2 x) = eval (lowMul3 2) x + x 3 := by
  simp only [eval_lowMul3_two, shiftBy, dirA2]
  simp
  ring

theorem z2_shiftB (x : Fin 6 → F₂) :
    eval (lowMul3 2) (shiftBy dirB2 x) = eval (lowMul3 2) x + x 0 := by
  simp only [eval_lowMul3_two, shiftBy, dirB2]
  simp
  ring

theorem shiftB_three (x : Fin 6 → F₂) : shiftBy dirB2 x 3 = x 3 := by
  simp [shiftBy, dirB2]

theorem shiftA_zero (x : Fin 6 → F₂) : shiftBy dirA2 x 0 = x 0 := by
  simp [shiftBy, dirA2]

/-! ## Finite facts -/

set_option maxRecDepth 100000 in
theorem fin_E1 : ∀ F H f h C z b aF aH af ah aC s : F₂,
    F * H + z + C + s * (f * h) = 0 →
    (F + aF) * (H + aH) + (z + b) + (C + aC) + s * ((f + af) * (h + ah)) = 0 →
    aF * H + aH * F + s * af * h + s * ah * f = b + (aF * aH + aC + s * (af * ah)) := by
  decide

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **Plücker duality, finite form.** `U = (u; v)` of rank two with
`det₀₁ = det₂₃`, `G` alternating with `U G = 0`: then `G₀₁ = G₂₃`, and the last
two columns of `U` are not both zero. -/
theorem gram_finite : ∀ u0 u1 u2 u3 v0 v1 v2 v3 g01 g02 g03 g12 g13 g23 : F₂,
    (∀ t1 t2 : F₂, t1 * u0 + t2 * v0 = 0 → t1 * u1 + t2 * v1 = 0 → t1 * u2 + t2 * v2 = 0 →
      t1 * u3 + t2 * v3 = 0 → t1 = 0 ∧ t2 = 0) →
    u1 * g01 + u2 * g02 + u3 * g03 = 0 → u0 * g01 + u2 * g12 + u3 * g13 = 0 →
    u0 * g02 + u1 * g12 + u3 * g23 = 0 → u0 * g03 + u1 * g13 + u2 * g23 = 0 →
    v1 * g01 + v2 * g02 + v3 * g03 = 0 → v0 * g01 + v2 * g12 + v3 * g13 = 0 →
    v0 * g02 + v1 * g12 + v3 * g23 = 0 → v0 * g03 + v1 * g13 + v2 * g23 = 0 →
    u0 * v1 + u1 * v0 = u2 * v3 + u3 * v2 →
    g01 = g23 ∧ ¬ (u2 = 0 ∧ v2 = 0 ∧ u3 = 0 ∧ v3 = 0) := by
  decide

theorem fin_rank : ∀ t1 t2 k1 k2 : F₂, t1 * (0 + k1) + t2 * (0 + k2) = 0 →
    t1 * (1 + k1) + t2 * (0 + k2) = 0 → t1 * (0 + k1) + t2 * (1 + k2) = 0 →
    t1 = 0 ∧ t2 = 0 := by
  decide

theorem fin_omega : ∀ g : F₂, g + 1 + 0 + 1 * g = 0 → False := by decide

theorem two_f2 : (2 : F₂) = 0 := rfl

/-! ## Lemma B3a -/

/-- **Lemma B3a (general form).** On a coset base there are no `F, H, f, h, C`
and `σ` with `F H + z₂ + C + σ f h = 0`. -/
theorem coset_B3a {A : Submodule F₂ (ANF 6)} (hA : CosetBase A) {F H f h C : ANF 6}
    (hF : F ∈ A) (hH : H ∈ A) (hf : f ∈ A) (hh : h ∈ A) (hC : C ∈ A) (σ : F₂)
    (hG : ∀ x, eval F x * eval H x + eval (lowMul3 2) x + eval C x +
      σ * (eval f x * eval h x) = 0) : False := by
  obtain ⟨aF, sAF⟩ := hA.shiftA hF
  obtain ⟨aH, sAH⟩ := hA.shiftA hH
  obtain ⟨af, sAf⟩ := hA.shiftA hf
  obtain ⟨ah, sAh⟩ := hA.shiftA hh
  obtain ⟨aC, sAC⟩ := hA.shiftA hC
  obtain ⟨bF, sBF⟩ := hA.shiftB hF
  obtain ⟨bH, sBH⟩ := hA.shiftB hH
  obtain ⟨bf, sBf⟩ := hA.shiftB hf
  obtain ⟨bh, sBh⟩ := hA.shiftB hh
  obtain ⟨bC, sBC⟩ := hA.shiftB hC
  -- The two first-derivative relations.
  have E1 : ∀ x, aF * eval H x + aH * eval F x + σ * af * eval h x + σ * ah * eval f x =
      x 3 + (aF * aH + aC + σ * (af * ah)) := by
    intro x
    have h1 := hG (shiftBy dirA2 x)
    rw [sAF, sAH, sAf, sAh, sAC, z2_shiftA] at h1
    exact fin_E1 _ _ _ _ _ _ _ _ _ _ _ _ _ (hG x) h1
  have E2 : ∀ x, bF * eval H x + bH * eval F x + σ * bf * eval h x + σ * bh * eval f x =
      x 0 + (bF * bH + bC + σ * (bf * bh)) := by
    intro x
    have h1 := hG (shiftBy dirB2 x)
    rw [sBF, sBH, sBf, sBh, sBC, z2_shiftB] at h1
    exact fin_E1 _ _ _ _ _ _ _ _ _ _ _ _ _ (hG x) h1
  -- The second derivative: `det₀₁ U = det₂₃ U`.
  have E12 : aF * bH + aH * bF = σ * af * (σ * bh) + σ * ah * (σ * bf) := by
    have e0 := E1 0
    have e1 := E1 (shiftBy dirB2 0)
    rw [sBF, sBH, sBf, sBh, shiftB_three] at e1
    have hs : σ * σ = σ := f2_mul_self σ
    linear_combination e1 - e0 - (af * bh + ah * bf) * hs - σ * (af * bh + ah * bf) * two_f2
  -- Rank two.
  have hrank : ∀ t1 t2 : F₂, t1 * aF + t2 * bF = 0 → t1 * aH + t2 * bH = 0 →
      t1 * (σ * af) + t2 * (σ * bf) = 0 → t1 * (σ * ah) + t2 * (σ * bh) = 0 →
      t1 = 0 ∧ t2 = 0 := by
    intro t1 t2 k0 k1 k2 k3
    have key : ∀ x : Fin 6 → F₂, t1 * (x 3 + (aF * aH + aC + σ * (af * ah))) +
        t2 * (x 0 + (bF * bH + bC + σ * (bf * bh))) = 0 := fun x => by
      linear_combination (-t1) * E1 x + (-t2) * E2 x + eval H x * k0 + eval F x * k1 +
        eval h x * k2 + eval f x * k3
    exact fin_rank t1 t2 _ _ (key 0) (key ![0, 0, 0, 1, 0, 0]) (key ![1, 0, 0, 0, 0, 0])
  -- The Gram relations `U G = 0`.
  have z1 : ∀ w ∈ A, cp one6 (eval w) = 0 := fun w hw => by rw [cp_comm]; exact hA.rad1 w hw
  have z3 : ∀ w ∈ A, cp (fun y => y 3) (eval w) = 0 := fun w hw => by
    rw [cp_comm]; exact hA.radB w hw
  have z0 : ∀ w ∈ A, cp (fun y => y 0) (eval w) = 0 := fun w hw => by
    rw [cp_comm]; exact hA.radA w hw
  have dg : ∀ w ∈ A, cp (eval w) (eval w) = 0 := fun w hw => by
    rw [cp_self]; exact hA.rad1 w hw
  have r1 : ∀ w ∈ A, aF * cp (eval H) (eval w) + aH * cp (eval F) (eval w) +
      σ * af * cp (eval h) (eval w) + σ * ah * cp (eval f) (eval w) = 0 := fun w hw => by
    rw [cp_lin4 E1 (eval w), z3 w hw, z1 w hw, mul_zero, add_zero]
  have r2 : ∀ w ∈ A, bF * cp (eval H) (eval w) + bH * cp (eval F) (eval w) +
      σ * bf * cp (eval h) (eval w) + σ * bh * cp (eval f) (eval w) = 0 := fun w hw => by
    rw [cp_lin4 E2 (eval w), z0 w hw, z1 w hw, mul_zero, add_zero]
  have u0 := r1 H hH
  have u1 := r1 F hF
  have u2 := r1 h hh
  have u3 := r1 f hf
  have v0 := r2 H hH
  have v1 := r2 F hF
  have v2 := r2 h hh
  have v3 := r2 f hf
  rw [dg H hH, cp_comm (eval F) (eval H), cp_comm (eval h) (eval H),
    cp_comm (eval f) (eval H)] at u0 v0
  rw [dg F hF, cp_comm (eval h) (eval F), cp_comm (eval f) (eval F)] at u1 v1
  rw [dg h hh, cp_comm (eval f) (eval h)] at u2 v2
  rw [dg f hf] at u3 v3
  simp only [mul_zero, add_zero, zero_add] at u0 u1 u2 u3 v0 v1 v2 v3
  obtain ⟨hg, hcol⟩ := gram_finite aF aH (σ * af) (σ * ah) bF bH (σ * bf) (σ * bh)
    _ _ _ _ _ _ hrank u0 u1 u2 u3 v0 v1 v2 v3 E12
  -- The carry coefficient.
  have E0 : cp (eval F) (eval H) + cp (eval (lowMul3 2)) one6 + cp (eval C) one6 +
      σ * cp (eval f) (eval h) = 0 := by
    have hsum : cp (eval F) (eval H) + cp (eval (lowMul3 2)) one6 + cp (eval C) one6 +
        σ * cp (eval f) (eval h) = ∑ n : Fin 16, (eval F (upt n) * eval H (upt n) +
          eval (lowMul3 2) (upt n) + eval C (upt n) +
          σ * (eval f (upt n) * eval h (upt n))) := by
      simp only [cp, one6, mul_one, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hsum]
    exact Finset.sum_eq_zero fun n _ => hG (upt n)
  rw [cp_z2, hA.rad1 C hC, cp_comm (eval F), cp_comm (eval f), hg] at E0
  rcases f2_eq_zero_or_one σ with rfl | rfl
  · exact hcol ⟨zero_mul _, zero_mul _, zero_mul _, zero_mul _⟩
  · exact fin_omega _ E0

/-! ## Lemma B3b -/

set_option maxRecDepth 100000 in
theorem fin_mu1 : ∀ k F f h z v a af ah av b : F₂,
    k * (F + f * h) + z + v = 0 →
    (k + 1) * ((F + a) + (f + af) * (h + ah)) + (z + b) + (v + av) = 0 →
    k * (b + av * 1) + z + v + 0 * (f * h) = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem fin_mu0 : ∀ k F f h z v a af ah av b : F₂,
    k * (F + f * h) + z + v = 0 →
    (k + 0) * ((F + a) + (f + af) * (h + ah)) + (z + b) + (v + av) = 0 →
    k * (a + (af * h + ah * f + af * ah)) = b + av := by
  decide

set_option maxRecDepth 100000 in
theorem fin_D : ∀ k a af ah h f bf bh b av : F₂,
    k * (a + (af * h + ah * f + af * ah)) = b + av →
    (k + 0) * (a + (af * (h + bh) + ah * (f + bf) + af * ah)) = b + av → k = 1 →
    af * bh + ah * bf = 0 := by
  decide

theorem fin_Dcases : ∀ af ah bf bh : F₂, af * bh + ah * bf = 0 →
    (af = 0 ∧ ah = 0) ∨ (bf = 0 ∧ bh = 0) ∨ (bf = af ∧ bh = ah) := by
  decide

theorem fin_zv : ∀ F f h z v : F₂, 0 * (F + f * h) + z + v = 0 → z = v := by decide

theorem fin_cancel : ∀ a b c : F₂, a + b = a + c → c = b := by decide

theorem fin_onept : ∀ a c d k0 k1 kp yp : F₂, k0 * a = 0 + c → k1 * a = 1 + c →
    kp * a = c + c → kp * yp = (d + 1) + d → False := by
  decide

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem fin_case3 : ∀ aA aB cA cB k0 l0 k3 l3 kp lp : F₂,
    k0 * (aA + l0) = 0 + cA → k0 * (aB + l0) = 0 + cB →
    k3 * (aA + l3) = 1 + cA → k3 * (aB + l3) = 0 + cB →
    kp * (aA + lp) = (cA + 1) + cA → kp * (aB + lp) = (cB + 1) + cB → False := by
  decide

/-- **Lemma B3b (general form).** On a coset base there are no `k, F', f, h, v`
with `k (F' + f h) + z₂ + v = 0`. -/
theorem coset_B3b {A : Submodule F₂ (ANF 6)} (hA : CosetBase A) {k F' f h v : ANF 6}
    (hk : k ∈ A) (hF' : F' ∈ A) (hf : f ∈ A) (hh : h ∈ A) (hv : v ∈ A)
    (hE : ∀ x, eval k x * (eval F' x + eval f x * eval h x) + eval (lowMul3 2) x +
      eval v x = 0) : False := by
  obtain ⟨μA, sAk⟩ := hA.shiftA hk
  obtain ⟨aA, sAF⟩ := hA.shiftA hF'
  obtain ⟨afA, sAf⟩ := hA.shiftA hf
  obtain ⟨ahA, sAh⟩ := hA.shiftA hh
  obtain ⟨avA, sAv⟩ := hA.shiftA hv
  obtain ⟨μB, sBk⟩ := hA.shiftB hk
  obtain ⟨aB, sBF⟩ := hA.shiftB hF'
  obtain ⟨afB, sBf⟩ := hA.shiftB hf
  obtain ⟨ahB, sBh⟩ := hA.shiftB hh
  obtain ⟨avB, sBv⟩ := hA.shiftB hv
  have shA : ∀ x, (eval k x + μA) * ((eval F' x + aA) + (eval f x + afA) * (eval h x + ahA)) +
      (eval (lowMul3 2) x + x 3) + (eval v x + avA) = 0 := fun x => by
    have h1 := hE (shiftBy dirA2 x)
    rwa [sAk, sAF, sAf, sAh, sAv, z2_shiftA] at h1
  have shB : ∀ x, (eval k x + μB) * ((eval F' x + aB) + (eval f x + afB) * (eval h x + ahB)) +
      (eval (lowMul3 2) x + x 0) + (eval v x + avB) = 0 := fun x => by
    have h1 := hE (shiftBy dirB2 x)
    rwa [sBk, sBF, sBf, sBh, sBv, z2_shiftB] at h1
  have memA : ∀ i : Fin 6, ∀ c : F₂, X i + c • (1 : ANF 6) ∈ A := fun i c =>
    hA.affine_le (Submodule.add_mem _ (X_mem_affine i)
      (Submodule.smul_mem _ _ (one_mem_affine 6)))
  rcases f2_eq_zero_or_one μA with hμA | hμA
  swap
  · -- `D_{a₂} k = 1`: `k F = k (b₀ + c)`, a product of two base functions.
    refine coset_B3a hA hk (memA 3 avA) hf hh hv 0 fun x => ?_
    rw [eval_add', eval_smul', eval_one', eval_X]
    have h1 := shA x
    rw [hμA] at h1
    exact fin_mu1 _ _ _ _ _ _ _ _ _ _ _ (hE x) h1
  rcases f2_eq_zero_or_one μB with hμB | hμB
  swap
  · refine coset_B3a hA hk (memA 0 avB) hf hh hv 0 fun x => ?_
    rw [eval_add', eval_smul', eval_one', eval_X]
    have h1 := shB x
    rw [hμB] at h1
    exact fin_mu1 _ _ _ _ _ _ _ _ _ _ _ (hE x) h1
  -- Both derivatives of `k` vanish.
  have EqA : ∀ x, eval k x * (aA + (afA * eval h x + ahA * eval f x + afA * ahA)) =
      x 3 + avA := fun x => by
    have h1 := shA x
    rw [hμA] at h1
    exact fin_mu0 _ _ _ _ _ _ _ _ _ _ _ (hE x) h1
  have EqB : ∀ x, eval k x * (aB + (afB * eval h x + ahB * eval f x + afB * ahB)) =
      x 0 + avB := fun x => by
    have h1 := shB x
    rw [hμB] at h1
    exact fin_mu0 _ _ _ _ _ _ _ _ _ _ _ (hE x) h1
  -- `k ≠ 0`, otherwise `z₂ ∈ A`.
  have hk1 : ∃ x, eval k x = 1 := by
    by_contra hne
    simp only [not_exists] at hne
    have hk0 : ∀ x, eval k x = 0 := fun x => (f2_eq_zero_or_one _).resolve_right (hne x)
    have hzv : ∀ x, eval (lowMul3 2) x = eval v x := fun x => by
      have := hE x
      rw [hk0] at this
      exact fin_zv _ _ _ _ _ this
    have hx3 : ∀ x : Fin 6 → F₂, x 3 = avA := fun x => by
      have h1 := z2_shiftA x
      rw [hzv, hzv, sAv] at h1
      exact fin_cancel _ _ _ h1
    have e0 : (0 : F₂) = avA := hx3 0
    have e1 : (1 : F₂) = avA := hx3 ![0, 0, 0, 1, 0, 0]
    exact absurd (e0.trans e1.symm) (by decide)
  -- The external parts of `f, h` are dependent.
  obtain ⟨x0, hx0⟩ := hk1
  have hD : afA * ahB + ahA * afB = 0 := by
    have e2 := EqA (shiftBy dirB2 x0)
    rw [sBk, sBf, sBh, shiftB_three, hμB] at e2
    exact fin_D _ _ _ _ _ _ _ _ _ _ (EqA x0) e2 hx0
  rcases fin_Dcases _ _ _ _ hD with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `a₂` kills `f, h`: `k = b₀ + c` on the nose.
    rw [h1, h2] at EqA
    simp only [zero_mul, mul_zero, add_zero] at EqA
    exact fin_onept aA avA avB _ _ _ _ (EqA 0) (EqA ![0, 0, 0, 1, 0, 0])
      (EqA ![avB + 1, 0, 0, avA, 0, 0]) (EqB ![avB + 1, 0, 0, avA, 0, 0])
  · -- `b₂` kills `f, h`.
    rw [h1, h2] at EqB
    simp only [zero_mul, mul_zero, add_zero] at EqB
    exact fin_onept aB avB avA _ _ _ _ (EqB 0) (EqB ![1, 0, 0, 0, 0, 0])
      (EqB ![avB, 0, 0, avA + 1, 0, 0]) (EqA ![avB, 0, 0, avA + 1, 0, 0])
  · -- `a₂ + b₂` kills `f, h`.
    rw [h1, h2] at EqB
    exact fin_case3 aA aB avA avB _ _ _ _ _ _ (EqA 0) (EqB 0) (EqA ![0, 0, 0, 1, 0, 0])
      (EqB ![0, 0, 0, 1, 0, 0]) (EqA ![avB + 1, 0, 0, avA + 1, 0, 0])
      (EqB ![avB + 1, 0, 0, avA + 1, 0, 0])

/-! ## Proposition B3 -/

theorem fin_00 : ∀ F H f h z C s : F₂,
    (F + 0 * (f * h)) * (H + 0 * (f * h)) + z = C + s * (f * h) →
    F * H + z + C + s * (f * h) = 0 := by
  decide

theorem fin_10 : ∀ F H f h z C s : F₂,
    (F + 1 * (f * h)) * (H + 0 * (f * h)) + z = C + s * (f * h) →
    (H + s * 1) * (F + f * h) + z + (C + s * F) = 0 := by
  decide

theorem fin_01 : ∀ F H f h z C s : F₂,
    (F + 0 * (f * h)) * (H + 1 * (f * h)) + z = C + s * (f * h) →
    (F + s * 1) * (H + f * h) + z + (C + s * H) = 0 := by
  decide

theorem fin_11 : ∀ F H f h z C s : F₂,
    (F + 1 * (f * h)) * (H + 1 * (f * h)) + z = C + s * (f * h) →
    (F + H + (s + 1) * 1) * (F + f * h) + z + (F + C + (s + 1) * F) = 0 := by
  decide

/-- **Proposition B3 (general coset lemma).** On a coset base `A`, with
`g = f h` (`f, h ∈ A`), no `F, H ∈ A + ⟨g⟩` satisfy `F H + z₂ ∈ A + ⟨g⟩`. -/
theorem coset_obstruction {A : Submodule F₂ (ANF 6)} (hA : CosetBase A) {f h F H : ANF 6}
    (hf : f ∈ A) (hh : h ∈ A) (hF : F ∈ A ⊔ Submodule.span F₂ {f * h})
    (hH : H ∈ A ⊔ Submodule.span F₂ {f * h})
    (hFH : F * H + lowMul3 2 ∈ A ⊔ Submodule.span F₂ {f * h}) : False := by
  obtain ⟨F', hF', w1, hw1, rfl⟩ := Submodule.mem_sup.mp hF
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hw1
  obtain ⟨H', hH', w2, hw2, rfl⟩ := Submodule.mem_sup.mp hH
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw2
  obtain ⟨C, hC, w3, hw3, hCeq⟩ := Submodule.mem_sup.mp hFH
  obtain ⟨σ, rfl⟩ := Submodule.mem_span_singleton.mp hw3
  have hpt : ∀ x, (eval F' x + s * (eval f x * eval h x)) *
      (eval H' x + t * (eval f x * eval h x)) + eval (lowMul3 2) x =
      eval C x + σ * (eval f x * eval h x) := fun x => by
    have := congrArg (fun p => eval p x) hCeq
    simp only [eval_add', eval_mul', eval_smul'] at this
    exact this.symm
  have memc : ∀ c : F₂, ∀ P ∈ A, P + c • (1 : ANF 6) ∈ A := fun c P hP =>
    Submodule.add_mem _ hP (Submodule.smul_mem _ _ (hA.affine_le (one_mem_affine 6)))
  rcases f2_eq_zero_or_one s with rfl | rfl <;> rcases f2_eq_zero_or_one t with rfl | rfl
  · exact coset_B3a hA hF' hH' hf hh hC σ fun x => fin_00 _ _ _ _ _ _ _ (hpt x)
  · refine coset_B3b hA (memc σ F' hF') hH' hf hh
      (Submodule.add_mem _ hC (Submodule.smul_mem _ σ hH')) fun x => ?_
    rw [eval_add', eval_smul', eval_one', eval_add', eval_smul']
    exact fin_01 _ _ _ _ _ _ _ (hpt x)
  · refine coset_B3b hA (memc σ H' hH') hF' hf hh
      (Submodule.add_mem _ hC (Submodule.smul_mem _ σ hF')) fun x => ?_
    rw [eval_add', eval_smul', eval_one', eval_add', eval_smul']
    exact fin_10 _ _ _ _ _ _ _ (hpt x)
  · refine coset_B3b hA (memc (σ + 1) (F' + H') (Submodule.add_mem _ hF' hH')) hF' hf hh
      (Submodule.add_mem _ (Submodule.add_mem _ hF' hC) (Submodule.smul_mem _ (σ + 1) hF'))
      fun x => ?_
    rw [eval_add', eval_add', eval_smul', eval_one', eval_add', eval_add', eval_smul']
    exact fin_11 _ _ _ _ _ _ _ (hpt x)

/-- `z₂ ∉ A + ⟨g⟩` on a coset base. -/
theorem coset_z2_not_mem {A : Submodule F₂ (ANF 6)} (hA : CosetBase A) {f h : ANF 6}
    (hf : f ∈ A) (hh : h ∈ A) (hz : lowMul3 2 ∈ A ⊔ Submodule.span F₂ {f * h}) : False := by
  obtain ⟨C, hC, w, hw, hCeq⟩ := Submodule.mem_sup.mp hz
  obtain ⟨σ, rfl⟩ := Submodule.mem_span_singleton.mp hw
  refine coset_B3a hA (Submodule.zero_mem _) (Submodule.zero_mem _) hf hh hC σ fun x => ?_
  have := congrArg (fun p => eval p x) hCeq
  simp only [eval_add', eval_mul', eval_smul'] at this
  have e0 : eval (0 : ANF 6) x = 0 := by rw [eval_eq_evalHom, map_zero]
  rw [e0, ← this]
  generalize eval C x = a
  generalize σ * (eval f x * eval h x) = b
  revert a b
  decide

/-! ## `V(Q)` for `Q ⊆ Λ²(U)` is a coset base; `B3Claim` -/

theorem cosetBase_V4 {Q : Submodule F₂ TwoForm6} (hQ : ∀ ω ∈ Q, Phi ω = 0) :
    CosetBase (V4 Q) where
  affine_le := affine_le_V4 Q
  derivA X hX x := by
    have hb := deriv_add_deriv_zero_eq (Or.inl rfl) X hX.1 x
    have h0 : iota dirA2 (pi2 X) = 0 := congrArg Prod.fst (hQ _ hX.2)
    rw [h0] at hb
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hb
    exact f2_eq_of_add_eq_zero hb
  derivB X hX x := by
    have hb := deriv_add_deriv_zero_eq (Or.inr (Or.inl rfl)) X hX.1 x
    have h0 : iota dirB2 (pi2 X) = 0 := congrArg Prod.snd (hQ _ hX.2)
    rw [h0] at hb
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hb
    exact f2_eq_of_add_eq_zero hb
  rad1 X hX := cp_one_eq_zero_of_deg3 (hX.1.mono (by norm_num))
  radA X hX := by
    have h := cp_one_eq_zero_of_deg3 (DegreeLE.mul hX.1 (degreeLE_one_of_mem_affine
      (X_mem_affine (0 : Fin 6))))
    simpa [cp, one6, eval_mul', eval_X] using h
  radB X hX := by
    have h := cp_one_eq_zero_of_deg3 (DegreeLE.mul hX.1 (degreeLE_one_of_mem_affine
      (X_mem_affine (3 : Fin 6))))
    simpa [cp, one6, eval_mul', eval_X] using h

/-- **`B3Claim` holds** (Proposition B3 of `lambda3_proof.tex`, for every
`Q ⊆ Λ²(U)`). -/
theorem b3Claim : B3Claim := fun _ hQ _ _ _ _ hf hh hF hH hFH =>
  coset_obstruction (cosetBase_V4 hQ) hf hh hF hH hFH

/-- `LambdaCase 3` now depends only on `BadClaim`. -/
theorem lambdaCase_three_of_badClaim (hbad : BadClaim) : LambdaCase 3 :=
  lambdaCase_three_of hbad b3Claim

/-- `MC(lowMul3) = 6` from `LambdaCase 1`, `LambdaCase 2` and `BadClaim`. -/
theorem mc_eq_six_of_badClaim (h1 : LambdaCase 1) (h2 : LambdaCase 2) (hbad : BadClaim) :
    MC(lowMul3) = 6 :=
  mc_eq_six_of_claims h1 h2 hbad b3Claim

end

end LowHalfMul3

end UnrestrictedBooleanMul
