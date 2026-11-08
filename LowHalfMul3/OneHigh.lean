module

public import LowHalfMul3.LambdaTwo

@[expose] public section

/-!
# Proposition `onehigh` outside `Λ²(U)`: parts 1 and 2

Notation: `Q = span{P₀, l ∧ r}` (`Q3span l r 0 0`), `S = Q + ⟨Z₁⟩` (`Sspan l r`),
`A = V(S)`. A last product with factors in `A + ⟨g⟩`, `g = f h`, normalizes to
(a) `F H + σ g + z₂ ∈ A` with `F, H ∈ A`, or (b) `k (g + F) + z₂ ∈ A` with `k, F ∈ A`.

* **Part 1** (`z2_not_mem_S_sup`): `z₂ ∉ A + ⟨f h⟩`. `S` always has a good direction
  (`goodDir_S`: `span{P₀, l ∧ r}` has one by `goodDir_zero2`, and adding `Z₁` keeps it),
  so Lemma 8′ (`starFree_of_goodDir`) excludes `f h + z₂ ∈ A`. The same lemma gives
  form (a) with `σ = 0` (`formA_zero`). No hypothesis on `l ∧ r` is needed.
* **Part 2** (`formA_one`): form (a) with `σ = 1`, `F H + f h + z₂ ∈ A`, is impossible
  when `l` has an external coordinate. Sum over the 16 points of the cube
  `K = {(a, b, m₂λ, p, q, m₅λ)}`, `λ = l₀a + l₁b + l₃p + l₄q`, `l₂m₂ + l₅m₅ = 1`, which
  lies in `ker l` and projects onto the `U`-coordinates `(a₀, a₁, b₀, b₁) = (a, b, p, q)`.
  On `K` the product `L R` with `π₂(L R) = l ∧ r` vanishes, so every element of `A`
  restricts to `c₀ + c₁a + c₂b + c₃p + c₄q + c₅ap + c₆(aq + bp)` (`eval_cpt_of_mem`).
  The cube sum of a product of two such functions is `0` (`csum_phi_mul`: their
  product has no `abpq` term, because `(aq + bp)² = aq + bp` in characteristic two),
  while the cube sum of `z₂` is `1` (`csum_z2`, the carry). This is the
  fourth-difference argument of the plan, in coordinates.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-- `S = span{P₀, l ∧ r, Z₁}`. -/
abbrev Sspan (l r : Fin 6 → F₂) : Submodule F₂ TwoForm6 :=
  Q3span l r 0 0 ⊔ Submodule.span F₂ {Z1form}

theorem goodDir_Q2 (l r : Fin 6 → F₂) : GoodDir (Q3span l r 0 0) :=
  goodDir_zero2 ⟨rfl, rfl, rfl, rfl⟩

theorem goodDir_S (l r : Fin 6 → F₂) : GoodDir (Sspan l r) :=
  goodDir_sup_Z1 (goodDir_Q2 l r)

/-! ## Part 1 -/

/-- **Part 1 of Proposition `onehigh`**: `z₂ ∉ V(S) + ⟨f h⟩` for `f, h ∈ V(S)`. -/
theorem z2_not_mem_S_sup {l r : Fin 6 → F₂} {f h : ANF 6} (hf : f ∈ V4 (Sspan l r))
    (hh : h ∈ V4 (Sspan l r))
    (hz : lowMul3 2 ∈ V4 (Sspan l r) ⊔ Submodule.span F₂ {f * h}) : False := by
  rcases mem_sup_span_cases hz with h0 | h1
  · exact not_degreeLE_two_lowMul3_two h0.1
  · exact starFree_of_goodDir (goodDir_S l r) f h hf hh h1

/-- **Form (a), `σ = 0`.** -/
theorem formA_zero {l r : Fin 6 → F₂} {F H : ANF 6} (hF : F ∈ V4 (Sspan l r))
    (hH : H ∈ V4 (Sspan l r)) (hFH : F * H + lowMul3 2 ∈ V4 (Sspan l r)) : False :=
  starFree_of_goodDir (goodDir_S l r) F H hF hH hFH

/-! ## Part 2: the cube in `ker l` -/

/-- The cube point with `U`-coordinates `(a₀, a₁, b₀, b₁) = (a, b, p, q)`. -/
def cpt (l : Fin 6 → F₂) (m2 m5 a b p q : F₂) : Fin 6 → F₂ :=
  ![a, b, m2 * (l 0 * a + l 1 * b + l 3 * p + l 4 * q), p, q,
    m5 * (l 0 * a + l 1 * b + l 3 * p + l 4 * q)]

/-- The restrictions of `V(S)` to the cube. -/
def phi7 (c0 c1 c2 c3 c4 c5 c6 a b p q : F₂) : F₂ :=
  c0 + c1 * a + c2 * b + c3 * p + c4 * q + c5 * (a * p) + c6 * (a * q + b * p)

/-- `z₂` on the cube. -/
def z2pt (l0 l1 l3 l4 m2 m5 a b p q : F₂) : F₂ :=
  a * (m5 * (l0 * a + l1 * b + l3 * p + l4 * q)) + b * q +
    m2 * (l0 * a + l1 * b + l3 * p + l4 * q) * p + a * b * p * q

/-- The sum over the 16 points of the cube. -/
def csum (G : F₂ → F₂ → F₂ → F₂ → F₂) : F₂ :=
  G 0 0 0 0 + G 0 0 0 1 + G 0 0 1 0 + G 0 0 1 1 + G 0 1 0 0 + G 0 1 0 1 + G 0 1 1 0 + G 0 1 1 1 + G 1 0 0 0 + G 1 0 0 1 + G 1 0 1 0 + G 1 0 1 1 + G 1 1 0 0 + G 1 1 0 1 + G 1 1 1 0 + G 1 1 1 1

theorem csum_add (G G' : F₂ → F₂ → F₂ → F₂ → F₂) :
    csum (fun a b p q => G a b p q + G' a b p q) = csum G + csum G' := by
  simp only [csum]; ring

set_option maxRecDepth 100000 in
theorem csum_phi_basis : ∀ c0 c1 c2 c3 c4 c5 c6 : F₂,
      csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * 1) = 0 ∧
      csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * a) = 0 ∧
      csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * b) = 0 ∧
      csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * p) = 0 ∧
      csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * q) = 0 ∧
      csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * (a * p)) = 0 ∧
      csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * (a * q + b * p)) = 0 := by
  decide

/-- The cube sum of a product of two restrictions vanishes (bilinearity and
`csum_phi_basis`). -/
theorem csum_phi_mul (c0 c1 c2 c3 c4 c5 c6 d0 d1 d2 d3 d4 d5 d6 : F₂) :
    csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q *
      phi7 d0 d1 d2 d3 d4 d5 d6 a b p q) = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := csum_phi_basis c0 c1 c2 c3 c4 c5 c6
  have e : csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q *
      phi7 d0 d1 d2 d3 d4 d5 d6 a b p q) =
        d0 * csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * 1) +
        d1 * csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * a) +
        d2 * csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * b) +
        d3 * csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * p) +
        d4 * csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * q) +
        d5 * csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * (a * p)) +
        d6 * csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q * (a * q + b * p)) := by
    simp only [csum, phi7]; ring
  rw [e, h0, h1, h2, h3, h4, h5, h6]; ring

set_option maxRecDepth 100000 in
theorem csum_phi : ∀ c0 c1 c2 c3 c4 c5 c6 : F₂,
    csum (fun a b p q => phi7 c0 c1 c2 c3 c4 c5 c6 a b p q) = 0 := by
  decide

set_option maxRecDepth 100000 in
/-- The cube sum of `z₂` is the carry coefficient, `1`. -/
theorem csum_z2 : ∀ l0 l1 l3 l4 m2 m5 : F₂,
    csum (fun a b p q => z2pt l0 l1 l3 l4 m2 m5 a b p q) = 1 := by
  decide

theorem lin_linANF_eq (v : Fin 6 → F₂) : lin (linANF v) = v := by
  ext i
  simp [lin, eval_linANF, dotv_unitVec, dotv_zero_right]

theorem dotv_cpt (v l : Fin 6 → F₂) (m2 m5 a b p q : F₂) :
    dotv v (cpt l m2 m5 a b p q) =
      (v 0 + (v 2 * m2 + v 5 * m5) * l 0) * a + (v 1 + (v 2 * m2 + v 5 * m5) * l 1) * b +
        (v 3 + (v 2 * m2 + v 5 * m5) * l 3) * p + (v 4 + (v 2 * m2 + v 5 * m5) * l 4) * q := by
  simp [dotv, cpt, Fin.sum_univ_succ]
  ring

theorem f2_self_add : ∀ x : F₂, x + x = 0 := by decide

theorem dotv_l_cpt {l : Fin 6 → F₂} {m2 m5 : F₂} (hm : l 2 * m2 + l 5 * m5 = 1)
    (a b p q : F₂) : dotv l (cpt l m2 m5 a b p q) = 0 := by
  rw [dotv_cpt, hm]
  simp only [one_mul, f2_self_add, zero_mul, add_zero]

theorem eval_z2_cpt (l : Fin 6 → F₂) (m2 m5 a b p q : F₂) :
    eval (lowMul3 2) (cpt l m2 m5 a b p q) = z2pt (l 0) (l 1) (l 3) (l 4) m2 m5 a b p q := by
  rw [eval_lowMul3_two]
  simp [cpt, z2pt]

theorem eval_z1_cpt (l : Fin 6 → F₂) (m2 m5 a b p q : F₂) :
    eval (lowMul3 1) (cpt l m2 m5 a b p q) = a * q + b * p := by
  rw [eval_lowMul3_one]
  simp [cpt]

theorem eval_p0_cpt (l : Fin 6 → F₂) (m2 m5 a b p q : F₂) :
    eval (aVar 3 0 * bVar 3 0) (cpt l m2 m5 a b p q) = a * p := by
  rw [← lowMul3_zero_eq_a0b0, eval_lowMul3_zero]
  simp [cpt]

theorem tf_three_cancel (A B C : TwoForm6) : A + B + C + A + B + C = 0 := by
  funext i j
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize A i j = x
  generalize B i j = y
  generalize C i j = z
  revert x y z
  decide

/-- Every element of `V(S)` restricts to the cube as a `phi7`. -/
theorem eval_cpt_of_mem {l r : Fin 6 → F₂} {m2 m5 : F₂} (hm : l 2 * m2 + l 5 * m5 = 1)
    {X : ANF 6} (hX : X ∈ V4 (Sspan l r)) :
    ∃ c0 c1 c2 c3 c4 c5 c6 : F₂, ∀ a b p q : F₂,
      eval X (cpt l m2 m5 a b p q) = phi7 c0 c1 c2 c3 c4 c5 c6 a b p q := by
  obtain ⟨hdeg, hpi⟩ := hX
  obtain ⟨q, hq, z, hz, hqz⟩ := Submodule.mem_sup.mp hpi
  obtain ⟨ζ, rfl⟩ := Submodule.mem_span_singleton.mp hz
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F₂).mp hq
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, wedge_self, smul_zero, add_zero] at hc
  have hPdeg : DegreeLE 2 (aVar 3 0 * bVar 3 0) := (degreeLE_one_aVar 0).mul (degreeLE_one_bVar 0)
  have hLRdeg : DegreeLE 2 (linANF l * linANF r) :=
    (degreeLE_one_of_mem_affine (linANF_mem_affine l)).mul
      (degreeLE_one_of_mem_affine (linANF_mem_affine r))
  have hpiLR : pi2 (linANF l * linANF r) = wedge l r := by
    rw [pi2_mul_affine (linANF_mem_affine l) (linANF_mem_affine r), lin_linANF_eq, lin_linANF_eq]
  set Y := X + c 0 • (aVar 3 0 * bVar 3 0) + c 1 • (linANF l * linANF r) + ζ • lowMul3 1
    with hYdef
  have hYdeg : DegreeLE 2 Y :=
    ((hdeg.add (hPdeg.smul _)).add (hLRdeg.smul _)).add (degreeLE_two_lowMul3_one.smul _)
  have hYpi : pi2 Y = 0 := by
    rw [hYdef, map_add, map_add, map_add, map_smul, map_smul, map_smul, pi2_a0b0, hpiLR,
      pi2_lowMul3_one, ← hqz, ← hc]
    exact tf_three_cancel _ _ _
  have hYaff : Y ∈ affine 6 := mem_affine_of_degreeLE_two_of_pi2_eq_zero Y hYdeg hYpi
  refine ⟨eval Y 0, lin Y 0 + (lin Y 2 * m2 + lin Y 5 * m5) * l 0,
    lin Y 1 + (lin Y 2 * m2 + lin Y 5 * m5) * l 1, lin Y 3 + (lin Y 2 * m2 + lin Y 5 * m5) * l 3,
    lin Y 4 + (lin Y 2 * m2 + lin Y 5 * m5) * l 4, c 0, ζ, fun a b p q => ?_⟩
  have hY := eval_affine hYaff (cpt l m2 m5 a b p q)
  have hYe : eval Y (cpt l m2 m5 a b p q) = eval X (cpt l m2 m5 a b p q) + c 0 * (a * p) +
      c 1 * (0 * dotv r (cpt l m2 m5 a b p q)) + ζ * (a * q + b * p) := by
    rw [hYdef, eval_add', eval_add', eval_add', eval_smul', eval_smul', eval_smul', eval_p0_cpt,
      eval_mul', eval_linANF, eval_linANF, dotv_l_cpt hm, eval_z1_cpt]
  rw [hY, dotv_cpt] at hYe
  simp only [phi7]
  linear_combination (-1 : F₂) * hYe - (c 0 * (a * p) + ζ * (a * q + b * p)) * two_f2

/-- **Part 2 of Proposition `onehigh`**: form (a) with `σ = 1` is impossible when `l`
has an external coordinate. -/
theorem formA_one {l r : Fin 6 → F₂} (hl : l 2 = 1 ∨ l 5 = 1) {F H f h : ANF 6}
    (hF : F ∈ V4 (Sspan l r)) (hH : H ∈ V4 (Sspan l r)) (hf : f ∈ V4 (Sspan l r))
    (hh : h ∈ V4 (Sspan l r)) (hE : F * H + f * h + lowMul3 2 ∈ V4 (Sspan l r)) : False := by
  obtain ⟨m2, m5, hm⟩ : ∃ m2 m5 : F₂, l 2 * m2 + l 5 * m5 = 1 := by
    rcases hl with h2 | h5
    · exact ⟨1, 0, by rw [h2]; ring⟩
    · exact ⟨0, 1, by rw [h5]; ring⟩
  obtain ⟨F0, F1, F2, F3, F4, F5, F6, hFe⟩ := eval_cpt_of_mem hm hF
  obtain ⟨H0, H1, H2, H3, H4, H5, H6, hHe⟩ := eval_cpt_of_mem hm hH
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, hfe⟩ := eval_cpt_of_mem hm hf
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, hhe⟩ := eval_cpt_of_mem hm hh
  obtain ⟨E0, E1, E2, E3, E4, E5, E6, hEe⟩ := eval_cpt_of_mem hm hE
  have key : (fun a b p q => phi7 F0 F1 F2 F3 F4 F5 F6 a b p q * phi7 H0 H1 H2 H3 H4 H5 H6 a b p q +
      phi7 f0 f1 f2 f3 f4 f5 f6 a b p q * phi7 h0 h1 h2 h3 h4 h5 h6 a b p q +
      z2pt (l 0) (l 1) (l 3) (l 4) m2 m5 a b p q) =
      fun a b p q => phi7 E0 E1 E2 E3 E4 E5 E6 a b p q := by
    funext a b p q
    rw [← hFe, ← hHe, ← hfe, ← hhe, ← hEe, ← eval_z2_cpt, eval_add', eval_add', eval_mul',
      eval_mul']
  have hs := congrArg csum key
  rw [csum_add, csum_add, csum_phi_mul, csum_phi_mul, csum_z2, csum_phi] at hs
  exact absurd hs (by decide)

theorem Q3span_swap (l r : Fin 6 → F₂) : Q3span l r 0 0 = Q3span r l 0 0 := by
  rw [Q3span, Q3span, wedge_comm l r]

theorem ext_coord_of_phi {l r : Fin 6 → F₂} (hP : Phi (wedge l r) ≠ 0) :
    (l 2 = 1 ∨ l 5 = 1) ∨ (r 2 = 1 ∨ r 5 = 1) := by
  by_contra hc
  apply hP
  apply phi_eq_zero_of_rows
  have h0 : ∀ x : F₂, ¬ x = 1 → x = 0 := by decide
  have hl2 := h0 _ fun h => hc (Or.inl (Or.inl h))
  have hl5 := h0 _ fun h => hc (Or.inl (Or.inr h))
  have hr2 := h0 _ fun h => hc (Or.inr (Or.inl h))
  have hr5 := h0 _ fun h => hc (Or.inr (Or.inr h))
  intro t
  simp [wedge_apply, hl2, hl5, hr2, hr5]

/-- **Part 2** under the hypothesis of `TwoClaim`. -/
theorem formA_one_of_phi {l r : Fin 6 → F₂} (hP : Phi (wedge l r) ≠ 0) {F H f h : ANF 6}
    (hF : F ∈ V4 (Sspan l r)) (hH : H ∈ V4 (Sspan l r)) (hf : f ∈ V4 (Sspan l r))
    (hh : h ∈ V4 (Sspan l r)) (hE : F * H + f * h + lowMul3 2 ∈ V4 (Sspan l r)) : False := by
  rcases ext_coord_of_phi hP with hl | hr
  · exact formA_one hl hF hH hf hh hE
  · rw [Sspan, Q3span_swap] at hF hH hf hh hE
    exact formA_one hr hF hH hf hh hE

end

end LowHalfMul3

end UnrestrictedBooleanMul
