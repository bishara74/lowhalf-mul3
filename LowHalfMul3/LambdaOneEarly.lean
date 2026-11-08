module

public import LowHalfMul3.LambdaOneCore

@[expose] public section

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

local notation "⟪" p "⟫" => singleton p

theorem no_z1_q0 : z1 ∉ V4 Q0 := by
  intro h
  exact z1_not_mem_V4_two 0 0
    (V4_mono (show Q0 ≤ Qlr 0 0 by rw [qlr_eq]; exact le_sup_left) h)

theorem no_z1_in_first {f h : A6} (hf : f ∈ V4 Q0) (hh : h ∈ V4 Q0) :
    z1 ∉ Base (f * h) := by
  intro hz
  have hp : Phi (wedge (unitVec 2) (unitVec 5)) ≠ 0 := by
    intro he
    have h := congrArg (fun a : Vec × Vec => a.1 5) he
    simp [Phi, iota_dirA2_apply, wedge, unitVec] at h
  have hle := V4_mono (show Q0 ≤ Qlr (unitVec 2) (unitVec 5) by
    rw [qlr_eq]
    exact le_sup_left)
  exact noPlace_z1_two hp f h (hle hf) (hle hh) (hle
    ((mem_sup_span_cases hz).resolve_left no_z1_q0))

theorem linANF_add (l b : Vec) : linANF (l + b) = linANF l + linANF b := by
  apply eval_injective 6
  funext x
  simp [eval_linANF, dotv_add_left]

theorem lin_linANF (l : Vec) : lin (linANF l) = l := by
  ext i
  simp [lin, eval_linANF, dotv_unitVec, dotv_zero_right]

theorem pi2_linANF_mul (l b : Vec) : pi2 (linANF l * linANF b) = wedge l b := by
  rw [pi2_mul_affine (linANF_mem_affine l) (linANF_mem_affine b), lin_linANF, lin_linANF]

theorem extGate_pair (l b l' b' : Vec) :
    ExtGate 1 l b + ExtGate 1 l' b' =
      linANF (l + l') * linANF b + linANF l' * linANF (b + b') +
        P0 * linANF (b + b') := by
  rw [extGate_one, extGate_one, linANF_add, linANF_add]
  simp only [add_mul, mul_add]
  rw [add_assoc (linANF l * linANF b), ← add_assoc (linANF l' * linANF b),
    anf_add_self, zero_add]
  abel

theorem wedge_core_factors {l b : Vec} (h : Phi (wedge l b) = 0)
    (hn : wedge l b ≠ 0) : l 2 = 0 ∧ l 5 = 0 ∧ b 2 = 0 ∧ b 5 = 0 := by
  have zero_left (a c : Vec) (i : Fin 6) (h : iota (unitVec i) (wedge a c) = 0)
      (hne : wedge a c ≠ 0) : a i = 0 := by
    rcases f2_eq_zero_or_one (a i) with ha | ha
    · exact ha
    · rw [iota_wedge, dotv_unitVec, dotv_unitVec, ha, one_smul] at h
      rcases f2_eq_zero_or_one (c i) with hc | hc
      · rw [hc, zero_smul, add_zero] at h
        exact (hne (h ▸ wedge_zero_right a)).elim
      · rw [hc, one_smul] at h
        have he : c = a := by
          rw [← add_zero c, ← vec_add_self a, ← add_assoc, h, zero_add]
        exact (hne (he ▸ wedge_self a)).elim
  have h2 : iota (unitVec 2) (wedge l b) = 0 := congrArg Prod.fst h
  have h5 : iota (unitVec 5) (wedge l b) = 0 := congrArg Prod.snd h
  refine ⟨zero_left l b 2 h2 hn, zero_left l b 5 h5 hn, ?_, ?_⟩
  · exact zero_left b l 2 (by rwa [wedge_comm b l]) (by rwa [wedge_comm b l])
  · exact zero_left b l 5 (by rwa [wedge_comm b l]) (by rwa [wedge_comm b l])

theorem early_z1_ordinary {l b : Vec} (hb : OffLowSpan b)
    {f h : A6} (hf : f ∈ V4 Q0) (hh : h ∈ V4 Q0)
    (hz : f * h + z1 ∈ Base (ExtGate 1 l b)) :
    CoreHi (ExtGate 1 l b) := by
  have hpair : f * h + z1 + ExtGate 1 l b ∈ V4 Q0 := by
    rcases mem_sup_span_cases hz with hz0 | hz1
    · exact (no_z1_in_first hf hh (mem_extend.mpr ⟨f*h+z1, hz0, 1, by
        rw [one_smul, add_comm (f*h), add_cancel_right]⟩)).elim
    · simpa only [add_comm (ExtGate 1 l b)] using hz1
  have hn : ¬ (f ∈ affine 6 ∧ h ∈ affine 6) := by
    rintro ⟨ha, hd⟩
    have hd' := (degreeLE_one_of_mem_affine ha).mul (degreeLE_one_of_mem_affine hd)
    have hc := (hd'.add degreeLE_two_lowMul3_one).add hpair.1
    rw [add_cancel_left] at hc
    exact (first_cubic_iff l b).mpr hb hc
  obtain ⟨l', b', hnorm⟩ := first_normal_form hf hh hn
  have hpair' : ExtGate 1 l b + ExtGate 1 l' b' + z1 ∈ V4 Q0 := by
    have hm := (V4 Q0).add_mem hpair hnorm
    have he : (f*h + z1 + ExtGate 1 l b) + (f*h + ExtGate 1 l' b') =
        ExtGate 1 l b + ExtGate 1 l' b' + z1 := by
      rw [add_assoc (f*h), add_add_add_comm, anf_add_self, zero_add]
      ac_rfl
    exact he ▸ hm
  have hlow : ¬ OffLowSpan (b + b') := by
    rintro ⟨i, h0, h3, hi⟩
    have hcard : ({0, 3} ∪ {i} : Finset (Fin 6)).card = 3 := by
      fin_cases i <;> simp_all <;> decide
    have hz' := hpair'.1 ⟨{0, 3} ∪ {i}⟩ (by change 2 < ({0, 3} ∪ {i} : Finset (Fin 6)).card; rw [hcard]; decide)
    have hz1 := degreeLE_two_lowMul3_one ⟨{0, 3} ∪ {i}⟩ (by change 2 < ({0, 3} ∪ {i} : Finset (Fin 6)).card; rw [hcard]; decide)
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, first_cubic_coeff _ _ h0 h3,
      hz1, add_zero] at hz'
    exact one_ne_zero (hi.symm.trans hz')
  have hp := hpair'.2
  rw [extGate_pair, low_mul_linear hlow, map_add, map_add, map_add,
    pi2_linANF_mul, pi2_linANF_mul, map_smul, pi2_a0b0, pi2_lowMul3_one] at hp
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hp
  have hsplit : wedge (l + l') b + wedge l' (b + b') =
      Z1form + (t + (b + b') 0 + (b + b') 3) • P0form := by
    let D : TwoForm6 := ((b + b') 0 + (b + b') 3) • P0form + Z1form
    have ht' : t • P0form = (wedge (l + l') b + wedge l' (b + b')) + D := by
      simpa only [D, add_assoc] using ht
    have he : t • P0form + D = wedge (l + l') b + wedge l' (b + b') := by
      rw [ht', add_assoc, tf_add_self, add_zero]
    rw [← he]
    simp only [D, add_smul, add_assoc, add_comm, add_left_comm]
  have hne₁ : wedge (l + l') b ≠ 0 := by
    intro he
    rw [he, zero_add] at hsplit
    exact wedge_ne_Z _ _ _ hsplit
  have hne₂ : wedge l' (b + b') ≠ 0 := by
    intro he
    rw [he, add_zero] at hsplit
    exact wedge_ne_Z _ _ _ hsplit
  obtain ⟨hm2, hm5, hb2, hb5⟩ := wedge_core_factors (lemma3 hsplit) hne₁
  have hphi : Phi (wedge l' (b+b')) = 0 :=
    lemma3 ((add_comm (wedge l' (b+b')) (wedge (l+l') b)).trans hsplit)
  obtain ⟨hl2, hl5, _, _⟩ := wedge_core_factors hphi hne₂
  exact coreHi_extGate_of_core (by simpa [Pi.add_apply, hl2] using hm2)
    (by simpa [Pi.add_apply, hl5] using hm5) hb2 hb5

structure LowForm where
  constant : F₂
  quadratic : F₂
  slope : Vec

def LowForm.value (f : LowForm) (x : Vec) : F₂ :=
  f.constant + dotv f.slope x + f.quadratic * (x 0 * x 3)

theorem lowForm_of_mem {p : A6} (hp : p ∈ V4 Q0) :
    ∃ f : LowForm, ∀ x, eval p x = f.value x := by
  rw [v4_q0] at hp
  obtain ⟨a, ha, t, rfl⟩ := mem_extend.mp hp
  refine ⟨⟨eval a 0, t, lin a⟩, fun x => ?_⟩
  rw [LowForm.value, eval_add', eval_smul', eval_p0, eval_affine ha]

theorem lowForm_shift (f : LowForm) (x : Vec) {i : Fin 6} (hi0 : i ≠ 0) (hi3 : i ≠ 3) :
    f.value (x + unitVec i) = f.value x + f.slope i := by
  simp only [LowForm.value, dotv_add_right, dotv_unitVec, Pi.add_apply, unitVec,
    if_neg (Ne.symm hi0), if_neg (Ne.symm hi3), add_zero]
  ring

def rValue (v : LowForm) (x : Vec) : F₂ := x 0 * x 4 + x 1 * x 3 + v.value x

def rSlope (v : LowForm) (x : Vec) (i : Fin 6) : F₂ :=
  v.slope i + x 0 * unitVec i 4 + unitVec i 1 * x 3

theorem rValue_shift (v : LowForm) (x : Vec) {i : Fin 6} (hi0 : i ≠ 0) (hi3 : i ≠ 3) :
    rValue v (x + unitVec i) = rValue v x + rSlope v x i := by
  rw [rValue, lowForm_shift v x hi0 hi3]
  simp only [rValue, rSlope, Pi.add_apply, unitVec, if_neg (Ne.symm hi0),
    if_neg (Ne.symm hi3), add_zero]
  ring

theorem rSlope_shift (v : LowForm) (x : Vec) (i : Fin 6) {j : Fin 6} (hj0 : j ≠ 0)
    (hj3 : j ≠ 3) : rSlope v (x + unitVec j) i = rSlope v x i := by
  simp [rSlope, unitVec, Ne.symm hj0, Ne.symm hj3]

def lowPoint (s t : F₂) : Vec := ![s, 0, 0, t, 0, 0]

theorem lowPoint_slopes (v : LowForm) (s t : F₂) :
    rSlope v (lowPoint s t) 1 = v.slope 1 + t ∧
      rSlope v (lowPoint s t) 4 = v.slope 4 + s := by
  simp [rSlope, lowPoint, unitVec, add_comm]

private theorem fiber_line_contradiction : ∀ u v a b m n : F₂,
    (∀ s t : F₂, (u + t = 0 ∧ v + s = 0) ∨
      ∃ e : F₂, u + t = a + e * m ∧ v + s = b + e * n) → False := by
  decide

private theorem fixed_shift_scalar : ∀ k r d : F₂,
    k * r = r → (k + 1) * (r + d) = r + d → r = k * d := by
  decide

private theorem fiber_cross_scalar : ∀ A B a b c d e u v : F₂,
    (A + a) * (B + b) + (A * B + e) = u →
    (A + c + a) * (B + d + b) + ((A + c) * (B + d) + e) = v →
    u = v → a * d + b * c = 0 := by
  decide

private theorem fiber_slope_scalar : ∀ A B d b : F₂,
    (A + d * b) * (B + b) + A * B = (A + d * (B + 1)) * b := by
  decide

theorem eval_extGate_one (l b x : Vec) :
    eval (ExtGate 1 l b) x = (x 0 * x 3 + dotv l x) * dotv b x := by
  rw [extGate_one, eval_mul', eval_add', eval_linANF, eval_linANF, eval_p0]

theorem early_z1_feedback {l b : Vec} (hb : OffLowSpan b)
    {k F : A6} (hk : k ∈ V4 Q0) (hF : F ∈ V4 Q0) :
    k * (ExtGate 1 l b + F) + z1 ∉ V4 Q0 := by
  intro hv
  obtain ⟨K, hK⟩ := lowForm_of_mem hk
  obtain ⟨G, hG⟩ := lowForm_of_mem hF
  obtain ⟨V, hV⟩ := lowForm_of_mem hv
  have hR (x : Vec) : K.value x * (eval (ExtGate 1 l b) x + G.value x) = rValue V x := by
    rw [rValue, ← hV x, eval_add', eval_mul', eval_add', hK, hG, eval_lowMul3_one]
    rw [add_comm (x 0 * x 4 + x 1 * x 3), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hfix (x : Vec) : K.value x * rValue V x = rValue V x := by
    rw [← hR x, ← mul_assoc, f2_mul_self]
  have hKlow (i : Fin 6) (hi0 : i ≠ 0) (hi3 : i ≠ 3) : K.slope i = 0 := by
    rcases f2_eq_zero_or_one (K.slope i) with hz | ho
    · exact hz
    · exfalso
      have he (x : Vec) : rValue V x = K.value x * rSlope V x i := by
        have h := hfix (x + unitVec i)
        rw [lowForm_shift K x hi0 hi3, ho, rValue_shift V x hi0 hi3] at h
        exact fixed_shift_scalar _ _ _ (hfix x) h
      apply fiber_line_contradiction (V.slope 1) (V.slope 4) 0 0 (K.slope 1) (K.slope 4)
      intro s t
      let x := lowPoint s t
      have h₁ (j : Fin 6) (hj0 : j ≠ 0) (hj3 : j ≠ 3) :
          rSlope V x j = rSlope V x i * K.slope j := by
        have hh := he (x + unitVec j)
        rw [rValue_shift V x hj0 hj3, lowForm_shift K x hj0 hj3,
          rSlope_shift V x i hj0 hj3, add_mul, ← he x] at hh
        simpa only [add_zero, mul_comm] using add_left_cancel hh
      exact Or.inr ⟨rSlope V x i,
        by simpa [x, (lowPoint_slopes V s t).1] using h₁ 1 (by decide) (by decide),
        by simpa [x, (lowPoint_slopes V s t).2] using h₁ 4 (by decide) (by decide)⟩
  have hshiftK (x : Vec) {i : Fin 6} (hi0 : i ≠ 0) (hi3 : i ≠ 3) :
      K.value (x + unitVec i) = K.value x := by
    rw [lowForm_shift K x hi0 hi3, hKlow i hi0 hi3, add_zero]
  have hKone : ∃ s t : F₂, K.value (lowPoint s t) = 1 := by
    let x := lowPoint 0 (V.slope 1 + 1)
    refine ⟨0, V.slope 1 + 1, ?_⟩
    rcases f2_eq_zero_or_one (K.value x) with hz | ho
    · have hz' : rValue V x = 0 := by rw [← hfix x, hz, zero_mul]
      have h := hfix (x + unitVec 1)
      rw [hshiftK x (by decide) (by decide), hz, zero_mul,
        rValue_shift V x (by decide) (by decide), hz', zero_add] at h
      rw [show rSlope V x 1 = 1 by
        change rSlope V (lowPoint 0 (V.slope 1 + 1)) 1 = _
        rw [(lowPoint_slopes V 0 _).1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]] at h
      exact (zero_ne_one h).elim
    · exact ho
  obtain ⟨j, hj0, hj3, hj⟩ := hb
  obtain ⟨s, t, hst⟩ := hKone
  let x := lowPoint s t
  have hlin (i : Fin 6) (hi0 : i ≠ 0) (hi3 : i ≠ 3) : l i = l j * b i := by
    have hc (y : Vec) (hy : K.value y = 1) :
        eval (ExtGate 1 l b) y + G.value y = rValue V y := by
      simpa only [hy, one_mul] using hR y
    have E (y : Vec) (hy : K.value y = 1) :
        eval (ExtGate 1 l b) (y + unitVec i) + eval (ExtGate 1 l b) y +
          G.slope i = rSlope V y i := by
      have h := congrArg₂ (· + ·) (hc (y + unitVec i) (by rwa [hshiftK y hi0 hi3])) (hc y hy)
      rw [lowForm_shift G y hi0 hi3, rValue_shift V y hi0 hi3, add_add_add_comm,
        add_right_comm (G.value y), CharTwo.add_self_eq_zero, zero_add,
        add_right_comm (rValue V y), CharTwo.add_self_eq_zero, zero_add] at h
      exact h
    have e₁ := E x hst
    have e₂ := E (x + unitVec j) (by rwa [hshiftK x hj0 hj3])
    rw [rSlope_shift V x i hj0 hj3] at e₂
    simp only [eval_extGate_one, dotv_add_right, dotv_unitVec, Pi.add_apply, unitVec,
      if_neg (Ne.symm hi0), if_neg (Ne.symm hi3), if_neg (Ne.symm hj0),
      if_neg (Ne.symm hj3), add_zero, ← add_assoc] at e₁ e₂
    have hh := fiber_cross_scalar (x 0 * x 3 + dotv l x) (dotv b x) (l i) (b i) (l j) (b j)
      (G.slope i) (rSlope V x i) (rSlope V x i)
      (by simpa only [add_assoc] using e₁) (by simpa only [add_assoc] using e₂) rfl
    rw [hj, mul_one, mul_comm (b i)] at hh
    exact f2_eq_of_add_eq_zero hh
  apply fiber_line_contradiction (V.slope 1) (V.slope 4) (G.slope 1) (G.slope 4) (b 1) (b 4)
  intro s' t'
  let y := lowPoint s' t'
  have ys := lowPoint_slopes V s' t'
  rcases f2_eq_zero_or_one (K.value y) with hz | ho
  · have hz₀ : rValue V y = 0 := by rw [← hfix y, hz, zero_mul]
    have hz₁ (i : Fin 6) (hi0 : i ≠ 0) (hi3 : i ≠ 3) : rSlope V y i = 0 := by
      have h := hfix (y + unitVec i)
      rw [hshiftK y hi0 hi3, hz, zero_mul, rValue_shift V y hi0 hi3, hz₀, zero_add] at h
      exact h.symm
    exact Or.inl ⟨by simpa only [y, ys.1] using hz₁ 1 (by decide) (by decide),
      by simpa only [y, ys.2] using hz₁ 4 (by decide) (by decide)⟩
  · let α := y 0 * y 3 + dotv l y + l j * (dotv b y + 1)
    have he (i : Fin 6) (hi0 : i ≠ 0) (hi3 : i ≠ 3) :
        rSlope V y i = G.slope i + α * b i := by
      have h := congrArg₂ (· + ·) (hR (y + unitVec i)) (hR y)
      rw [hshiftK y hi0 hi3, ho, one_mul, one_mul, lowForm_shift G y hi0 hi3,
        rValue_shift V y hi0 hi3, add_add_add_comm, add_right_comm (G.value y),
        CharTwo.add_self_eq_zero, zero_add, add_right_comm (rValue V y),
        CharTwo.add_self_eq_zero, zero_add] at h
      simp only [eval_extGate_one, dotv_add_right, dotv_unitVec, Pi.add_apply, unitVec,
        if_neg (Ne.symm hi0), if_neg (Ne.symm hi3), add_zero, ← add_assoc] at h
      rw [hlin i hi0 hi3] at h
      have h' := fiber_slope_scalar (y 0 * y 3 + dotv l y) (dotv b y) (l j) (b i)
      rw [h', add_comm] at h
      exact h.symm
    exact Or.inr ⟨α, by simpa only [y, ys.1] using he 1 (by decide) (by decide),
      by simpa only [y, ys.2] using he 4 (by decide) (by decide)⟩

theorem early_z1_core (hnormal : FeedbackNormal) {l b : Vec} (hb : OffLowSpan b)
    {f h : A6} (hf : f ∈ Base (ExtGate 1 l b)) (hh : h ∈ Base (ExtGate 1 l b))
    (hz : z1 ∈ Base (ExtGate 1 l b) ⊔ ⟪f * h⟫) :
    CoreHi (ExtGate 1 l b) := by
  have h' : f * h + z1 ∈ V4 Q0 ⊔ ⟪ExtGate 1 l b⟫ := by
    rcases mem_sup_span_cases hz with h0 | h1
    · have hdeg := h0
      rcases mem_sup_span_cases hdeg with h0' | h1'
      · exact (no_z1_q0 h0').elim
      · have h := degreeLE_two_lowMul3_one.add h1'.1
        rw [add_comm (ExtGate 1 l b), add_cancel_left] at h
        exact ((first_cubic_iff l b).mpr hb h).elim
    · exact h1
  rcases hnormal (affine_le_V4 Q0 (one_mem_affine 6)) hf hh
      h' with
    h | h
  · obtain ⟨f', h', hf', hh', hz'⟩ := h
    exact early_z1_ordinary hb hf' hh' hz'
  · obtain ⟨k, F, hk, hF, h⟩ := h
    exact (early_z1_feedback hb hk hF h).elim

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
