module

public import LowHalfMul3.LambdaOneParity
public import LowHalfMul3.LambdaOneEarly

@[expose] public section

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

open scoped BigOperators

local notation "⟪" p "⟫" => singleton p

theorem s0_decompose {p : A6} (hp : p ∈ V4 S0) :
    ∃ a ∈ affine 6, ∃ w z : F₂, p = a + w • P0 + z • z1 := by
  rw [v4_s0, v4_q0] at hp
  obtain ⟨q, hq, z, rfl⟩ := mem_extend.mp hp
  obtain ⟨a, ha, w, rfl⟩ := mem_extend.mp hq
  exact ⟨a, ha, w, z, rfl⟩

theorem p0_mul_z1 : P0 * z1 = P0 * (X (1 : Fin 6) + X (4 : Fin 6)) := by
  apply eval_injective 6
  funext x
  change eval (P0 * z1) x = eval (P0 * (X 1 + X 4)) x
  rw [eval_mul' P0 z1, eval_mul' P0 (X 1 + X 4), eval_p0]
  simp only [eval_add', eval_X, eval_lowMul3_one, mul_add]
  calc
    _ = (x 0 * x 0) * x 3 * x 4 + x 0 * (x 3 * x 3) * x 1 := by ring
    _ = _ := by rw [f2_mul_self, f2_mul_self]; ring

theorem degree_s0_mul {f h : A6} (hf : f ∈ V4 S0) (hh : h ∈ V4 S0) :
    DegreeLE 3 (f * h) := by
  obtain ⟨a, ha, w, z, rfl⟩ := s0_decompose hf
  obtain ⟨b, hb, u, v, rfl⟩ := s0_decompose hh
  have hqa : DegreeLE 2 (a + w • P0 + z • z1) :=
    ((degreeLE_one_of_mem_affine ha).mono (by omega)).add (p0_degree.smul w)
      |>.add (degreeLE_two_lowMul3_one.smul z)
  have hp : DegreeLE 3 (P0 * z1) := by
    rw [p0_mul_z1]
    exact p0_degree.mul (degreeLE_one_of_mem_affine ((affine 6).add_mem
      (X_mem_affine 1) (X_mem_affine 4)))
  rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm]
  apply DegreeLE.add
  · apply DegreeLE.add
    · exact hqa.mul (degreeLE_one_of_mem_affine hb)
    · apply DegreeLE.smul
      rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, anf_mul_self,
        mul_comm z1 P0]
      exact (((degreeLE_one_of_mem_affine ha).mul p0_degree).add
        ((p0_degree.mono (by omega)).smul w)).add (hp.smul z)
  · apply DegreeLE.smul
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, anf_mul_self]
    exact (((degreeLE_one_of_mem_affine ha).mul degreeLE_two_lowMul3_one).add
      (hp.smul w)).add ((degreeLE_two_lowMul3_one.mono (by omega)).smul z)

theorem q2_degree : DegreeLE 2 q2 := by
  exact (((degreeLE_one_aVar 0).mul (degreeLE_one_bVar 2)).add
    ((degreeLE_one_aVar 1).mul (degreeLE_one_bVar 1))).add
    ((degreeLE_one_aVar 2).mul (degreeLE_one_bVar 0))

theorem z2_eq_q2_add_carry : z2 = q2 + monomial carryMonomial.vars := by
  apply eval_injective 6
  funext x
  change eval z2 x = eval _ x
  rw [eval_lowMul3_two, eval_add', eval_monomial]
  simp [q2, carryMonomial, aVar, bVar, Finset.prod_insert] <;> ring

theorem degree_carry : DegreeLE 4 (monomial carryMonomial.vars : A6) := by
  rintro ⟨m⟩ hm
  rw [coeff_monomial]
  apply if_neg
  intro he
  rw [← he] at hm
  exact (by simpa [carryMonomial_card] using hm : False)

theorem coeff_carry_mul_lin (b : Vec) {i : Fin 6} (hi : i = 2 ∨ i = 5) :
    ((monomial carryMonomial.vars : A6) * linANF b).coeff
      ⟨carryMonomial.vars ∪ {i}⟩ = b i := by
  have hi' : i ∉ carryMonomial.vars := by
    rcases hi with rfl | rfl <;> decide
  simp only [linANF, Finset.mul_sum, mul_smul_comm, X, monomial_mul,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply,
    coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : carryMonomial.vars ∪ {j} ≠ carryMonomial.vars ∪ {i} := by
      intro h
      have hm : i ∈ carryMonomial.vars ∪ {j} := by rw [h]; simp
      exact hji (Finset.mem_singleton.mp ((Finset.mem_union.mp hm).resolve_left hi')).symm
    rw [if_neg hne, mul_zero]
  · simp

/-- The carry obstructs a linear factor with an external coordinate. -/
theorem ordinary_carry_factor {b : Vec} {G : A6} (hG : DegreeLE 3 G)
    (he : (z2 + G) * linANF b = z2 + G) : b 2 = 0 ∧ b 5 = 0 := by
  have hB := degreeLE_one_of_mem_affine (linANF_mem_affine b)
  have hR := (q2_degree.mono (by omega : 2 ≤ 4)).add degree_carry
    |>.add (hG.mono (by omega : 3 ≤ 4))
  have hC : DegreeLE 4 ((monomial carryMonomial.vars : A6) * linANF b) := by
    have hsum : q2 + G + monomial carryMonomial.vars = z2 + G := by
      rw [z2_eq_q2_add_carry, add_right_comm]
    have hprod : DegreeLE 4 ((q2 + G) * linANF b +
        (monomial carryMonomial.vars : A6) * linANF b) := by
      rw [← add_mul, hsum, he]
      simpa only [z2_eq_q2_add_carry] using hR
    have ha := ((q2_degree.mono (by omega : 2 ≤ 3)).add hG).mul hB
    simpa only [add_cancel_left] using ha.add hprod
  have aux (i : Fin 6) (hi : i = 2 ∨ i = 5) : b i = 0 := by
    rw [← coeff_carry_mul_lin b hi]
    apply hC
    rcases hi with rfl | rfl <;> decide
  exact ⟨aux 2 (Or.inl rfl), aux 5 (Or.inr rfl)⟩

theorem ordinary_external_B_zero {l b : Vec} {F : Fin 4 → A6}
    (hF : ∀ i, F i ∈ PlusZ1 (ExtGate 1 l b))
    (ho : F 0 * F 1 + F 2 * F 3 + z2 ∈ PlusZ1 (ExtGate 1 l b)) :
    b 2 = 0 ∧ b 5 = 0 := by
  let c := ExtGate 1 l b
  obtain ⟨a0, ha0, t0, e0⟩ := mem_extend.mp (hF 0)
  obtain ⟨a1, ha1, t1, e1⟩ := mem_extend.mp (hF 1)
  obtain ⟨a2, ha2, t2, e2⟩ := mem_extend.mp (hF 2)
  obtain ⟨a3, ha3, t3, e3⟩ := mem_extend.mp (hF 3)
  obtain ⟨v, hv, s, hs⟩ := mem_extend.mp ho
  change F 0 = a0 + t0 • c at e0
  change F 1 = a1 + t1 • c at e1
  change F 2 = a2 + t2 • c at e2
  change F 3 = a3 + t3 • c at e3
  change _ = v + s • c at hs
  let G := v + (a0 * a1 + a2 * a3)
  let H := t1 • a0 + t0 • a1 + t3 • a2 + t2 • a3 + (s + t0*t1 + t2*t3) • c
  have hG : DegreeLE 3 G := (hv.1.mono (by omega)).add
    ((degree_s0_mul ha0 ha1).add (degree_s0_mul ha2 ha3))
  have he : z2 + G = c * H := by
    apply eval_injective 6
    funext x
    have hx := congrArg (fun p : A6 => eval p x) hs
    rw [e0, e1, e2, e3] at hx
    simp only [eval_add', eval_mul', eval_smul'] at hx
    simp only [G, H, eval_add', eval_mul', eval_smul']
    have hc : eval c x * eval c x = eval c x := f2_mul_self _
    linear_combination (norm := (ring_nf <;> simp [two_f2])) hx - s * hc
  apply ordinary_carry_factor hG
  rw [he, mul_assoc]
  have hc : c * linANF b = c := by
    change ExtGate 1 l b * linANF b = ExtGate 1 l b
    rw [extGate_one, mul_assoc, anf_mul_self]
  rw [mul_comm H (linANF b), ← mul_assoc, hc]

def extDir (a b : F₂) : Vec := ![0, 0, a, 0, 0, b]
def coreVec (x : Vec) : Vec := ![x 0, x 1, 0, x 3, x 4, 0]

theorem dotv_extDir (v : Vec) (a b : F₂) :
    dotv v (extDir a b) = v 2 * a + v 5 * b := by
  simp [dotv, extDir, Fin.sum_univ_succ]

theorem dotv_coreVec (v x : Vec) :
    dotv (coreVec v) x = dotv v (coreVec x) := by
  simp [dotv, coreVec, Fin.sum_univ_succ]

theorem coreVec_eq {x : Vec} (hx2 : x 2 = 0) (hx5 : x 5 = 0) : coreVec x = x := by
  ext i
  fin_cases i <;> simp [coreVec, hx2, hx5]

private theorem choose_external_basis : ∀ x y : F₂, (x ≠ 0 ∨ y ≠ 0) →
    ∃ a b c d : F₂, x*a+y*b = 1 ∧ x*c+y*d = 0 ∧ a*d+b*c = 1 := by
  decide

theorem sliceParity (b : Vec) (j : F₂) (p : A6) (hp : DegreeLE 2 p) :
    betaSlice (Finset.univ.filter fun n : Fin 16 => dotv b (upt n) = j)
      (fun n => eval p (upt n)) (fun _ => 1) = 0 := by
  let I : A6 := (1 + j) • (1 : A6) + linANF b
  have hd : DegreeLE 1 I := degreeLE_one_of_mem_affine ((affine 6).add_mem
    ((affine 6).smul_mem _ (one_mem_affine 6)) (linANF_mem_affine b))
  have h := cp_one_eq_zero_of_deg3 (hp.mul hd)
  have he' : ∀ j k : F₂, 1 + j + k = if k = j then 1 else 0 := by decide
  have he := he' j
  simpa only [betaSlice, Finset.sum_filter, mul_one, cp, one6, eval_mul', I, eval_add',
    eval_smul', eval_one', eval_linANF, he, mul_ite, mul_zero] using h

theorem wedge_ne_p0_of_off {b : Vec} (hb : OffLowSpan b) (m : Vec) :
    wedge b m ≠ P0form := by
  intro he
  obtain ⟨i, h0, h3, hi⟩ := hb
  have h := iota_P0_gen (unitVec i)
    (by simp [unitVec, Ne.symm h0]) (by simp [unitVec, Ne.symm h3])
  rw [← he, iota_wedge, dotv_unitVec, dotv_unitVec, hi, one_smul] at h
  have hm : m = m i • b := by
    have h' := congrArg (fun v : Vec => v + m i • b) h
    simpa only [add_assoc, vec_add_self, add_zero, zero_add] using h'
  have hz : wedge b m = 0 := by
    calc
      _ = wedge b (m i • b) := congrArg (wedge b) hm
      _ = 0 := by rw [wedge_smul_right, wedge_self, smul_zero]
  rw [he] at hz
  have h01 := congrFun (congrFun hz (0 : Fin 6)) (3 : Fin 6)
  simp [P0form, wedge, unitVec] at h01

theorem slice_quad_independent {b : Vec} (hb : OffLowSpan b) (j w z : F₂)
    {a : A6} (ha : a ∈ affine 6)
    (h : ∀ x : Vec, j + dotv b x = 0 → eval (a + w • P0 + z • z1) x = 0) :
    w = 0 ∧ z = 0 := by
  have hb' : b ≠ 0 := by
    obtain ⟨i, _, _, hi⟩ := hb
    intro he
    simpa [he] using hi
  have hdeg : DegreeLE 2 (a + w • P0 + z • z1) :=
    (((degreeLE_one_of_mem_affine ha).mono (by omega)).add (p0_degree.smul w)).add
      (degreeLE_two_lowMul3_one.smul z)
  obtain ⟨m, hm⟩ := pi2_wedge_of_vanish hdeg hb' h
  rw [map_add, map_add, map_smul, map_smul, pi2_eq_zero_of_mem_affine ha, zero_add,
    pi2_a0b0, pi2_lowMul3_one] at hm
  rcases f2_eq_zero_or_one z with hz | hz
  · rcases f2_eq_zero_or_one w with hw | hw
    · exact ⟨hw, hz⟩
    · rw [hz, hw, zero_smul, one_smul, add_zero] at hm
      exact (wedge_ne_p0_of_off hb m hm.symm).elim
  · rw [hz, one_smul, add_comm] at hm
    exact (wedge_ne_Z b m w hm.symm).elim

def swapRow (x : Row4) : Row4 := ![x 1, x 0, x 3, x 2]

theorem symp4_swap (u v : Row4) : symp4 (swapRow u) (swapRow v) = symp4 u v := by
  simp [symp4, swapRow, add_comm, add_left_comm, add_assoc]

theorem row4_add (a x y : Row4) : row4 a (x + y) = row4 a x + row4 a y := by
  simp only [row4, Pi.add_apply]
  ring

theorem row4_smul (a x : Row4) (k : F₂) : row4 a (k • x) = k * row4 a x := by
  simp only [row4, Pi.smul_apply, smul_eq_mul]
  ring

theorem row4_swap (a x : Row4) : row4 (swapRow a) x = symp4 a x := by
  simp [row4, swapRow, symp4] <;> ring

theorem row4_lin_left (a b x : Row4) (u v : F₂) :
    row4 (u • a + v • b) x = u * row4 a x + v * row4 b x := by
  simp only [row4, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem row4_zero_left (x : Row4) : row4 0 x = 0 := by simp [row4]

def linRow (r : Row4) (p : Fin 4 → A6) : A6 :=
  r 0 • p 0 + r 1 • p 1 + r 2 • p 2 + r 3 • p 3

theorem eval_linRow (r : Row4) (p : Fin 4 → A6) (x : Vec) :
    eval (linRow r p) x = row4 r (fun i => eval (p i) x) := by
  simp [linRow, row4]

theorem linRow_affine {p : Fin 4 → A6} (r : Row4) (hp : ∀ i, p i ∈ affine 6) :
    linRow r p ∈ affine 6 :=
  (affine 6).add_mem
    ((affine 6).add_mem
      ((affine 6).add_mem ((affine 6).smul_mem _ (hp 0)) ((affine 6).smul_mem _ (hp 1)))
      ((affine 6).smul_mem _ (hp 2)))
    ((affine 6).smul_mem _ (hp 3))

theorem eval_quad_formula (a : A6) (w z : F₂) (x : Vec) :
    eval (a + w • P0 + z • z1) x =
      eval a x + w * (x 0 * x 3) + z * (x 0 * x 4 + x 1 * x 3) := by
  rw [eval_add', eval_add', eval_smul', eval_smul', eval_p0, eval_lowMul3_one]

theorem linRow_quad (r w z : Row4) (a : Fin 4 → A6) (x : Vec) :
    row4 r (fun i => eval (a i + w i • P0 + z i • z1) x) =
      eval (linRow r a + row4 r w • P0 + row4 r z • z1) x := by
  simp only [eval_quad_formula, eval_linRow, row4]
  ring

theorem sliceRow_coefficients {b : Vec} (hb : OffLowSpan b) (j : F₂)
    (r w z : Row4) (a : Fin 4 → A6) (ha : ∀ i, a i ∈ affine 6)
    {f : A6} (hf : f ∈ affine 6)
    (he : ∀ x : Vec, dotv b x = j →
      row4 r (fun i => eval (a i + w i • P0 + z i • z1) x) = eval f x) :
    row4 r w = 0 ∧ row4 r z = 0 := by
  refine slice_quad_independent hb j (row4 r w) (row4 r z)
    ((affine 6).add_mem (linRow_affine r ha) hf) ?_
  intro x hx
  have h := he x (f2_eq_of_add_eq_zero hx).symm
  rw [linRow_quad] at h
  simp only [eval_add', eval_smul'] at h ⊢
  linear_combination (norm := (ring_nf <;> simp [two_f2])) h

theorem degree_lowMul {p : A6} (hp : p ∈ V4 Q0) {a b : F₂} :
    DegreeLE 2 (p * linANF (a • unitVec 0 + b • unitVec 3)) := by
  rw [v4_q0] at hp
  obtain ⟨r, hr, t, rfl⟩ := mem_extend.mp hp
  let d := a • unitVec 0 + b • unitVec 3
  have hd : ¬ OffLowSpan d := by
    rintro ⟨i, h0, h3, hi⟩
    simp [d, unitVec, h0, h3] at hi
  change DegreeLE 2 ((r + t • P0) * linANF d)
  rw [add_mul, smul_mul_assoc, low_mul_linear hd]
  exact ((degreeLE_one_of_mem_affine hr).mul (degreeLE_one_of_mem_affine (linANF_mem_affine d))).add
    ((p0_degree.smul _).smul _)

theorem betaSlice_low_rad {b : Vec} (j : F₂) {p : A6} (hp : p ∈ V4 Q0)
    (a c : F₂) :
    betaSlice (Finset.univ.filter fun n : Fin 16 => dotv b (upt n) = j)
      (fun n => eval p (upt n)) (fun n => eval (linANF (a • unitVec 0 + c • unitVec 3)) (upt n)) = 0 := by
  simpa only [betaSlice, eval_mul', mul_one] using
    sliceParity b j _ (degree_lowMul hp (a := a) (b := c))

theorem extDir_basis_rows (a b c d u v : F₂) (h : a*d+b*c = 1)
    (h0 : u*b+v*d = 0) (h3 : u*a+v*c = 0) : u = 0 ∧ v = 0 := by
  revert a b c d u v
  decide

theorem row_independent_of_slice {B : Vec} (hB : OffLowSpan B) {j : F₂}
    {u v : Row4} {x : Fin 4 → A6} {a b c d κ mu : F₂} (hdet : a*d+b*c = 1)
    (hu : ∀ p : Vec, dotv B p = j → row4 u (fun i => eval (x i) p) = b*p 0+a*p 3+κ)
    (hv : ∀ p : Vec, dotv B p = j → row4 v (fun i => eval (x i) p) = d*p 0+c*p 3+mu) :
    ∀ α β : F₂, α • u + β • v = 0 → α = 0 ∧ β = 0 := by
  intro α β he
  let w : Vec := (α*b+β*d) • unitVec 0 + (α*a+β*c) • unitVec 3
  have hn : B ≠ 0 := by
    obtain ⟨i, _, _, hi⟩ := hB
    intro h
    simpa [h] using hi
  have hw : w = 0 ∨ w = B := by
    apply affine_vanish (ℓ := B) (c := j) (α := α*κ+β*mu) hn
    intro p hp
    have hp' := (f2_eq_of_add_eq_zero hp).symm
    have he' := row4_lin_left u v (fun i => eval (x i) p) α β
    rw [he, row4_zero_left, hu p hp', hv p hp'] at he'
    simp only [w, dotv_add_left, dotv_smul_left, dotv_unit_left]
    linear_combination -he'
  have hz (i : Fin 6) (h0 : i ≠ 0) (h3 : i ≠ 3) : w i = 0 := by
    simp [w, unitVec, h0, h3]
  have hw' : w = 0 := by
    rcases hw with h | h
    · exact h
    · obtain ⟨i, h0, h3, hi⟩ := hB
      have he := hz i h0 h3
      rw [h, hi] at he
      exact (one_ne_zero he).elim
  have h0 := congrFun hw' (0 : Fin 6)
  have h3 := congrFun hw' (3 : Fin 6)
  exact extDir_basis_rows a b c d α β hdet
    (by simpa [w, unitVec] using h0) (by simpa [w, unitVec] using h3)

def pairProd (x : Row4) : F₂ := x 0 * x 1 + x 2 * x 3

theorem external_rows (X P Q : Row4) (Z C S R κ mu : F₂)
    (h : ∀ s t : F₂, pairProd (X + s • P + t • Q) + (Z + s*S + t*R) +
      (C + s*κ + t*mu) = 0) :
    row4 (swapRow P) X = S + κ + pairProd P ∧
      row4 (swapRow Q) X = R + mu + pairProd Q ∧ symp4 P Q = 0 := by
  have h00 := h 0 0
  have h10 := h 1 0
  have h01 := h 0 1
  have h11 := h 1 1
  simp only [zero_smul, one_smul, zero_mul, one_mul, add_zero] at h00 h10 h01 h11
  simp [row4, swapRow, pairProd, symp4, Pi.add_apply] at h00 h10 h01 h11 ⊢
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := (ring_nf <;> simp [two_f2])) h10 - h00
  · linear_combination (norm := (ring_nf <;> simp [two_f2])) h01 - h00
  · linear_combination h11 - h10 - h01 + h00

structure PlusForm where
  low : LowForm
  z : F₂
  t : F₂

def PlusForm.affAt (r : PlusForm) (l : Vec) (j : F₂) : A6 :=
  r.low.constant • (1 : A6) + linANF (coreVec r.low.slope) +
    (j*r.t) • linANF (coreVec l)

def PlusForm.yAt (r : PlusForm) (l : Vec) (j : F₂) : A6 :=
  r.affAt l j + (r.low.quadratic + j*r.t) • P0

def PlusForm.xAt (r : PlusForm) (l : Vec) (j : F₂) : A6 := r.yAt l j + r.z • z1

def PlusForm.ext (r : PlusForm) (e : Vec) (v : F₂) : F₂ := dotv r.low.slope e + v*r.t

theorem plusForm_exists {c p : A6} (h : p ∈ PlusZ1 c) :
    ∃ f : PlusForm, ∀ x, eval p x = f.low.value x + f.z * eval z1 x + f.t * eval c x := by
  obtain ⟨a, ha, t, rfl⟩ := mem_extend.mp h
  rw [v4_s0] at ha
  obtain ⟨u, hu, z, rfl⟩ := mem_extend.mp ha
  obtain ⟨f, hf⟩ := lowForm_of_mem hu
  exact ⟨⟨f, z, t⟩, fun x => by simp only [eval_add', eval_smul', hf]⟩

theorem plusForm_aff_mem (r : PlusForm) (l : Vec) (j : F₂) : r.affAt l j ∈ affine 6 :=
  (affine 6).add_mem ((affine 6).add_mem
    ((affine 6).smul_mem _ (one_mem_affine 6)) (linANF_mem_affine _))
      ((affine 6).smul_mem _ (linANF_mem_affine _))

theorem plusForm_y_mem (r : PlusForm) (l : Vec) (j : F₂) : r.yAt l j ∈ V4 Q0 := by
  rw [v4_q0]
  exact mem_extend.mpr ⟨r.affAt l j, plusForm_aff_mem r l j, _, rfl⟩

theorem extPoint_eval {l B : Vec} {p : A6} {f : PlusForm}
    (hf : ∀ x, eval p x = f.low.value x + f.z * eval z1 x +
      f.t * eval (ExtGate 1 l B) x)
    {a b c d : F₂} (hP : dotv l (extDir a b) = 1) (hQ : dotv l (extDir c d) = 0)
    (hB2 : B 2 = 0) (hB5 : B 5 = 0) {x : Vec} {j : F₂}
    (hx : dotv B (coreVec x) = j) (s t : F₂) :
    eval p (coreVec x + s • extDir a b + t • extDir c d) =
      eval (f.xAt l j) x + s * f.ext (extDir a b) j + t * f.ext (extDir c d) 0 := by
  rw [hf, eval_extGate_one, eval_lowMul3_one]
  have hBP : dotv B (extDir a b) = 0 := by simp [dotv_extDir, hB2, hB5]
  have hBQ : dotv B (extDir c d) = 0 := by simp [dotv_extDir, hB2, hB5]
  simp only [PlusForm.xAt, PlusForm.yAt, PlusForm.affAt, PlusForm.ext, LowForm.value,
    eval_add', eval_smul', eval_one', eval_linANF, dotv_coreVec, dotv_add_right, dotv_smul_right,
    eval_p0, eval_lowMul3_one, hP, hQ, hBP, hBQ, hx]
  simp [coreVec, extDir, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem extPoint_z2 (a b c d : F₂) (x : Vec) (s t : F₂) :
    eval z2 (coreVec x + s • extDir a b + t • extDir c d) =
      eval z2 (coreVec x) + s * (b * x 0 + a * x 3) + t * (d * x 0 + c * x 3) := by
  simp [eval_lowMul3_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coreVec, extDir] <;> ring

theorem dotv_core_of_core {B : Vec} (h2 : B 2 = 0) (h5 : B 5 = 0) (x : Vec) :
    dotv B (coreVec x) = dotv B x := by
  simp [dotv, coreVec, Fin.sum_univ_succ, h2, h5]

theorem eval_low_lin (a b : F₂) (x : Vec) :
    eval (linANF (a • unitVec 0 + b • unitVec 3)) x = a*x 0+b*x 3 := by
  rw [eval_linANF, dotv_add_left, dotv_smul_left, dotv_smul_left, dotv_unit_left, dotv_unit_left]

def SliceCertificate (B l : Vec) (f : Fin 4 → PlusForm) (j : F₂) : Prop :=
  symp4 (fun i => (f i).low.quadratic + j*(f i).t) (fun i => (f i).z) = 0 ∧
    betaSlice (Finset.univ.filter fun n : Fin 16 => dotv B (upt n) = j)
      (fun n => eval ((f 0).yAt l j) (upt n)) (fun n => eval ((f 1).yAt l j) (upt n)) +
    betaSlice (Finset.univ.filter fun n : Fin 16 => dotv B (upt n) = j)
      (fun n => eval ((f 2).yAt l j) (upt n)) (fun n => eval ((f 3).yAt l j) (upt n)) = 0

theorem slice_gram_zero {B l : Vec} (hB : OffLowSpan B) (f : Fin 4 → PlusForm) (j : F₂)
    {a b c d κ mu : F₂} (hdet : a*d+b*c = 1) (u v : Row4) (hiso : symp4 u v = 0)
    (hu : ∀ x : Vec, dotv B x = j →
      row4 u (fun i => eval ((f i).xAt l j) x) = b*x 0+a*x 3+κ)
    (hv : ∀ x : Vec, dotv B x = j →
      row4 v (fun i => eval ((f i).xAt l j) x) = d*x 0+c*x 3+mu) :
    SliceCertificate B l f j := by
  let w : Row4 := fun i => (f i).low.quadratic + j*(f i).t
  let z : Row4 := fun i => (f i).z
  let S : A6 := linANF (b • unitVec 0 + a • unitVec 3)
  let R : A6 := linANF (d • unitVec 0 + c • unitVec 3)
  have hs := linANF_mem_affine (b • unitVec 0 + a • unitVec 3)
  have hr := linANF_mem_affine (d • unitVec 0 + c • unitVec 3)
  have hu' : row4 u w = 0 ∧ row4 u z = 0 := by
    refine sliceRow_coefficients hB j u w z (fun i => (f i).affAt l j)
      (fun i => plusForm_aff_mem _ _ _) ((affine 6).add_mem hs
        ((affine 6).smul_mem κ (one_mem_affine 6))) ?_
    intro x hx
    simpa only [eval_add', eval_smul', eval_one', mul_one, eval_low_lin, PlusForm.xAt, PlusForm.yAt, w, z] using hu x hx
  have hv' : row4 v w = 0 ∧ row4 v z = 0 := by
    refine sliceRow_coefficients hB j v w z (fun i => (f i).affAt l j)
      (fun i => plusForm_aff_mem _ _ _) ((affine 6).add_mem hr
        ((affine 6).smul_mem mu (one_mem_affine 6))) ?_
    intro x hx
    simpa only [eval_add', eval_smul', eval_one', mul_one, eval_low_lin, PlusForm.xAt, PlusForm.yAt, w, z] using hv x hx
  have hI := row_independent_of_slice hB hdet hu hv
  refine ⟨kernel_symp4 hI hiso hu'.1 hv'.1 hu'.2 hv'.2, ?_⟩
  let pts := Finset.univ.filter fun n : Fin 16 => dotv B (upt n) = j
  let Y (i : Fin 4) (n : Fin 16) := eval ((f i).yAt l j) (upt n)
  refine slice_product_parity (pts := pts) (Y := Y)
    (r := fun n => eval R (upt n)) (s := fun n => eval S (upt n)) (a := κ) (b := mu) hI hiso ?_ ?_ ?_
  · intro n hn
    have h := hu (upt n) (Finset.mem_filter.mp hn).2
    have he : (fun i => eval ((f i).xAt l j) (upt n)) =
        (fun i => Y i n) + eval z1 (upt n) • z := by
      funext i
      simp [PlusForm.xAt, Y, z, mul_comm]
    rw [he, row4_add, row4_smul, hu'.2, mul_zero, add_zero] at h
    simpa only [S, eval_low_lin] using h
  · intro n hn
    have h := hv (upt n) (Finset.mem_filter.mp hn).2
    have he : (fun i => eval ((f i).xAt l j) (upt n)) =
        (fun i => Y i n) + eval z1 (upt n) • z := by
      funext i
      simp [PlusForm.xAt, Y, z, mul_comm]
    rw [he, row4_add, row4_smul, hv'.2, mul_zero, add_zero] at h
    simpa only [R, eval_low_lin] using h
  · intro i
    exact ⟨sliceParity B j _ (plusForm_y_mem (f i) l j).1,
      betaSlice_low_rad j (plusForm_y_mem (f i) l j) d c,
      betaSlice_low_rad j (plusForm_y_mem (f i) l j) b a⟩

private theorem symp4_add_right (z u v : Row4) : symp4 z (u + v) = symp4 z u + symp4 z v := by
  simp only [symp4, Pi.add_apply]
  ring

private theorem symp4_smul_right (z w : Row4) (a : F₂) : symp4 z (a • w) = a * symp4 z w := by
  simp only [symp4, Pi.smul_apply, smul_eq_mul]
  ring

private theorem pairProd_add_scaled (Y z : Row4) (s : F₂) :
    pairProd (Y + s • z) = pairProd Y + s * (symp4 z Y + pairProd z) := by
  simp only [pairProd, symp4, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (z 0 * z 1 + z 2 * z 3) * f2_mul_self s

set_option maxHeartbeats 2500000 in
theorem two_slices_cancel {B l : Vec} {F : Fin 4 → A6} {f : Fin 4 → PlusForm}
    (hslice : ∀ j : F₂, SliceCertificate B l f j)
    (hEval : ∀ j n, dotv B (upt n) = j →
      ∀ i, eval (F i) (upt n) = eval ((f i).xAt l j) (upt n)) :
    (∑ n : Fin 16, pairProd (fun i => eval (F i) (upt n))) = 0 := by
  let z : Row4 := fun i => (f i).z
  let w : Row4 := fun i => (f i).low.quadratic
  let T : Row4 := fun i => (f i).t
  have hw : symp4 z w = 0 := by
    have h := (hslice 0).1
    simp only [zero_mul, add_zero] at h
    simpa only [symp4, z, w, mul_comm, add_comm, add_left_comm, add_assoc] using h
  have ht : symp4 z T = 0 := by
    have h := (hslice 1).1
    change symp4 (fun i => w i + 1 * T i) z = 0 at h
    simp only [one_mul, symp4] at hw h ⊢
    linear_combination (norm := (ring_nf <;> simp [two_f2])) h - hw
  let A (i : Fin 4) : A6 := (f i).low.constant • (1 : A6) + linANF (coreVec (f i).low.slope)
  let D : A6 := linRow (swapRow z) A + pairProd z • (1 : A6)
  have hD : D ∈ affine 6 := (affine 6).add_mem (linRow_affine (swapRow z) fun i =>
    (affine 6).add_mem ((affine 6).smul_mem _ (one_mem_affine 6)) (linANF_mem_affine _))
      ((affine 6).smul_mem _ (one_mem_affine 6))
  have hpoint (j : F₂) (n : Fin 16) (hn : dotv B (upt n) = j) :
      pairProd (fun i => eval (F i) (upt n)) =
        pairProd (fun i => eval ((f i).yAt l j) (upt n)) + eval (z1 * D) (upt n) := by
    let Y : Row4 := fun i => eval ((f i).yAt l j) (upt n)
    let E := eval P0 (upt n)
    let L := eval (linANF (coreVec l)) (upt n)
    have hx : (fun i => eval (F i) (upt n)) = Y + eval z1 (upt n) • z := by
      funext i
      rw [hEval j n hn i]
      simp [PlusForm.xAt, Y, z, mul_comm]
    have hy : Y = (fun i => eval (A i) (upt n)) + E • w + (j * (E + L)) • T := by
      funext i
      simp only [Y, A, E, L, w, T, PlusForm.yAt, PlusForm.affAt, eval_add',
        eval_smul', eval_one', mul_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hd : symp4 z Y + pairProd z = eval D (upt n) := by
      rw [hy, symp4_add_right, symp4_add_right, symp4_smul_right,
        symp4_smul_right, hw, ht, mul_zero, mul_zero, add_zero, add_zero]
      simp only [D, eval_add', eval_smul', eval_linRow, eval_one', mul_one, row4_swap]
    rw [hx, pairProd_add_scaled, hd, eval_mul' z1 D]
  have hsum (j : F₂) :
      ∑ n ∈ Finset.univ.filter (fun n : Fin 16 => dotv B (upt n) = j),
        pairProd (fun i => eval (F i) (upt n)) =
      ∑ n ∈ Finset.univ.filter (fun n : Fin 16 => dotv B (upt n) = j),
        eval (z1 * D) (upt n) := by
    rw [Finset.sum_congr rfl (fun n hn => hpoint j n (Finset.mem_filter.mp hn).2),
      Finset.sum_add_distrib]
    have he : (∑ n ∈ Finset.univ.filter (fun n : Fin 16 => dotv B (upt n) = j),
        pairProd (fun i => eval ((f i).yAt l j) (upt n))) = 0 := by
      simpa only [betaSlice, pairProd, Finset.sum_add_distrib] using (hslice j).2
    rw [he, zero_add]
  have total (g : Fin 16 → F₂) :
      (∑ n ∈ Finset.univ.filter (fun n : Fin 16 => dotv B (upt n) = 0), g n) +
      (∑ n ∈ Finset.univ.filter (fun n : Fin 16 => dotv B (upt n) = 1), g n) = ∑ n, g n := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases f2_eq_zero_or_one (dotv B (upt n)) with h | h <;> simp [h]
  rw [← total _, hsum 0, hsum 1, total]
  simpa only [cp, one6, mul_one] using
    cp_one_eq_zero_of_deg3 (degreeLE_two_lowMul3_one.mul (degreeLE_one_of_mem_affine hD))

set_option maxHeartbeats 1500000 in
theorem ordinary_pair_noPlace {l B : Vec} (hb : OffLowSpan B)
    {F : Fin 4 → A6} (hF : ∀ i, F i ∈ PlusZ1 (ExtGate 1 l B)) :
    F 0 * F 1 + F 2 * F 3 + z2 ∉ PlusZ1 (ExtGate 1 l B) := by
  intro ho
  by_cases hcore : CoreHi (ExtGate 1 l B)
  · have hn := core_noNextZ2 hcore (hF 0) (hF 1)
    exact hn.2 (F 2) (F 3) (Submodule.mem_sup_left (hF 2)) (Submodule.mem_sup_left (hF 3))
      (mem_extend.mpr ⟨F 0 * F 1 + F 2 * F 3 + z2, ho, 1, by
        rw [one_smul]
        symm
        calc
          _ = (F 2 * F 3 + z2) + (F 0 * F 1 + F 0 * F 1) := by ac_rfl
          _ = _ := by rw [anf_add_self, add_zero]⟩)
  obtain ⟨hB2, hB5⟩ := ordinary_external_B_zero hF ho
  have hL : l 2 ≠ 0 ∨ l 5 ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hcore (coreHi_extGate_of_core hn.1 hn.2 hB2 hB5)
  obtain ⟨a,b,c,d,hP,hQ,hdet⟩ := choose_external_basis (l 2) (l 5) hL
  have hP' : dotv l (extDir a b) = 1 := by rwa [dotv_extDir]
  have hQ' : dotv l (extDir c d) = 0 := by rwa [dotv_extDir]
  choose f hf using fun i => plusForm_exists (hF i)
  let C := F 0 * F 1 + F 2 * F 3 + z2
  obtain ⟨g,hg⟩ := plusForm_exists ho
  let P (j : F₂) : Row4 := fun i => (f i).ext (extDir a b) j
  let Q : Row4 := fun i => (f i).ext (extDir c d) 0
  let Xv (j : F₂) (x : Vec) : Row4 := fun i => eval ((f i).xAt l j) x
  have hr (j : F₂) (x : Vec) (hx : dotv B x = j) :
      row4 (swapRow (P j)) (Xv j x) =
        b*x 0+a*x 3+(g.ext (extDir a b) j + pairProd (P j)) ∧
      row4 (swapRow Q) (Xv j x) =
        d*x 0+c*x 3+(g.ext (extDir c d) 0 + pairProd Q) ∧
      symp4 (P j) Q = 0 := by
    have hx' : dotv B (coreVec x) = j := by rwa [dotv_core_of_core hB2 hB5]
    have he (s t : F₂) :
        pairProd (Xv j x + s • P j + t • Q) +
          (eval z2 (coreVec x) + s*(b*x 0+a*x 3) + t*(d*x 0+c*x 3)) +
          (eval (g.xAt l j) x + s*g.ext (extDir a b) j + t*g.ext (extDir c d) 0) = 0 := by
      let y := coreVec x + s • extDir a b + t • extDir c d
      have hh := extPoint_eval (x := x) (j := j) hg hP' hQ' hB2 hB5 hx' s t
      have hf' (i : Fin 4) := extPoint_eval (x := x) (j := j) (hf i) hP' hQ' hB2 hB5 hx' s t
      change eval (F 0 * F 1 + F 2 * F 3 + z2) y = _ at hh
      simp only [eval_add', eval_mul', y, hf', extPoint_z2] at hh
      simp only [pairProd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Xv, P, Q]
      rw [hh, CharTwo.add_self_eq_zero]
    obtain ⟨hp,hq,hi⟩ := external_rows _ _ _ _ _ _ _ _ _ he
    exact ⟨by simpa only [add_assoc] using hp, by simpa only [add_assoc] using hq, hi⟩
  have hex (j : F₂) : ∃ x : Vec, dotv B x = j := by
    obtain ⟨i, _, _, hi⟩ := hb
    exact ⟨j • unitVec i, by rw [dotv_smul_right, dotv_unitVec, hi, mul_one]⟩
  have hslice (j : F₂) : SliceCertificate B l f j := slice_gram_zero hb f j hdet
    (swapRow (P j)) (swapRow Q)
    (by rw [symp4_swap]; obtain ⟨x,hx⟩ := hex j; exact (hr j x hx).2.2)
    (fun x hx => (hr j x hx).1) (fun x hx => (hr j x hx).2.1)
  have hFzero := two_slices_cancel (B := B) (l := l) (F := F) (f := f) hslice (by
    intro j n hn i
    have hc : coreVec (upt n) = upt n := coreVec_eq rfl rfl
    rw [hf i, eval_extGate_one, hn]
    simp only [PlusForm.xAt, PlusForm.yAt, PlusForm.affAt, LowForm.value, eval_add',
      eval_smul', eval_one', mul_one, eval_linANF, dotv_coreVec, hc, eval_p0]
    ring)
  have hCdeg : DegreeLE 3 C := by
    obtain ⟨v,hv,t,he⟩ := mem_extend.mp ho
    change C = _ at he
    rw [he]
    exact (hv.1.mono (by omega)).add ((first_degree l B).smul t)
  have hC := cp_one_eq_zero_of_deg3 hCdeg
  simp only [cp, one6, mul_one, C, eval_add', eval_mul', Finset.sum_add_distrib] at hC
  have hZ : (∑ n : Fin 16, eval z2 (upt n)) = 1 := by simpa [cp, one6] using cp_z2
  simp only [pairProd, Finset.sum_add_distrib] at hFzero
  rw [hFzero, hZ, zero_add] at hC
  exact one_ne_zero hC

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
