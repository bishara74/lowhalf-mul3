module

public import LowHalfMul3.LambdaThree

@[expose] public section

namespace UnrestrictedBooleanMul.LowHalfMul3.LambdaOne

noncomputable section

open scoped BigOperators

abbrev Vec := Fin 6 → F₂
abbrev A6 := ANF 6

abbrev P0 : A6 := aVar 3 0 * bVar 3 0
abbrev z1 : A6 := lowMul3 1
abbrev z2 : A6 := lowMul3 2
abbrev singleton (p : A6) : Submodule F₂ A6 := Submodule.span F₂ {p}
local notation "⟪" p "⟫" => singleton p

def Q0 : Submodule F₂ TwoForm6 := Submodule.span F₂ {P0form}
def S0 : Submodule F₂ TwoForm6 := Q0 ⊔ Submodule.span F₂ {Z1form}
abbrev Qlr (l r : Vec) : Submodule F₂ TwoForm6 := Q3span l r 0 0
abbrev Slr (l r : Vec) : Submodule F₂ TwoForm6 := Qlr l r ⊔ Submodule.span F₂ {Z1form}
def Base (c : A6) : Submodule F₂ A6 := V4 Q0 ⊔ ⟪c⟫
def PlusZ1 (c : A6) : Submodule F₂ A6 := V4 S0 ⊔ ⟪c⟫
def ExtGate (d : F₂) (l b : Vec) : A6 := (d • P0 + linANF l) * linANF b

def CoreHi (c : A6) : Prop :=
  ∀ m : Monomial 6, 2 ≤ m.vars.card →
    ((2 : Fin 6) ∈ m.vars ∨ (5 : Fin 6) ∈ m.vars) → c.coeff m = 0

def OffLowSpan (b : Vec) : Prop :=
  ∃ i : Fin 6, i ≠ 0 ∧ i ≠ 3 ∧ b i = 1

def q2 : A6 := aVar 3 0 * bVar 3 2 + aVar 3 1 * bVar 3 1 + aVar 3 2 * bVar 3 0
def InLowIdeal (p : A6) : Prop := P0 * p = p
def ModLow (p q : A6) : Prop := InLowIdeal (p + q)

def NoNextZ2 (W : Submodule F₂ A6) : Prop :=
  (z2 ∉ W) ∧ ∀ F H : A6, F ∈ W → H ∈ W → F * H + z2 ∉ W

/-- Interface to the shared last-factor theorem. -/
def LastFactorLowIdeal : Prop :=
  ∀ {d : F₂} {l b : Vec}, OffLowSpan b → ¬ CoreHi (ExtGate d l b) →
    ∀ {k R : A6}, k ∈ PlusZ1 (ExtGate d l b) →
      R + z2 ∈ PlusZ1 (ExtGate d l b) → k * R = R → ModLow k 1

def IdealExtract : Prop :=
  ∀ {l r : Vec} {f h R : A6}, f ∈ V4 (Qlr l r) → h ∈ V4 (Qlr l r) →
    DegreeLE 2 R → ModLow (f * h) R →
      ∃ π ∈ Qlr l r, ∃ a b : Vec, pi2 R = π + wedge a b

def Q2NotTwoWedges : Prop :=
  ∀ (ε α : F₂) (l r a b : Vec),
    q2Form + ε • Z1form + α • P0form + wedge l r ≠ wedge a b

def FeedbackNoPlaceModLow : Prop :=
  ∀ {l r : Vec} {f h F v : A6}, f ∈ V4 (Qlr l r) → h ∈ V4 (Qlr l r) →
    F ∈ V4 (Slr l r) → v ∈ V4 (Slr l r) → ModLow (f * h) (q2 + F + v) → False

def FeedbackNormal : Prop :=
  ∀ {A : Submodule F₂ A6}, (1 : A6) ∈ A →
    ∀ {g F H T : A6}, F ∈ A ⊔ ⟪g⟫ → H ∈ A ⊔ ⟪g⟫ → F * H + T ∈ A ⊔ ⟪g⟫ →
      (∃ f h : A6, f ∈ A ∧ h ∈ A ∧ f * h + T ∈ A ⊔ ⟪g⟫) ∨
      (∃ k a : A6, k ∈ A ∧ a ∈ A ∧ k * (g + a) + T ∈ A)

theorem add_cancel_right (p q : A6) : (p + q) + q = p := by
  rw [add_assoc, anf_add_self, add_zero]

theorem add_cancel_left (p q : A6) : p + (p + q) = q := by
  rw [← add_assoc, anf_add_self, zero_add]

theorem mem_extend {W : Submodule F₂ A6} {g p : A6} :
    p ∈ W ⊔ ⟪g⟫ ↔ ∃ a ∈ W, ∃ t : F₂, p = a + t • g := by
  constructor
  · intro h
    obtain ⟨a, ha, v, hv, he⟩ := Submodule.mem_sup.mp h
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨a, ha, t, he.symm⟩
  · rintro ⟨a, ha, t, rfl⟩
    exact Submodule.mem_sup.mpr ⟨a, ha, _, Submodule.smul_mem _ t
      (Submodule.mem_span_singleton_self g), rfl⟩

theorem extend_eq_of_add_mem {W : Submodule F₂ A6} {p q : A6} (h : p + q ∈ W) :
    W ⊔ ⟪p⟫ = W ⊔ ⟪q⟫ := by
  have hp : p ∈ W ⊔ ⟪q⟫ := by
    exact mem_extend.mpr ⟨p+q, h, 1, by rw [one_smul, add_cancel_right]⟩
  have hq : q ∈ W ⊔ ⟪p⟫ := by
    exact mem_extend.mpr ⟨p+q, h, 1, by rw [one_smul, add_comm p q, add_cancel_right]⟩
  exact le_antisymm (sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hp))
    (sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hq))

theorem mem_V4_sup_singleton {Q : Submodule F₂ TwoForm6} {p : A6} (hp : DegreeLE 2 p) :
    V4 (Q ⊔ Submodule.span F₂ {pi2 p}) = V4 Q ⊔ ⟪p⟫ := by
  apply le_antisymm
  · intro v hv
    obtain ⟨q, hq, s, hs, he⟩ := Submodule.mem_sup.mp hv.2
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hs
    refine mem_extend.mpr ⟨v + t • p, ⟨hv.1.add (hp.smul t), ?_⟩, t, ?_⟩
    · rw [map_add, map_smul, ← he, add_assoc, tf_add_self, add_zero]
      exact hq
    · rw [add_cancel_right]
  · exact sup_le (V4_mono le_sup_left) ((Submodule.span_singleton_le_iff_mem _ _).mpr
      ⟨hp, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩)

theorem p0_degree : DegreeLE 2 P0 :=
  (degreeLE_one_aVar 0).mul (degreeLE_one_bVar 0)

theorem v4_q0 : V4 Q0 = affine 6 ⊔ ⟪P0⟫ := by
  rw [Q0, ← pi2_a0b0]
  have hb : (⊥ : Submodule F₂ TwoForm6) ⊔ Submodule.span F₂ {pi2 P0} =
      Submodule.span F₂ {pi2 P0} := by simp
  rw [← hb, mem_V4_sup_singleton p0_degree]
  congr 1
  exact le_antisymm (fun p hp => mem_affine_of_degreeLE_two_of_pi2_eq_zero p hp.1 (by simpa using hp.2))
    (fun p hp => ⟨(degreeLE_one_of_mem_affine hp).mono (by omega), by simpa using pi2_eq_zero_of_mem_affine hp⟩)

theorem v4_s0 : V4 S0 = V4 Q0 ⊔ ⟪z1⟫ := by
  rw [S0, ← pi2_lowMul3_one, mem_V4_sup_singleton degreeLE_two_lowMul3_one]

theorem plusZ1_eq (c : A6) : PlusZ1 c = Base c ⊔ ⟪z1⟫ := by
  rw [PlusZ1, Base, v4_s0, sup_right_comm]

theorem wireSpace_one_eq (D : Circuit 6 5) (h0 : D.gate 0 = P0) :
    wireSpace D.gate 1 = V4 Q0 := by
  show wireSpace D.gate (0 + 1) = _
  rw [N4.wireSpace_succ D.gate (by decide), N4.wireSpace_zero]
  change affine 6 ⊔ ⟪D.gate 0⟫ = V4 Q0
  rw [h0, v4_q0]

theorem qlr_eq (l b : Vec) :
    Qlr l b = Q0 ⊔ Submodule.span F₂ {wedge l b} := by
  apply le_antisymm
  · change Submodule.span F₂ (Set.range ![P0form, wedge l b, wedge 0 0]) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · change wedge 0 0 ∈ Q0 ⊔ Submodule.span F₂ {wedge l b}
      rw [wedge_zero_right]
      exact (Q0 ⊔ Submodule.span F₂ {wedge l b}).zero_mem
  · apply sup_le <;> apply Submodule.span_le.mpr
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      exact Submodule.subset_span ⟨0, rfl⟩
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      exact Submodule.subset_span ⟨1, rfl⟩

theorem extGate_zero (l b : Vec) : ExtGate 0 l b = linANF l * linANF b := by
  simp [ExtGate]

theorem extGate_one (l b : Vec) : ExtGate 1 l b = (P0 + linANF l) * linANF b := by
  simp [ExtGate]

theorem quadratic_space_eq (l b : Vec) :
    Base (ExtGate 0 l b) = V4 (Qlr l b) ∧
      PlusZ1 (ExtGate 0 l b) = V4 (Slr l b) := by
  have hL := linANF_mem_affine l
  have hB := linANF_mem_affine b
  have hd := (degreeLE_one_of_mem_affine hL).mul (degreeLE_one_of_mem_affine hB)
  have hπ := pi2_mul_affine hL hB
  have lin_id (v : Vec) : lin (linANF v) = v := by
    ext i
    simp [lin, eval_linANF, dotv_unitVec, dotv_zero_right]
  rw [lin_id, lin_id] at hπ
  constructor
  · rw [Base, extGate_zero, qlr_eq, ← hπ, mem_V4_sup_singleton hd]
  · change PlusZ1 (ExtGate 0 l b) = V4 (Qlr l b ⊔ Submodule.span F₂ {Z1form})
    rw [PlusZ1, extGate_zero, qlr_eq, sup_right_comm, ← S0, ← hπ,
      mem_V4_sup_singleton hd]

theorem affine_repr {p : A6} (hp : p ∈ affine 6) :
    p = eval p 0 • (1 : A6) + linANF (lin p) := by
  apply eval_injective 6
  funext x
  change eval p x = eval _ x
  rw [eval_affine hp x, eval_add', eval_smul', eval_one', mul_one, eval_linANF]

private theorem product_add_constants : ∀ a b u v : F₂,
    (u + a) * (v + b) + u * v = b*u + a*v + a*b := by
  decide

theorem first_normal_form {f h : A6} (hf : f ∈ V4 Q0) (hh : h ∈ V4 Q0)
    (hn : ¬ (f ∈ affine 6 ∧ h ∈ affine 6)) :
    ∃ l b : Vec, f * h + ExtGate 1 l b ∈ V4 Q0 := by
  have step {u v : A6} (hu : u ∈ affine 6) (hv : v ∈ affine 6) :
      (P0 + u) * v + ExtGate 1 (lin u) (lin v) ∈ V4 Q0 := by
    let a := eval u 0
    let b := eval v 0
    let U := P0 + linANF (lin u)
    let V := linANF (lin v)
    have hU : U ∈ V4 Q0 := by
      apply (V4 Q0).add_mem _ (affine_le_V4 Q0 (linANF_mem_affine _))
      refine ⟨p0_degree, ?_⟩
      rw [pi2_a0b0]
      exact Submodule.mem_span_singleton_self _
    have hV := affine_le_V4 Q0 (linANF_mem_affine (lin v))
    have h1 := affine_le_V4 Q0 (one_mem_affine 6)
    have he : (P0 + u) * v + ExtGate 1 (lin u) (lin v) =
        b • U + a • V + (a*b) • (1 : A6) := by
      have hu' : P0 + u = U + a • (1 : A6) := by
        calc
          _ = P0 + (a • (1 : A6) + linANF (lin u)) := congrArg (P0 + ·) (affine_repr hu)
          _ = _ := by simp only [U, add_left_comm, add_comm, add_assoc]
      have hv' : v = V + b • (1 : A6) := (affine_repr hv).trans (add_comm _ _)
      rw [congrArg₂ (· * ·) hu' hv', extGate_one]
      change (U + a • (1 : A6)) * (V + b • (1 : A6)) + U * V = _
      apply eval_injective 6
      funext x
      change eval (_ + _) x = eval (_ + _) x
      simp only [eval_add', eval_mul', eval_smul', eval_one', mul_one]
      exact product_add_constants a b (eval U x) (eval V x)
    rw [he]
    exact (V4 Q0).add_mem ((V4 Q0).add_mem ((V4 Q0).smul_mem b hU)
      ((V4 Q0).smul_mem a hV)) ((V4 Q0).smul_mem (a*b) h1)
  rw [v4_q0] at hf hh
  obtain ⟨u, hu, s, rfl⟩ := mem_extend.mp hf
  obtain ⟨v, hv, t, rfl⟩ := mem_extend.mp hh
  rcases f2_eq_zero_or_one s with rfl | rfl <;>
    rcases f2_eq_zero_or_one t with rfl | rfl
  · exact (hn ⟨by simpa using hu, by simpa using hv⟩).elim
  · exact ⟨lin v, lin u, by simpa [add_comm v P0, mul_comm] using step hv hu⟩
  · exact ⟨lin u, lin v, by simpa [add_comm u P0] using step hu hv⟩
  · refine ⟨lin u, lin (u+v), ?_⟩
    have he : (u + (1 : F₂) • P0) * (v + (1 : F₂) • P0) =
        (P0 + u) * (u + v) + (P0 + u) := by
      have h : u + v = (P0 + u) + (P0 + v) := by
        rw [add_add_add_comm, anf_add_self, zero_add]
      simp only [one_smul]
      rw [add_comm u P0, add_comm v P0, h, mul_add (P0 + u) (P0 + u) (P0 + v), anf_mul_self,
        add_comm (P0 + u) ((P0 + u) * (P0 + v)), add_cancel_right]
    rw [he, add_right_comm]
    exact (V4 Q0).add_mem (step hu ((affine 6).add_mem hu hv))
      ((V4 Q0).add_mem ⟨p0_degree, by rw [pi2_a0b0]; exact Submodule.mem_span_singleton_self _⟩
        (affine_le_V4 Q0 hu))

theorem p0_monomial : P0 = monomial {0, 3} := by
  change (X (0 : Fin 6) * X (3 : Fin 6)) = _
  simp only [X, monomial_mul]
  congr 1

theorem p0_mul_linANF (b : Vec) :
    P0 * linANF b = ∑ i : Fin 6, b i • monomial ({0, 3} ∪ {i}) := by
  simp [linANF, Finset.mul_sum, mul_smul_comm, p0_monomial, X]

theorem first_degree (l b : Vec) : DegreeLE 3 (ExtGate 1 l b) := by
  rw [extGate_one]
  exact (p0_degree.add ((degreeLE_one_of_mem_affine (linANF_mem_affine l)).mono
    (by omega))).mul (degreeLE_one_of_mem_affine (linANF_mem_affine b))

theorem first_cubic_coeff (l b : Vec) {i : Fin 6} (h0 : i ≠ 0) (h3 : i ≠ 3) :
    (ExtGate 1 l b).coeff ⟨{0, 3} ∪ {i}⟩ = b i := by
  have hc : ({0, 3} ∪ {i} : Finset (Fin 6)).card = 3 := by
    fin_cases i <;> simp_all <;> decide
  have hquad := (degreeLE_one_of_mem_affine (linANF_mem_affine l)).mul
    (degreeLE_one_of_mem_affine (linANF_mem_affine b))
  have hz := hquad ⟨{0, 3} ∪ {i}⟩ (by change 2 < ({0, 3} ∪ {i} : Finset (Fin 6)).card; rw [hc]; decide)
  rw [extGate_one, add_mul, p0_mul_linANF]
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
    coeff_monomial, hz, add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : ({0, 3} ∪ {j} : Finset (Fin 6)) ≠ {0, 3} ∪ {i} := by
      intro he
      have hi : i ∈ ({0, 3} ∪ {j} : Finset (Fin 6)) := by rw [he]; simp
      simp [h0, h3, Ne.symm hji] at hi
    rw [if_neg hne, mul_zero]
  · simp

theorem low_mul_linear {b : Vec} (hb : ¬ OffLowSpan b) :
    P0 * linANF b = (b 0 + b 3) • P0 := by
  have hzero (i : Fin 6) (h0 : i ≠ 0) (h3 : i ≠ 3) : b i = 0 := by
    rcases f2_eq_zero_or_one (b i) with h | h
    · exact h
    · exact (hb ⟨i, h0, h3, h⟩).elim
  rw [p0_mul_linANF, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  change b 0 • monomial _ + (b 1 • monomial _ + (b 2 • monomial _ +
    (b 3 • monomial _ + (b 4 • monomial _ + b 5 • monomial _)))) = _
  rw [hzero 1 (by decide) (by decide), hzero 2 (by decide) (by decide),
    hzero 4 (by decide) (by decide), hzero 5 (by decide) (by decide)]
  simp only [zero_smul, add_zero, zero_add, add_smul, p0_monomial]
  have h0 : ({0, 3} ∪ {0} : Finset (Fin 6)) = {0, 3} := by decide
  have h3 : ({0, 3} ∪ {3} : Finset (Fin 6)) = {0, 3} := by decide
  change b 0 • monomial ({0, 3} ∪ {0}) + b 3 • monomial ({0, 3} ∪ {(3 : Fin 6)}) = _
  rw [h0, h3]

theorem first_cubic_iff (l b : Vec) :
    (¬ DegreeLE 2 (ExtGate 1 l b)) ↔ OffLowSpan b := by
  constructor
  · intro hd
    by_contra hb
    apply hd
    rw [extGate_one, add_mul, low_mul_linear hb]
    exact (p0_degree.smul _).add ((degreeLE_one_of_mem_affine (linANF_mem_affine l)).mul
      (degreeLE_one_of_mem_affine (linANF_mem_affine b)))
  · rintro ⟨i, h0, h3, hi⟩ hd
    have hcard : ({0, 3} ∪ {i} : Finset (Fin 6)).card = 3 := by
      fin_cases i <;> simp_all <;> decide
    have hz := hd ⟨{0, 3} ∪ {i}⟩ (by change 2 < ({0, 3} ∪ {i} : Finset (Fin 6)).card; rw [hcard]; decide)
    rw [first_cubic_coeff l b h0 h3, hi] at hz
    exact one_ne_zero hz

theorem quadratic_first_le {c : A6} {l b : Vec}
    (hc : c + ExtGate 1 l b ∈ V4 Q0) (hd : DegreeLE 2 c) :
    Base c ≤ V4 (Qlr l b) := by
  have hdegree : DegreeLE 2 (ExtGate 1 l b) := by
    simpa only [add_cancel_left] using hd.add hc.1
  have hb : ¬ OffLowSpan b := fun hb => (first_cubic_iff l b).mpr hb hdegree
  rw [← (quadratic_space_eq l b).1]
  have hc' : c + ExtGate 0 l b ∈ V4 Q0 := by
    have hp : P0 ∈ V4 Q0 := by
      refine ⟨p0_degree, ?_⟩
      rw [pi2_a0b0]
      exact Submodule.mem_span_singleton_self _
    have h := (V4 Q0).add_mem hc ((V4 Q0).smul_mem (b 0 + b 3) hp)
    rw [extGate_one, add_mul, low_mul_linear hb, add_comm
      ((b 0 + b 3) • P0) (linANF l * linANF b), add_assoc, add_cancel_right] at h
    simpa only [extGate_zero] using h
  exact le_of_eq (extend_eq_of_add_mem hc')

end

end UnrestrictedBooleanMul.LowHalfMul3.LambdaOne
