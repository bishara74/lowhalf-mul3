import LowHalfMul3.Types
import LowHalfMul3.LineDerivative

/-!
# Theorem 12 of `lambda4_proof.tex` (the case `λ = 4`): `StarFree`

Let `P₀ = a₀ ∧ b₀` and `P_k = l_k ∧ r_k` (`k = 1, 2, 3`) with
`Z₁ ∈ Q = span{P₀, …, P₃}`. We show that `Q` has a good direction in the sense
of Lemma 8′ (`GoodDir`), so (★) has no solution.

Write `Z₁ = c₀P₀ + c₁P₁ + c₂P₂ + c₃P₃` and `Z = Z₁ + c₀P₀` (rank 4, in `Λ²(U)`).

* No or one `c_k = 1` (`k ≥ 1`): `Z` would be a single wedge — impossible
  (`wedge_ne_Z`).
* Two: Lemma 3 kills both cross parts; Case A below.
* Three: `P₁ + P₂ + P₃ = Z`, so the cross parts sum to zero. If one of them
  vanishes, the other two are equal: Case A. Otherwise normalise by Lemma 11:
  - all of type `v`: some direction kills all `P_k` (Lemma 8), or some `r_k = 0`,
    or all `r_k` coincide and `Z = (l₁ + l₂ + l₃) ∧ r` is a wedge
    (`zeroFull`, with the finite check `zeroFull_finite`);
  - one or three full: the `a₂ ∧ b₂` coefficients sum to `1 ≠ 0` (parity);
  - two full: `Z = (v₁ lᵢ + v₂ rᵢ + l_m) ∧ r_m` is a wedge (`twoFull`).
* **Case A** (`goodDir_caseA`): if all nonzero cross parts equal one
  `Φ(a ∧ b)`, Lemma 6 gives `ι_{a₂}(a ∧ b) ≠ b₀` or `ι_{b₂}(a ∧ b) ≠ a₀`, and
  Lemma 8′ applies along `a₂` or `b₂` with `ℓ` that contraction.

This route replaces the paper's Proposition 7, Lemma 5 and the
`d_U`-case analysis; see LEAN_LOG.md, phase 4.
-/

namespace UnrestrictedBooleanMul

namespace LowHalfMul3

noncomputable section

/-! ## Good directions from generators -/

theorem goodDir_of_gens (gen : Fin 4 → TwoForm6) {e d ℓ : Fin 6 → F₂}
    (hp : PaperPair e d) (hℓ : ℓ ≠ d) (hk : ∀ k, ∃ γ : F₂, iota e (gen k) = γ • ℓ) :
    GoodDir (Submodule.span F₂ (Set.range gen)) := by
  refine ⟨e, d, ℓ, hp, hℓ, fun ω hω => ?_⟩
  have hle : Submodule.span F₂ (Set.range gen) ≤
      (Submodule.span F₂ {ℓ}).comap (iota e) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨γ, hγ⟩ := hk k
    show iota e (gen k) ∈ Submodule.span F₂ {ℓ}
    rw [hγ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ℓ)
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_comap.mp (hle hω))
  exact ⟨γ, hγ.symm⟩

theorem PaperPair.ne_zero {e d : Fin 6 → F₂} (hp : PaperPair e d) : (0 : Fin 6 → F₂) ≠ d := by
  rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> intro h
  · have := congrFun h 3; simp [unitVec] at this
  · have := congrFun h 0; simp [unitVec] at this
  · have := congrFun h 0; simp [unitVec] at this

/-- A direction killing every generator gives a good direction (`ℓ = 0`). -/
theorem goodDir_kill (gen : Fin 4 → TwoForm6) {e d : Fin 6 → F₂} (hp : PaperPair e d)
    (hk : ∀ k, iota e (gen k) = 0) : GoodDir (Submodule.span F₂ (Set.range gen)) :=
  goodDir_of_gens gen hp hp.ne_zero fun k => ⟨0, by rw [hk k, zero_smul]⟩

theorem unitVec3_eq : unitVec 3 = ![0, 0, 0, 1, 0, 0] := by
  funext i
  revert i
  unfold unitVec
  decide

theorem unitVec0_eq : unitVec 0 = ![1, 0, 0, 0, 0, 0] := by
  funext i
  revert i
  unfold unitVec
  decide

/-- **Case A.** If every generator has cross part `0` or `Φ(a ∧ b)`, there is a
good direction (by Lemma 6 and Lemma 8′). -/
theorem goodDir_caseA (gen : Fin 4 → TwoForm6) (a b : Fin 6 → F₂)
    (hk : ∀ k, Phi (gen k) = 0 ∨ Phi (gen k) = Phi (wedge a b)) :
    GoodDir (Submodule.span F₂ (Set.range gen)) := by
  have h6 := lemma6 a b
  rw [pi2_lowMul3_two, phi_q2] at h6
  have hor : (Phi (wedge a b)).1 ≠ unitVec 3 ∨ (Phi (wedge a b)).2 ≠ unitVec 0 := by
    by_cases h1 : (Phi (wedge a b)).1 = unitVec 3
    · right
      intro h2
      apply h6
      rw [← unitVec3_eq, ← unitVec0_eq, ← h1, ← h2]
    · exact Or.inl h1
  rcases hor with h | h
  · refine goodDir_of_gens gen (e := dirA2) (d := unitVec 3) (Or.inl ⟨rfl, rfl⟩) h ?_
    intro k
    rcases hk k with hz | he
    · exact ⟨0, by rw [zero_smul]; exact congrArg Prod.fst hz⟩
    · exact ⟨1, by rw [one_smul]; exact congrArg Prod.fst he⟩
  · refine goodDir_of_gens gen (e := dirB2) (d := unitVec 0) (Or.inr (Or.inl ⟨rfl, rfl⟩)) h ?_
    intro k
    rcases hk k with hz | he
    · exact ⟨0, by rw [zero_smul]; exact congrArg Prod.snd hz⟩
    · exact ⟨1, by rw [one_smul]; exact congrArg Prod.snd he⟩

/-! ## Facts about `P₀`, `Z₁` and `Z = Z₁ + c₀ P₀` -/

theorem iota_P0 {e d : Fin 6 → F₂} (hp : PaperPair e d) : iota e P0form = 0 := by
  rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · funext t; rw [iota_dirA2_apply]; simp [P0form, wedge, unitVec]
  · funext t; rw [iota_dirB2_apply]; simp [P0form, wedge, unitVec]
  · rw [iota_dirA2B2]; funext t
    simp only [Pi.add_apply]
    rw [iota_dirA2_apply, iota_dirB2_apply]; simp [P0form, wedge, unitVec]

theorem phi_P0 : Phi P0form = 0 :=
  Prod.ext (iota_P0 (Or.inl ⟨rfl, rfl⟩)) (iota_P0 (Or.inr (Or.inl ⟨rfl, rfl⟩)))

/-- Rows 2 and 5 of `Z = Z₁ + c₀ P₀` vanish: `Z ∈ Λ²(U)`. -/
theorem Z_rows (c0 : F₂) (t : Fin 6) :
    (Z1form + c0 • P0form) 2 t = 0 ∧ (Z1form + c0 • P0form) 5 t = 0 := by
  rcases Z_eq_lit_cases c0 with h | h <;> rw [h] <;> revert t
  · unfold Z1lit; decide
  · unfold Z1P0lit; decide

theorem phi_Z (c0 : F₂) : Phi (Z1form + c0 • P0form) = 0 :=
  phi_eq_zero_of_rows (Z_rows c0)

/-- Row sums of a three-term decomposition of `Z`. -/
theorem row_sum {A B C : TwoForm6} {c0 : F₂} (hsum : A + B + C = Z1form + c0 • P0form)
    (t : Fin 6) : A 2 t + B 2 t + C 2 t = 0 ∧ A 5 t + B 5 t + C 5 t = 0 :=
  ⟨by show (A + B + C) 2 t = 0; rw [hsum]; exact (Z_rows c0 t).1,
   by show (A + B + C) 5 t = 0; rw [hsum]; exact (Z_rows c0 t).2⟩

theorem tf_cancel_left {X Y W : TwoForm6} (h : X + Y = W) : Y = W + X := by
  rw [← h, add_comm X Y, add_assoc, tf_add_self, add_zero]

theorem pair_eq_of_add_eq_zero {x y : (Fin 6 → F₂) × (Fin 6 → F₂)} (h : x + y = 0) :
    x = y := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun t => ?_) (funext fun t => ?_)
  · exact f2_eq_of_add_eq_zero (congrFun h1 t)
  · exact f2_eq_of_add_eq_zero (congrFun h2 t)

theorem f2_mid : ∀ x y z : F₂, x + y + z = 0 → y = x + z := by decide

/-! ## The three-term analysis -/

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- All three of type `v`: finite core. -/
theorem zeroFull_finite : ∀ x1 y1 x2 y2 x3 y3 : F₂,
    ¬ (x1 = 0 ∧ y1 = 0) → ¬ (x2 = 0 ∧ y2 = 0) → ¬ (x3 = 0 ∧ y3 = 0) →
    (x1 = 0 ∧ x2 = 0 ∧ x3 = 0) ∨ (y1 = 0 ∧ y2 = 0 ∧ y3 = 0) ∨
    (x1 + y1 = 0 ∧ x2 + y2 = 0 ∧ x3 + y3 = 0) ∨
    (∀ s1 s2 s3 : F₂, x1 * s1 + x2 * s2 + x3 * s3 = 0 → y1 * s1 + y2 * s2 + y3 * s3 = 0 →
      s1 = 0) ∨
    (∀ s1 s2 s3 : F₂, x1 * s1 + x2 * s2 + x3 * s3 = 0 → y1 * s1 + y2 * s2 + y3 * s3 = 0 →
      s2 = 0) ∨
    (∀ s1 s2 s3 : F₂, x1 * s1 + x2 * s2 + x3 * s3 = 0 → y1 * s1 + y2 * s2 + y3 * s3 = 0 →
      s3 = 0) ∨
    (∀ s1 s2 s3 : F₂, x1 * s1 + x2 * s2 + x3 * s3 = 0 → y1 * s1 + y2 * s2 + y3 * s3 = 0 →
      s1 = s2 ∧ s2 = s3) := by
  decide

/-- The output of the three-term analysis. -/
def KillDir (A B C : TwoForm6) : Prop :=
  ∃ e d : Fin 6 → F₂, PaperPair e d ∧ iota e A = 0 ∧ iota e B = 0 ∧ iota e C = 0

/-- All three of type `v`. -/
theorem zeroFull {l1 r1 l2 r2 l3 r3 : Fin 6 → F₂} {c0 : F₂}
    (h1 : NFv l1 r1) (h2 : NFv l2 r2) (h3 : NFv l3 r3)
    (n1 : Phi (wedge l1 r1) ≠ 0) (n2 : Phi (wedge l2 r2) ≠ 0) (n3 : Phi (wedge l3 r3) ≠ 0)
    (hsum : wedge l1 r1 + wedge l2 r2 + wedge l3 r3 = Z1form + c0 • P0form) :
    KillDir (wedge l1 r1) (wedge l2 r2) (wedge l3 r3) := by
  have hr2 : ∀ t, l1 2 * r1 t + l2 2 * r2 t + l3 2 * r3 t = 0 := fun t => by
    have := (row_sum hsum t).1
    rwa [(rows_v h1 t).1, (rows_v h2 t).1, (rows_v h3 t).1] at this
  have hr5 : ∀ t, l1 5 * r1 t + l2 5 * r2 t + l3 5 * r3 t = 0 := fun t => by
    have := (row_sum hsum t).2
    rwa [(rows_v h1 t).2, (rows_v h2 t).2, (rows_v h3 t).2] at this
  rcases zeroFull_finite (l1 2) (l1 5) (l2 2) (l2 5) (l3 2) (l3 5) h1.2.2 h2.2.2 h3.2.2 with
    ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨c1, c2, c3⟩ | hs | hs | hs | hall
  · exact ⟨dirA2, unitVec 3, Or.inl ⟨rfl, rfl⟩, iota_dirA2_v h1 a1, iota_dirA2_v h2 a2,
      iota_dirA2_v h3 a3⟩
  · exact ⟨dirB2, unitVec 0, Or.inr (Or.inl ⟨rfl, rfl⟩), iota_dirB2_v h1 b1,
      iota_dirB2_v h2 b2, iota_dirB2_v h3 b3⟩
  · exact ⟨dirA2B2, unitVec 0 + unitVec 3, Or.inr (Or.inr ⟨rfl, rfl⟩), iota_dirA2B2_v h1 c1,
      iota_dirA2B2_v h2 c2, iota_dirA2B2_v h3 c3⟩
  · have hr : r1 = 0 := funext fun t => hs _ _ _ (hr2 t) (hr5 t)
    exact absurd (by rw [hr, wedge_zero_right, map_zero]) n1
  · have hr : r2 = 0 := funext fun t => hs _ _ _ (hr2 t) (hr5 t)
    exact absurd (by rw [hr, wedge_zero_right, map_zero]) n2
  · have hr : r3 = 0 := funext fun t => hs _ _ _ (hr2 t) (hr5 t)
    exact absurd (by rw [hr, wedge_zero_right, map_zero]) n3
  · have h12 : r1 = r2 := funext fun t => (hall _ _ _ (hr2 t) (hr5 t)).1
    have h23 : r2 = r3 := funext fun t => (hall _ _ _ (hr2 t) (hr5 t)).2
    rw [← h23, ← h12, ← wedge_add_left, ← wedge_add_left] at hsum
    exact (wedge_ne_Z _ _ c0 hsum).elim

/-- Two of full type, one of type `v`: `Z` would be a single wedge. -/
theorem twoFull {li ri lj rj lm rm : Fin 6 → F₂} {c0 : F₂}
    (hi : NFfull li ri) (hj : NFfull lj rj) (hm : NFv lm rm)
    (hsum : wedge li ri + wedge lj rj + wedge lm rm = Z1form + c0 • P0form) : False := by
  have hr2 : ∀ t, ri t + rj t + lm 2 * rm t = 0 := fun t => by
    have := (row_sum hsum t).1
    rwa [(rows_full hi t).1, (rows_full hj t).1, (rows_v hm t).1] at this
  have hr5 : ∀ t, li t + lj t + lm 5 * rm t = 0 := fun t => by
    have := (row_sum hsum t).2
    rwa [(rows_full hi t).2, (rows_full hj t).2, (rows_v hm t).2] at this
  have key : wedge li ri + wedge lj rj + wedge lm rm =
      wedge (lm 2 • li + lm 5 • ri + lm) rm := by
    funext a b
    simp only [Pi.add_apply, wedge, Pi.smul_apply, smul_eq_mul]
    rw [f2_mid _ _ _ (hr2 a), f2_mid _ _ _ (hr2 b), f2_mid _ _ _ (hr5 a),
      f2_mid _ _ _ (hr5 b)]
    generalize li a = p1
    generalize li b = p2
    generalize ri a = q1
    generalize ri b = q2
    generalize rm a = m1
    generalize rm b = m2
    generalize lm a = n1
    generalize lm b = n2
    generalize lm 2 = v1
    generalize lm 5 = v2
    revert p1 p2 q1 q2 m1 m2 n1 n2 v1 v2
    decide
  exact wedge_ne_Z _ _ c0 (key.symm.trans hsum)

/-- Both or neither of the two cases of Case A, packaged. -/
def CaseA3 (A B C : TwoForm6) : Prop :=
  ∃ a b : Fin 6 → F₂, (Phi A = 0 ∨ Phi A = Phi (wedge a b)) ∧
    (Phi B = 0 ∨ Phi B = Phi (wedge a b)) ∧ (Phi C = 0 ∨ Phi C = Phi (wedge a b))

/-- The three-term case `P₁ + P₂ + P₃ = Z`. -/
theorem triple_core {c0 : F₂} {l1 r1 l2 r2 l3 r3 : Fin 6 → F₂}
    (hc : c0 • P0form + wedge l1 r1 + wedge l2 r2 + wedge l3 r3 = Z1form) :
    CaseA3 (wedge l1 r1) (wedge l2 r2) (wedge l3 r3) ∨
      KillDir (wedge l1 r1) (wedge l2 r2) (wedge l3 r3) := by
  have hsum : wedge l1 r1 + wedge l2 r2 + wedge l3 r3 = Z1form + c0 • P0form :=
    tf_cancel_left (by rw [← hc]; abel)
  have hΦ : Phi (wedge l1 r1) + Phi (wedge l2 r2) + Phi (wedge l3 r3) = 0 := by
    rw [← map_add, ← map_add, hsum, phi_Z]
  by_cases n1 : Phi (wedge l1 r1) = 0
  · rw [n1, zero_add] at hΦ
    exact Or.inl ⟨l2, r2, Or.inl n1, Or.inr rfl, Or.inr (pair_eq_of_add_eq_zero hΦ).symm⟩
  by_cases n2 : Phi (wedge l2 r2) = 0
  · rw [n2, add_zero] at hΦ
    exact Or.inl ⟨l1, r1, Or.inr rfl, Or.inl n2, Or.inr (pair_eq_of_add_eq_zero hΦ).symm⟩
  by_cases n3 : Phi (wedge l3 r3) = 0
  · rw [n3, add_zero] at hΦ
    exact Or.inl ⟨l1, r1, Or.inr rfl, Or.inr (pair_eq_of_add_eq_zero hΦ).symm, Or.inl n3⟩
  right
  obtain ⟨l1', r1', hw1, t1⟩ := types l1 r1
  obtain ⟨l2', r2', hw2, t2⟩ := types l2 r2
  obtain ⟨l3', r3', hw3, t3⟩ := types l3 r3
  rw [← hw1] at hsum n1 ⊢
  rw [← hw2] at hsum n2 ⊢
  rw [← hw3] at hsum n3 ⊢
  have h25 : wedge l1' r1' 2 5 + wedge l2' r2' 2 5 + wedge l3' r3' 2 5 = 0 :=
    (row_sum hsum 5).1
  rcases t1 with z1 | v1 | f1
  · exact absurd (phi_of_NFzero z1) n1
  all_goals rcases t2 with z2 | v2 | f2
  all_goals try exact absurd (phi_of_NFzero z2) n2
  all_goals rcases t3 with z3 | v3 | f3
  all_goals try exact absurd (phi_of_NFzero z3) n3
  -- v v v
  · exact zeroFull v1 v2 v3 n1 n2 n3 hsum
  -- v v f
  · rw [gamma_v v1, gamma_v v2, gamma_full f3] at h25; exact absurd h25 (by decide)
  -- v f v
  · rw [gamma_v v1, gamma_full f2, gamma_v v3] at h25; exact absurd h25 (by decide)
  -- v f f
  · exact (twoFull f2 f3 v1 (by rw [← hsum]; abel)).elim
  -- f v v
  · rw [gamma_full f1, gamma_v v2, gamma_v v3] at h25; exact absurd h25 (by decide)
  -- f v f
  · exact (twoFull f1 f3 v2 (by rw [← hsum]; abel)).elim
  -- f f v
  · exact (twoFull f1 f2 v3 hsum).elim
  -- f f f
  · rw [gamma_full f1, gamma_full f2, gamma_full f3] at h25; exact absurd h25 (by decide)

/-! ## The `Z₁`-decomposition -/

theorem none_false {c0 : F₂} (h : c0 • P0form = Z1form) : False :=
  wedge_ne_Z 0 0 c0 (by rw [wedge_self, ← h, tf_add_self])

theorem single_false {c0 : F₂} {a b : Fin 6 → F₂} (h : c0 • P0form + wedge a b = Z1form) :
    False :=
  wedge_ne_Z a b c0 (tf_cancel_left h)

theorem pair_zero {c0 : F₂} {a b a' b' : Fin 6 → F₂}
    (h : c0 • P0form + wedge a b + wedge a' b' = Z1form) :
    Phi (wedge a b) = 0 ∧ Phi (wedge a' b') = 0 := by
  have h' : wedge a b + wedge a' b' = Z1form + c0 • P0form :=
    tf_cancel_left (by rw [← add_assoc]; exact h)
  exact ⟨lemma3 h', lemma3 (by rw [add_comm]; exact h')⟩

/-- Every decomposition `Z₁ = c₀P₀ + c₁P₁ + c₂P₂ + c₃P₃` leads to Case A or a
killing direction. -/
theorem decomposition_cases (c0 c1 c2 c3 : F₂) {l1 r1 l2 r2 l3 r3 : Fin 6 → F₂}
    (hc : c0 • P0form + c1 • wedge l1 r1 + c2 • wedge l2 r2 + c3 • wedge l3 r3 = Z1form) :
    CaseA3 (wedge l1 r1) (wedge l2 r2) (wedge l3 r3) ∨
      KillDir (wedge l1 r1) (wedge l2 r2) (wedge l3 r3) := by
  rcases f2_eq_zero_or_one c1 with rfl | rfl
  · rcases f2_eq_zero_or_one c2 with rfl | rfl
    · rcases f2_eq_zero_or_one c3 with rfl | rfl
      · simp only [zero_smul, add_zero] at hc; exact (none_false hc).elim
      · simp only [zero_smul, one_smul, add_zero] at hc; exact (single_false hc).elim
    · rcases f2_eq_zero_or_one c3 with rfl | rfl
      · simp only [zero_smul, one_smul, add_zero] at hc; exact (single_false hc).elim
      · simp only [zero_smul, one_smul, add_zero] at hc
        obtain ⟨z2, z3⟩ := pair_zero hc
        exact Or.inl ⟨l1, r1, Or.inr rfl, Or.inl z2, Or.inl z3⟩
  · rcases f2_eq_zero_or_one c2 with rfl | rfl
    · rcases f2_eq_zero_or_one c3 with rfl | rfl
      · simp only [zero_smul, one_smul, add_zero] at hc; exact (single_false hc).elim
      · simp only [zero_smul, one_smul, add_zero] at hc
        obtain ⟨z1, z3⟩ := pair_zero hc
        exact Or.inl ⟨l2, r2, Or.inl z1, Or.inr rfl, Or.inl z3⟩
    · rcases f2_eq_zero_or_one c3 with rfl | rfl
      · simp only [zero_smul, one_smul, add_zero] at hc
        obtain ⟨z1, z2⟩ := pair_zero hc
        exact Or.inl ⟨l3, r3, Or.inl z1, Or.inl z2, Or.inr rfl⟩
      · simp only [one_smul] at hc
        exact triple_core hc

/-! ## Theorem 12 -/

/-- **Theorem 12, combinatorial core.** If `P₀ = a₀ ∧ b₀` and `Z₁` lies in the
span of `P₀` and three further wedges, that span has a good direction. -/
theorem goodDir_main (l r : Fin 4 → Fin 6 → F₂) (h0 : wedge (l 0) (r 0) = P0form)
    (hZ : Z1form ∈ Submodule.span F₂ (Set.range fun k => wedge (l k) (r k))) :
    GoodDir (Submodule.span F₂ (Set.range fun k => wedge (l k) (r k))) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F₂).mp hZ
  rw [Fin.sum_univ_four] at hc
  have hc' : c 0 • P0form + c 1 • wedge (l 1) (r 1) + c 2 • wedge (l 2) (r 2) +
      c 3 • wedge (l 3) (r 3) = Z1form := by
    rw [← h0]; exact hc
  rcases decomposition_cases (c 0) (c 1) (c 2) (c 3) hc' with
    ⟨a, b, h1, h2, h3⟩ | ⟨e, d, hp, k1, k2, k3⟩
  · refine goodDir_caseA _ a b fun k => ?_
    fin_cases k
    · exact Or.inl (by show Phi (wedge (l 0) (r 0)) = 0; rw [h0]; exact phi_P0)
    · exact h1
    · exact h2
    · exact h3
  · refine goodDir_kill _ hp fun k => ?_
    fin_cases k
    · show iota e (wedge (l 0) (r 0)) = 0; rw [h0]; exact iota_P0 hp
    · exact k1
    · exact k2
    · exact k3

/-- **Theorem 12 (`λ = 4`).** `StarFree` holds. -/
theorem starFree : StarFree := by
  intro L R hL hR hL0 hR0 hZ f h hf hh hg
  have hfun : (fun i => pi2 (L i * R i)) = fun k => wedge (lin (L k)) (lin (R k)) :=
    funext fun k => pi2_mul_affine (hL k) (hR k)
  have hQ : quadSpan L R =
      Submodule.span F₂ (Set.range fun k => wedge (lin (L k)) (lin (R k))) := by
    rw [quadSpan, hfun]
  rw [hQ] at hZ hf hh hg
  have h0 : wedge (lin (L 0)) (lin (R 0)) = P0form := by
    rw [hL0, hR0]
    simp only [aVar, bVar, lin_X]
    rfl
  rw [pi2_lowMul3_one] at hZ
  exact starFree_of_goodDir (goodDir_main (fun k => lin (L k)) (fun k => lin (R k)) h0 hZ)
    f h hf hh hg

/-- The case `λ = 4` of the five-gate exclusion. -/
theorem lambdaCase_four : LambdaCase 4 := lambdaCase_four_of_starFree starFree

/-- The five-gate exclusion, from the three cases `λ = 1, 2, 3`. -/
theorem not_hasCircuit_five_of_lambda_cases (h1 : LambdaCase 1) (h2 : LambdaCase 2)
    (h3 : LambdaCase 3) : ¬ HasCircuit lowMul3 5 :=
  not_hasCircuit_five_of_cases h1 h2 h3 lambdaCase_four

/-- **`MC(lowMul3) = 6` from the cases `λ = 1, 2, 3` alone.** -/
theorem mc_eq_six_of_lambda_cases (h1 : LambdaCase 1) (h2 : LambdaCase 2)
    (h3 : LambdaCase 3) : MC(lowMul3) = 6 :=
  mc_eq_six_of_remaining_cases h1 h2 h3 starFree

end

end LowHalfMul3

end UnrestrictedBooleanMul
