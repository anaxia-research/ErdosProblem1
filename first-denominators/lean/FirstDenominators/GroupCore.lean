import FirstDenominators.RatioSet

/-!
# Group-theoretic core of Theorems 3 and 4

* `odd_card_iff_not_mem` : in a group whose only elements with `g² = 1` are `1` and `ε`
  (e.g. a cyclic group of even order, `isCyclic_sq_eq_one`), a subgroup has odd order iff it
  omits `ε`.
* `mul_mem_of_sq_mem` : if `H` has odd order, `q ∉ H` and `q² ∈ H`, then `q ∈ εH`.
* `card_image_A` : the image of `{q⁻¹, 1, q}` in `G/H` has `1 + c_H(q)` elements.
* `card_A_mul` : the same count for `{q⁻¹, 1, q} · H` inside `G` (`= |H| (1 + c_H(q))`).
-/

namespace FirstDenominators

open Pointwise Finset

section General

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- `c_H(q)`: `0` if `q ∈ H`, `1` if `q ∉ H` but `q² ∈ H`, `2` otherwise. -/
def cH (H : Finset G) (q : G) : ℕ := if q ∈ H then 0 else if q ^ 2 ∈ H then 1 else 2

/-- In a cyclic group, `g² = 1` forces `g = 1` or `g = ε` for any element `ε ≠ 1` with `ε² = 1`. -/
theorem isCyclic_sq_eq_one [Fintype G] [IsCyclic G] {ε : G} (hε : ε ^ 2 = 1) (hε1 : ε ≠ 1)
    (g : G) (hg : g ^ 2 = 1) : g = 1 ∨ g = ε := by
  by_contra h
  push Not at h
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  have hsub : ({1, ε, g} : Finset G) ⊆ univ.filter (fun a : G => a ^ 2 = 1) := by
    intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [*]
  have h3 : ({1, ε, g} : Finset G).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simpa [eq_comm] using h.2
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun e => hε1 e.symm, fun e => h.1 e.symm⟩
  have := card_le_card hsub
  omega

variable (H : Subgroup G) {ε : G}

omit [DecidableEq G] in
/-- A subgroup has odd order iff it omits `ε`, when `1, ε` are the only square roots of `1`. -/
theorem odd_card_iff_not_mem [Finite G] (hε : orderOf ε = 2)
    (huniq : ∀ g : G, g ^ 2 = 1 → g = 1 ∨ g = ε) : Odd (Nat.card H) ↔ ε ∉ H := by
  constructor
  · intro hodd hmem
    have : orderOf (⟨ε, hmem⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hε] at this
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  · intro hnot
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (even_iff_two_dvd.1 hev)
    have hy2 : (y : G) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hy; rw [← hy]; exact pow_orderOf_eq_one _
    have hy1 : (y : G) ≠ 1 := by
      intro h1; rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hy; norm_num at hy
    rcases huniq _ hy2 with h | h
    · exact hy1 h
    · exact hnot (h ▸ y.2)

omit [DecidableEq G] in
/-- If `H` has odd order, `q ∉ H` and `q² ∈ H`, then `ε q ∈ H` (i.e. `q ∈ εH`, as `ε = ε⁻¹`). -/
theorem mul_mem_of_sq_mem [Finite G] (hodd : Odd (Nat.card H))
    (huniq : ∀ g : G, g ^ 2 = 1 → g = 1 ∨ g = ε) {q : G} (hq : q ∉ H) (hq2 : q ^ 2 ∈ H) :
    ε * q ∈ H := by
  obtain ⟨j, hj⟩ := hodd
  set h := Nat.card H
  have hpow : (q ^ 2) ^ h = 1 := by
    have h' := congrArg Subtype.val (pow_card_eq_one' (G := H) (x := ⟨q ^ 2, hq2⟩))
    rw [Subgroup.coe_pow, OneMemClass.coe_one] at h'
    exact h'
  have hsq : (q ^ h) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hpow]
  have hmem : q ^ (h + 1) ∈ H := by
    rw [show h + 1 = 2 * (j + 1) by omega, pow_mul]; exact H.pow_mem hq2 _
  rcases huniq _ hsq with h1 | h1
  · exact absurd (by rwa [pow_succ, h1, one_mul] at hmem) hq
  · rwa [pow_succ, h1] at hmem

/-- Cardinality of `{a⁻¹, 1, a}` in a group. -/
theorem card_triple {K : Type*} [Group K] [DecidableEq K] (a : K) :
    ({a⁻¹, 1, a} : Finset K).card = 1 + (if a = 1 then 0 else if a ^ 2 = 1 then 1 else 2) := by
  by_cases h1 : a = 1
  · subst h1; simp
  · have hi1 : a⁻¹ ≠ 1 := inv_ne_one.2 h1
    by_cases h2 : a ^ 2 = 1
    · have : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq, h2]
      rw [this]; simp [h1, h2, Finset.card_insert_of_notMem, Ne.symm h1]
    · have hia : a⁻¹ ≠ a := by
        intro e; apply h2; rw [sq]; nth_rewrite 1 [← e]; exact inv_mul_cancel a
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp [h1, h2]
      · simpa [eq_comm] using h1
      · simp [hi1, hia]

/-- **The image of `{q⁻¹, 1, q}` in `G/H` has `1 + c_H(q)` elements.** -/
theorem card_image_A [DecidableEq (G ⧸ H)] (Hf : Finset G) (hH : ∀ g, g ∈ Hf ↔ g ∈ H) (q : G) :
    ((A q).image (QuotientGroup.mk : G → G ⧸ H)).card = 1 + cH Hf q := by
  have himg : (A q).image (QuotientGroup.mk : G → G ⧸ H) =
      {(q : G ⧸ H)⁻¹, 1, (q : G ⧸ H)} := by
    simp [A, Finset.image_insert, Finset.image_singleton]
  rw [himg, card_triple]
  have e1 : ((q : G ⧸ H) = 1) ↔ q ∈ Hf := by rw [hH]; exact QuotientGroup.eq_one_iff q
  have e2 : ((q : G ⧸ H) ^ 2 = 1) ↔ q ^ 2 ∈ Hf := by
    rw [hH, ← QuotientGroup.mk_pow]; exact QuotientGroup.eq_one_iff _
  simp only [cH, e1, e2]

/-- Cosets of a subgroup, as finsets. -/
theorem smul_eq_self_of_mem [Fintype G] (Hf : Finset G) (hH : ∀ g, g ∈ Hf ↔ g ∈ H) {h : G}
    (hh : h ∈ Hf) : h • Hf = Hf := by
  apply eq_of_subset_of_card_le
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := mem_smul_finset.1 hg
    rw [hH] at hh hk ⊢; exact H.mul_mem hh hk
  · rw [card_smul_finset]

theorem smul_eq_smul [Fintype G] (Hf : Finset G) (hH : ∀ g, g ∈ Hf ↔ g ∈ H) {a b : G}
    (hab : a⁻¹ * b ∈ Hf) : a • Hf = b • Hf := by
  have : b • Hf = a • ((a⁻¹ * b) • Hf) := by rw [smul_smul, mul_inv_cancel_left]
  rw [this, smul_eq_self_of_mem H Hf hH hab]

theorem disjoint_smul (Hf : Finset G) (hH : ∀ g, g ∈ Hf ↔ g ∈ H) {a b : G}
    (hab : a⁻¹ * b ∉ Hf) : Disjoint (a • Hf) (b • Hf) := by
  rw [Finset.disjoint_left]
  intro g ha hb
  obtain ⟨k1, hk1, rfl⟩ := mem_smul_finset.1 ha
  obtain ⟨k2, hk2, e⟩ := mem_smul_finset.1 hb
  apply hab
  simp only [smul_eq_mul] at e
  have : a⁻¹ * b = k1 * k2⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, e]; group
  rw [this, hH]; rw [hH] at hk1 hk2; exact H.mul_mem hk1 (H.inv_mem hk2)

/-- `|{q⁻¹, 1, q} · H| = |H| (1 + c_H(q))`. -/
theorem card_A_mul [Fintype G] (Hf : Finset G) (hH : ∀ g, g ∈ Hf ↔ g ∈ H) (q : G) :
    (A q * Hf).card = Hf.card * (1 + cH Hf q) := by
  have hdec : A q * Hf = q⁻¹ • Hf ∪ (Hf ∪ q • Hf) := by
    ext g
    simp only [A, mem_mul, mem_insert, mem_singleton, mem_union, mem_smul_finset, smul_eq_mul]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact Or.inl ⟨b, hb, rfl⟩
      · exact Or.inr (Or.inl (by simpa using hb))
      · exact Or.inr (Or.inr ⟨b, hb, rfl⟩)
    · rintro (⟨b, hb, rfl⟩ | hg | ⟨b, hb, rfl⟩)
      · exact ⟨q⁻¹, Or.inl rfl, b, hb, rfl⟩
      · exact ⟨1, Or.inr (Or.inl rfl), g, hg, one_mul g⟩
      · exact ⟨q, Or.inr (Or.inr rfl), b, hb, rfl⟩
  have hone : (1 : G) • Hf = Hf := one_smul G Hf
  rw [hdec]
  unfold cH
  by_cases h1 : q ∈ Hf
  · have e1 : q⁻¹ • Hf = Hf := smul_eq_self_of_mem H Hf hH (by rw [hH] at h1 ⊢; exact H.inv_mem h1)
    have e2 : q • Hf = Hf := smul_eq_self_of_mem H Hf hH h1
    rw [e1, e2]; simp [h1]
  · by_cases h2 : q ^ 2 ∈ Hf
    · have e1 : q⁻¹ • Hf = q • Hf := smul_eq_smul H Hf hH (by rw [inv_inv, ← sq]; exact h2)
      have d : Disjoint Hf (q • Hf) := by
        have := disjoint_smul H Hf hH (a := 1) (b := q) (by simpa using h1)
        rwa [hone] at this
      rw [e1, ← union_assoc, union_comm (q • Hf) Hf, union_assoc, union_self,
        card_union_of_disjoint d, card_smul_finset]
      simp [h1, h2]; ring
    · have d1 : Disjoint (q⁻¹ • Hf) Hf := by
        have := disjoint_smul H Hf hH (a := q⁻¹) (b := 1) (by simpa using h1)
        rwa [hone] at this
      have d2 : Disjoint (q⁻¹ • Hf) (q • Hf) :=
        disjoint_smul H Hf hH (by rw [inv_inv, ← sq]; exact h2)
      have d3 : Disjoint Hf (q • Hf) := by
        have := disjoint_smul H Hf hH (a := 1) (b := q) (by simpa using h1)
        rwa [hone] at this
      rw [card_union_of_disjoint (disjoint_union_right.2 ⟨d1, d2⟩),
        card_union_of_disjoint d3, card_smul_finset, card_smul_finset]
      simp [h1, h2]; ring

end General

end FirstDenominators
