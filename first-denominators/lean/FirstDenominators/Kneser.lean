import FirstDenominators.GroupCore
import FirstDenominators.Vendor.Kneser

/-!
# Kneser's theorem, Lemma 2, and the abstract Theorems 3, 4 and Corollary 5

Mathlib (v4.34.1) does not contain Kneser's addition theorem (it has Cauchy–Davenport and
DeVos's generalisation only).  We vendor the formalisation of Mantas Bakšys and Yaël Dillies
(`Finset.mul_kneser`, from github.com/YaelDillies/misc-yd, Apache 2.0, originally LeanCamCombi)
in `FirstDenominators/Vendor/`.  The abstract theorems below are stated with the proposition
`KneserHyp G` as a parameter, and `kneserHyp` proves it for every finite abelian group, so all
results are unconditional (see the `_uncond` versions and `Main.lean`).

`KneserHyp G` : for non-empty `s, t ⊆ G`, with `H = stab(s t)`,
  `|s H| + |t H| ≤ |s t| + |H|`                      (Kneser, Math. Z. 58 (1953)).
-/

set_option linter.unusedSectionVars false

namespace FirstDenominators

open Pointwise Finset

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The stabiliser `{g : g • S = S}` of a finset, as a finset. -/
def stabF (S : Finset G) : Finset G := univ.filter (fun g => g • S = S)

theorem mem_stabF {S : Finset G} {g : G} : g ∈ stabF S ↔ g • S = S := by simp [stabF]

theorem mem_stabF_iff {S : Finset G} (g : G) : g ∈ stabF S ↔ g ∈ MulAction.stabilizer G S := by
  rw [mem_stabF, MulAction.mem_stabilizer_iff]

theorem card_stabF (S : Finset G) : (stabF S).card = Nat.card (MulAction.stabilizer G S) := by
  have e : Nat.card (MulAction.stabilizer G S) = Nat.card {g // g ∈ stabF S} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun g => (mem_stabF_iff g).symm))
  rw [e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem stabF_one : stabF (1 : Finset G) = {1} := by
  ext g
  simp only [mem_stabF, mem_singleton, ← Finset.singleton_one, Finset.smul_finset_singleton,
    smul_eq_mul, mul_one, Finset.singleton_inj]

/-- **Kneser's theorem** for `G`, as a proposition (used only as a hypothesis). -/
def KneserHyp (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] : Prop :=
  ∀ s t : Finset G, s.Nonempty → t.Nonempty →
    (s * stabF (s * t)).card + (t * stabF (s * t)).card ≤ (s * t).card + (stabF (s * t)).card

/-- **Kneser's theorem holds** in every finite abelian group: this is `Finset.mul_kneser`
(Bakšys–Dillies, vendored in `FirstDenominators/Vendor/`), restated for `stabF`. -/
theorem kneserHyp : KneserHyp G := by
  intro s t hs ht
  have e : stabF (s * t) = (s * t).mulStab := by
    ext g; rw [mem_stabF]; exact (Finset.mem_mulStab (hs.mul ht)).symm
  rw [e]
  exact Finset.mul_kneser (s := s) (t := t)

/-! ### Basic facts about stabilisers and saturated sets -/

theorem one_mem_stabF (S : Finset G) : (1 : G) ∈ stabF S := by simp [mem_stabF]

theorem mul_stabF_eq (S : Finset G) : S * stabF S = S := by
  ext g
  simp only [mem_mul]
  constructor
  · rintro ⟨s, hs, h, hh, rfl⟩
    rw [mem_stabF] at hh
    rw [← hh, mul_comm]; exact smul_mem_smul_finset hs
  · intro hg; exact ⟨g, hg, 1, one_mem_stabF S, mul_one g⟩

theorem mul_mul_self_of_subgroup (H : Subgroup G) (Hf : Finset G) (hH : ∀ g, g ∈ Hf ↔ g ∈ H) :
    Hf * Hf = Hf := by
  ext g
  simp only [mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; rw [hH] at ha hb ⊢; exact H.mul_mem ha hb
  · intro hg; exact ⟨g, hg, 1, (hH 1).2 H.one_mem, mul_one g⟩

theorem stab_le_of_sat (Hf : Finset G)
    {T : Finset G} (hT : T * Hf = T) {h : G} (hh : h ∈ Hf) : h • T = T := by
  apply eq_of_subset_of_card_le
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := mem_smul_finset.1 hg
    rw [← hT]; exact mem_mul.2 ⟨t, ht, h, hh, by rw [smul_eq_mul, mul_comm]⟩
  · rw [card_smul_finset]

theorem smul_mul_eq (g : G) (B T : Finset G) : g • (B * T) = B * (g • T) := by
  ext a
  simp only [mem_smul_finset, mem_mul, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨b, hb, t, ht, rfl⟩, rfl⟩
    exact ⟨b, hb, g * t, ⟨t, ht, rfl⟩, by rw [mul_left_comm]⟩
  · rintro ⟨b, hb, _, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨b * t, ⟨b, hb, t, ht, rfl⟩, by rw [mul_left_comm]⟩

theorem stabF_subset_mul (B T : Finset G) : stabF T ⊆ stabF (B * T) := by
  intro g hg
  rw [mem_stabF] at hg ⊢
  rw [smul_mul_eq, hg]

theorem nonempty_prod (l : List (Finset G)) (h : ∀ B ∈ l, B.Nonempty) : l.prod.Nonempty := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons B l ih =>
    rw [List.prod_cons]
    exact (h B (by simp)).mul (ih (fun C hC => h C (by simp [hC])))

theorem prod_mul_sat (Hf : Finset G) (l : List (Finset G)) (hl : l ≠ [])
    (h : ∀ B ∈ l, B * Hf = B) : l.prod * Hf = l.prod := by
  induction l with
  | nil => exact absurd rfl hl
  | cons B l ih =>
    rw [List.prod_cons, mul_assoc]
    by_cases hl' : l = []
    · subst hl'; simpa using h B (by simp)
    · rw [ih hl' (fun C hC => h C (by simp [hC]))]

/-! ### Lemma 2 (Kneser for `k` sets) -/

theorem kneser_sat (hK : KneserHyp G) (H : Subgroup G) (Hf : Finset G)
    (hH : ∀ g, g ∈ Hf ↔ g ∈ H) :
    ∀ (Bs : List (Finset G)), Bs ≠ [] → (∀ B ∈ Bs, B.Nonempty ∧ B * Hf = B) →
      stabF Bs.prod = Hf →
      Hf.card + (Bs.map card).sum ≤ Bs.prod.card + Bs.length * Hf.card := by
  intro Bs
  induction Bs with
  | nil => intro h; exact absurd rfl h
  | cons B l ih =>
    intro _ hB hstab
    by_cases hl : l = []
    · subst hl
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons,
        List.prod_nil, mul_one, List.length_cons, List.length_nil]
      omega
    · have hBl : ∀ C ∈ l, C.Nonempty ∧ C * Hf = C := fun C hC => hB C (by simp [hC])
      have hTsat : l.prod * Hf = l.prod := prod_mul_sat Hf l hl (fun C hC => (hBl C hC).2)
      rw [List.prod_cons] at hstab ⊢
      have hTstab : stabF l.prod = Hf := by
        apply Subset.antisymm
        · rw [← hstab]; exact stabF_subset_mul B l.prod
        · intro h hh; rw [mem_stabF]; exact stab_le_of_sat Hf hTsat hh
      have ih' := ih hl hBl hTstab
      have hk := hK B l.prod (hB B (by simp)).1 (nonempty_prod l (fun C hC => (hBl C hC).1))
      rw [hstab, (hB B (by simp)).2, hTsat] at hk
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [add_mul, one_mul]
      linarith [ih', hk]

/-- **Lemma 2** (Kneser's theorem for `k` sets), in the form
`|H| + Σ |A_i H| ≤ |S| + k |H|`, i.e. `|S/H| ≥ 1 + Σ (|A_i H/H| - 1)`, `S = A₁⋯A_k`,
`H = stab(S)`. -/
theorem prod_map_mul_sat (Hf : Finset G) (hHH : Hf * Hf = Hf) (l : List (Finset G))
    (hl : l ≠ []) : (l.map (· * Hf)).prod = l.prod * Hf := by
  induction l with
  | nil => exact absurd rfl hl
  | cons A l ih =>
    by_cases hl' : l = []
    · subst hl'; simp
    · simp only [List.map_cons, List.prod_cons]
      rw [ih hl', show A * Hf * (l.prod * Hf) = A * l.prod * (Hf * Hf) by
        simp only [mul_assoc, mul_left_comm Hf l.prod Hf], hHH, mul_assoc]

theorem kneser_k (hK : KneserHyp G) (As : List (Finset G)) (hne : ∀ A ∈ As, A.Nonempty) :
    (stabF As.prod).card + (As.map (fun A => (A * stabF As.prod).card)).sum ≤
      As.prod.card + As.length * (stabF As.prod).card := by
  rcases As with _ | ⟨A0, l0⟩
  · simp [stabF_one]
  set As := A0 :: l0 with hAsdef
  have hAs : As ≠ [] := by simp [hAsdef]
  set Hf := stabF As.prod with hHf
  have hH : ∀ g, g ∈ Hf ↔ g ∈ MulAction.stabilizer G As.prod := mem_stabF_iff
  have hHH := mul_mul_self_of_subgroup _ Hf hH
  have hprod : (As.map (· * Hf)).prod = As.prod * Hf := prod_map_mul_sat Hf hHH As hAs
  have hS : As.prod * Hf = As.prod := by rw [hHf]; exact mul_stabF_eq _
  have key := kneser_sat hK _ Hf hH (As.map (· * Hf)) (by simpa using hAs)
    (by
      intro B hB
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
      exact ⟨(hne A hA).mul ⟨1, (hH 1).2 (Subgroup.one_mem _)⟩,
        by rw [mul_assoc, hHH]⟩)
    (by rw [hprod, hS])
  rw [hprod, hS, List.map_map, List.length_map] at key
  exact key

/-! ### Theorem 3 (abstract form) -/

theorem one_mem_prod_A (qs : List G) : (1 : G) ∈ (qs.map A).prod := by
  induction qs with
  | nil => simp
  | cons q l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mem_mul.2 ⟨1, by simp [A], 1, ih, mul_one 1⟩

theorem inv_mem_prod_A {qs : List G} {q : G} (hq : q ∈ qs) : q⁻¹ ∈ (qs.map A).prod := by
  induction qs with
  | nil => simp at hq
  | cons r l ih =>
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 hq with rfl | h
    · exact mem_mul.2 ⟨q⁻¹, by simp [A], 1, one_mem_prod_A l, mul_one _⟩
    · exact mem_mul.2 ⟨1, by simp [A], q⁻¹, ih h, one_mul _⟩

theorem sum_card_A_mul (H : Subgroup G) (Hf : Finset G) (hH : ∀ g, g ∈ Hf ↔ g ∈ H)
    (qs : List G) :
    ((qs.map A).map (fun B => (B * Hf).card)).sum =
      Hf.card * qs.length + Hf.card * (qs.map (cH Hf)).sum := by
  induction qs with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih, card_A_mul H Hf hH q]; ring

/-- **Theorem 3, abstract form.** `S = A_{q₁} ⋯ A_{q_k}`, `H = stab(S)`. If `ε, t ∉ S`, then
`H ⊂ S`, `ε ∉ H` and `|H| (Σ c_H(q_i) + 2 + δ) ≤ |G|`, where `δ = 0` iff `ε⁻¹ t ∈ H`. -/
theorem thm3_abstract (hK : KneserHyp G) (qs : List G) {ε t : G}
    (hε : ε ∉ (qs.map A).prod) (ht : t ∉ (qs.map A).prod) :
    stabF (qs.map A).prod ⊆ (qs.map A).prod ∧ ε ∉ stabF (qs.map A).prod ∧
    (stabF (qs.map A).prod).card *
      ((qs.map (cH (stabF (qs.map A).prod))).sum + 2 +
        (if ε⁻¹ * t ∈ stabF (qs.map A).prod then 0 else 1)) ≤ Fintype.card G := by
  set S := (qs.map A).prod with hSdef
  set Hf := stabF S with hHf
  have hH : ∀ g, g ∈ Hf ↔ g ∈ MulAction.stabilizer G S := mem_stabF_iff
  have h1 : (1 : G) ∈ S := one_mem_prod_A qs
  have hsub : Hf ⊆ S := by
    intro h hh
    have : h • (1 : G) ∈ h • S := smul_mem_smul_finset h1
    rw [mem_stabF.1 hh] at this; simpa using this
  have hSH : S * Hf = S := mul_stabF_eq S
  have hdisj : ∀ a : G, a ∉ S → Disjoint S (a • Hf) := by
    intro a ha
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨h, hh, rfl⟩ := mem_smul_finset.1 hs'
    apply ha
    have hhinv : h⁻¹ ∈ Hf := by rw [hH] at hh ⊢; exact Subgroup.inv_mem _ hh
    rw [← hSH]
    exact mem_mul.2 ⟨a • h, hs, h⁻¹, hhinv, by simp⟩
  refine ⟨hsub, fun h => hε (hsub h), ?_⟩
  -- lower bound from Lemma 2
  have hk := kneser_k hK (qs.map A) (by
    intro B hB; obtain ⟨q, -, rfl⟩ := List.mem_map.1 hB; exact ⟨1, by simp [A]⟩)
  rw [← hSdef, ← hHf, sum_card_A_mul _ Hf hH qs, List.length_map] at hk
  -- upper bound: S, εH, tH are disjoint (εH = tH when δ = 0)
  have hU : S.card + Hf.card * (1 + (if ε⁻¹ * t ∈ Hf then 0 else 1)) ≤ Fintype.card G := by
    split_ifs with hδ
    · have := card_union_of_disjoint (hdisj ε hε)
      rw [card_smul_finset] at this
      have := card_le_univ (S ∪ ε • Hf)
      omega
    · have d2 : Disjoint (ε • Hf) (t • Hf) := disjoint_smul _ Hf hH hδ
      have := card_union_of_disjoint
        (disjoint_union_right.2 ⟨hdisj ε hε, hdisj t ht⟩ : Disjoint S (ε • Hf ∪ t • Hf))
      rw [card_union_of_disjoint d2, card_smul_finset, card_smul_finset] at this
      have := card_le_univ (S ∪ (ε • Hf ∪ t • Hf))
      omega
  have e : (stabF (qs.map A).prod).card *
      ((qs.map (cH (stabF (qs.map A).prod))).sum + 2 +
        (if ε⁻¹ * t ∈ stabF (qs.map A).prod then 0 else 1)) =
      Hf.card + Hf.card * (qs.map (cH Hf)).sum +
        Hf.card * (1 + (if ε⁻¹ * t ∈ Hf then 0 else 1)) := by ring
  rw [e]
  linarith [hk, hU]

/-- **Theorem 3, abstract form, index version.** -/
theorem thm3_abstract_index (hK : KneserHyp G) (qs : List G) {ε t : G}
    (hε : ε ∉ (qs.map A).prod) (ht : t ∉ (qs.map A).prod) :
    (qs.map (cH (stabF (qs.map A).prod))).sum + 2 +
        (if ε⁻¹ * t ∈ stabF (qs.map A).prod then 0 else 1) ≤
      (MulAction.stabilizer G (qs.map A).prod).index := by
  have h := (thm3_abstract hK qs hε ht).2.2
  have hci := Subgroup.card_mul_index (MulAction.stabilizer G (qs.map A).prod)
  rw [← card_stabF, Nat.card_eq_fintype_card] at hci
  have hpos : 0 < (stabF (qs.map A).prod).card := Finset.card_pos.2 ⟨1, one_mem_stabF _⟩
  rw [← hci] at h
  exact Nat.le_of_mul_le_mul_left h hpos

/-! ### Theorem 4 (abstract form) -/

theorem sum_cH_eq (Hf : Finset G) (qs : List G) (h : ∀ q ∈ qs, cH Hf q ≠ 1) :
    (qs.map (cH Hf)).sum = 2 * (qs.filter (fun q => q ∉ Hf)).length := by
  induction qs with
  | nil => simp
  | cons q l ih =>
    have hq := h q (by simp)
    rw [List.map_cons, List.sum_cons, ih (fun r hr => h r (by simp [hr])), List.filter_cons]
    unfold cH at hq ⊢
    by_cases h1 : q ∈ Hf
    · simp [h1]
    · by_cases h2 : q ^ 2 ∈ Hf
      · simp [h1, h2] at hq
      · simp [h1, h2]; ring

/-- **Theorem 4, abstract form.** Assume `|G| = 2n` and that `1, ε` are the only square roots
of `1` in `G` (true in a cyclic group of even order with `ε` of order 2). If `ε, t ∉ S`, then
`h = |stab S|` is odd and divides `n`, no `q_i` lies in `εH`, and
`#{i : q_i ∉ H} + 1 + δ ≤ n / h`. -/
theorem thm4_abstract (hK : KneserHyp G) (qs : List G) {ε t : G} {n : ℕ}
    (hcard : Fintype.card G = 2 * n) (hε2 : orderOf ε = 2)
    (huniq : ∀ g : G, g ^ 2 = 1 → g = 1 ∨ g = ε)
    (hε : ε ∉ (qs.map A).prod) (ht : t ∉ (qs.map A).prod) :
    Odd (stabF (qs.map A).prod).card ∧ (stabF (qs.map A).prod).card ∣ n ∧
    (∀ q ∈ qs, ε * q ∉ stabF (qs.map A).prod) ∧
    (qs.filter (fun q => q ∉ stabF (qs.map A).prod)).length + 1 +
        (if ε⁻¹ * t ∈ stabF (qs.map A).prod then 0 else 1) ≤
      n / (stabF (qs.map A).prod).card := by
  set S := (qs.map A).prod with hSdef
  set Hf := stabF S with hHf
  set H := MulAction.stabilizer G S
  have hH : ∀ g, g ∈ Hf ↔ g ∈ H := mem_stabF_iff
  obtain ⟨hsub, hεH, -⟩ := thm3_abstract hK qs hε ht
  have hidx := thm3_abstract_index hK qs hε ht
  rw [← hSdef, ← hHf] at hidx
  have hcardH : Hf.card = Nat.card H := card_stabF S
  have hodd : Odd Hf.card := by
    rw [hcardH, odd_card_iff_not_mem H hε2 huniq, ← hH]; exact hεH
  have hdvd2 : Hf.card ∣ 2 * n := by
    rw [hcardH, ← hcard, ← Nat.card_eq_fintype_card]; exact Subgroup.card_subgroup_dvd_card H
  have hdvd : Hf.card ∣ n :=
    (Nat.Coprime.dvd_mul_left (Nat.coprime_two_right.2 hodd)).1 hdvd2
  have hSH : S * Hf = S := mul_stabF_eq S
  have item1 : ∀ q ∈ qs, ε * q ∉ Hf := by
    intro q hq hmem
    apply hε
    rw [← hSH]
    exact mem_mul.2 ⟨q⁻¹, inv_mem_prod_A hq, ε * q, hmem, by rw [mul_left_comm, inv_mul_cancel, mul_one]⟩
  have hc1 : ∀ q ∈ qs, cH Hf q ≠ 1 := by
    intro q hq
    unfold cH
    by_cases h1 : q ∈ Hf
    · simp [h1]
    · by_cases h2 : q ^ 2 ∈ Hf
      · exfalso
        apply item1 q hq
        rw [hH] at h1 h2 ⊢
        exact mul_mem_of_sq_mem H (hcardH ▸ hodd) huniq h1 h2
      · simp [h1, h2]
  rw [sum_cH_eq Hf qs hc1] at hidx
  refine ⟨hodd, hdvd, item1, ?_⟩
  -- index = 2 (n / h)
  have hci := Subgroup.card_mul_index H
  rw [← hcardH, Nat.card_eq_fintype_card, hcard] at hci
  obtain ⟨N, hN⟩ := hdvd
  have hpos : 0 < Hf.card := Finset.card_pos.2 ⟨1, one_mem_stabF _⟩
  have hN' : n / Hf.card = N := by rw [hN]; exact Nat.mul_div_cancel_left N hpos
  have hindex : H.index = 2 * N := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hci, hN]; ring
  rw [hN']
  rw [hindex] at hidx
  split_ifs at hidx ⊢ <;> omega

/-! ### Corollary 5 (abstract form) -/

/-- Elements of an odd-order subgroup are squares. -/
theorem isSquare_of_mem_odd (H : Subgroup G) (hodd : Odd (Nat.card H)) {h : G} (hh : h ∈ H) :
    IsSquare h := by
  obtain ⟨j, hj⟩ := hodd
  have h' := congrArg Subtype.val (pow_card_eq_one' (G := H) (x := ⟨h, hh⟩))
  rw [Subgroup.coe_pow, OneMemClass.coe_one] at h'
  refine ⟨h ^ (j + 1), ?_⟩
  rw [← pow_add, show j + 1 + (j + 1) = Nat.card H + 1 by omega, pow_succ, h', one_mul]

/-- The number of `q_i` that are not squares in `G`. -/
def omegaNS (qs : List G) : ℕ := (qs.filter (fun q => ¬ IsSquare q)).length

theorem omegaNS_le (qs : List G) (Hf : Finset G) (hns : ∀ q : G, ¬ IsSquare q → q ∉ Hf) :
    omegaNS qs ≤ (qs.filter (fun q => q ∉ Hf)).length := by
  unfold omegaNS
  exact (List.monotone_filter_right qs (fun q hq => by
    simp only [decide_eq_true_eq] at hq ⊢; exact hns q hq)).length_le

/-- **Corollary 5 (a), (b), abstract form.** With the hypotheses of Theorem 4:
(a) if at least `n` of the `q_i` are non-squares then `ε ∈ S`;
(b) if at least `n - 1` are non-squares and `ε⁻¹ t ≠ 1`, then `ε ∈ S` or `t ∈ S`. -/
theorem cor5_abstract (hK : KneserHyp G) (qs : List G) {ε t : G} {n : ℕ}
    (hcard : Fintype.card G = 2 * n) (hε2 : orderOf ε = 2)
    (huniq : ∀ g : G, g ^ 2 = 1 → g = 1 ∨ g = ε) :
    (n ≤ omegaNS qs → ε ∈ (qs.map A).prod) ∧
    (n ≤ omegaNS qs + 1 → ε⁻¹ * t ≠ 1 → ε ∈ (qs.map A).prod ∨ t ∈ (qs.map A).prod) := by
  have hn : 0 < n := by
    have : 0 < Fintype.card G := Fintype.card_pos
    omega
  -- non-squares lie outside every odd-order stabiliser
  have hns : ∀ (S : Finset G), Odd (stabF S).card → ∀ q : G, ¬ IsSquare q → q ∉ stabF S := by
    intro S hodd q hq hmem
    rw [card_stabF] at hodd
    rw [mem_stabF_iff] at hmem
    exact hq (isSquare_of_mem_odd _ hodd hmem)
  constructor
  · intro hΩ
    by_contra hε
    obtain ⟨hodd, hdvd, -, hb⟩ := thm4_abstract hK qs hcard hε2 huniq hε hε
    have hle := omegaNS_le qs _ (fun q hq => hns _ hodd q hq)
    have : n / (stabF (qs.map A).prod).card ≤ n := Nat.div_le_self _ _
    rw [inv_mul_cancel, ite_eq_left_of_eq_true _ _ (eq_true (one_mem_stabF _))] at hb
    omega
  · intro hΩ hne
    by_contra hc
    push Not at hc
    obtain ⟨hodd, hdvd, -, hb⟩ := thm4_abstract hK qs hcard hε2 huniq hc.1 hc.2
    have hle := omegaNS_le qs _ (fun q hq => hns _ hodd q hq)
    set h := (stabF (qs.map A).prod).card with hh
    have hpos : 0 < h := Finset.card_pos.2 ⟨1, one_mem_stabF _⟩
    by_cases h1 : h = 1
    · -- H = {1}, so δ = 0 forces ε⁻¹ t = 1
      have hsing : stabF (qs.map A).prod = {1} := by
        symm; apply eq_of_subset_of_card_le
        · simpa using one_mem_stabF (qs.map A).prod
        · rw [← hh, h1, card_singleton]
      rw [hsing] at hb hle
      simp only [Finset.mem_singleton] at hle
      rw [h1, Nat.div_one] at hb
      simp only [mem_singleton] at hb
      split_ifs at hb with hδ
      · exact hne hδ
      · omega
    · have h3 : 3 ≤ h := by
        obtain ⟨j, hj⟩ := hodd; omega
      have : n / h < n := lt_of_le_of_lt (Nat.div_le_div_left h3 (by norm_num))
        (Nat.div_lt_self hn (by norm_num))
      split_ifs at hb <;> omega

/-! ### Unconditional versions -/

theorem kneser_k_uncond (As : List (Finset G)) (hne : ∀ A ∈ As, A.Nonempty) :
    (stabF As.prod).card + (As.map (fun A => (A * stabF As.prod).card)).sum ≤
      As.prod.card + As.length * (stabF As.prod).card :=
  kneser_k kneserHyp As hne

end FirstDenominators
