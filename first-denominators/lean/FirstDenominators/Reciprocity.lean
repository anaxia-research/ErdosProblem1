import FirstDenominators.Main

/-!
# Reciprocity step of Corollary 5 (FirstDenominators Lemma 3.1)

For `p ≡ 1 (mod 4)` prime, `4x = p + m` and a prime `q ∣ x`: `(q/m) = (q/p)` (Jacobi = Legendre).
Hence a prime factor of `x` that is a non-residue mod `p` is a non-square in `(ZMod m)ˣ`, and
Corollary 5 holds with `Ω_N(x)` = number of prime factors of `x` (with multiplicity) that are
quadratic non-residues mod `p`.
-/

namespace FirstDenominators

open Pointwise

theorem jacobi_eq_legendre {p x m q : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) (hm : 4 * x = p + m)
    (hq : q.Prime) (hqx : q ∣ x) : jacobiSym q m = legendreSym p q := by
  rw [jacobiSym.legendreSym.to_jacobiSym]
  have hm4 : m % 4 = 3 := by omega
  have hmodd : Odd m := Nat.odd_iff.2 (by omega)
  obtain ⟨y, rfl⟩ := hqx
  rcases hq.eq_two_or_odd' with rfl | hqodd
  · -- q = 2: compare χ₈ m and χ₈ p, using m ≡ -p (mod 8)
    have hpodd : Odd p := Nat.odd_iff.2 (by omega)
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, jacobiSym.at_two hmodd, jacobiSym.at_two hpodd,
      ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight]
    have : (m + p) % 8 = 0 := by omega
    have h1 : m % 2 = 1 := by omega
    have h2 : p % 2 = 1 := by omega
    simp only [h1, h2]
    have : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
    rcases this with h | h | h | h <;> simp [h] <;> omega
  · -- q odd: two applications of reciprocity
    have hqm : jacobiSym (q : ℤ) m = jacobiSym (p : ℤ) q := by
      have hJ : jacobiSym (m : ℤ) q = jacobiSym (-1) q * jacobiSym (p : ℤ) q := by
        rw [← jacobiSym.mul_left]
        apply jacobiSym.mod_left'
        rw [neg_one_mul]
        apply Int.emod_eq_emod_iff_emod_sub_eq_zero.2
        have : (m : ℤ) - -(p : ℤ) = q * (4 * y) := by
          have := congrArg (Nat.cast (R := ℤ)) hm; push_cast at this; linarith
        rw [this]; simp
      rw [jacobiSym.at_neg_one hqodd] at hJ
      rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hqodd) with h | h
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four h hmodd, hJ, ZMod.χ₄_nat_one_mod_four h,
          one_mul]
      · rw [jacobiSym.quadratic_reciprocity_three_mod_four h hm4, hJ,
          ZMod.χ₄_nat_three_mod_four h]; ring
    rw [hqm, jacobiSym.quadratic_reciprocity_one_mod_four hp4 hqodd]

/-- A prime factor of `x` that is a non-residue mod `p` is a non-square in `(ZMod m)ˣ`. -/
theorem not_isSquare_toU {p x m q : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) (hm : 4 * x = p + m)
    (hq : q.Prime) (hqx : q ∣ x) (hqm : q.Coprime m) (hleg : legendreSym p q = -1) :
    ¬ IsSquare (toU m q) := by
  rintro ⟨r, hr⟩
  have hJ : jacobiSym (q : ℤ) m = -1 := by rw [jacobi_eq_legendre hp4 hm hq hqx]; exact hleg
  apply ZMod.nonsquare_of_jacobiSym_eq_neg_one hJ
  refine ⟨(r : ZMod m), ?_⟩
  have := congrArg Units.val hr
  rw [coe_toU hqm, Units.val_mul] at this
  simpa using this

/-- `Ω_N(x)`: prime factors of `x`, with multiplicity, that are non-residues mod `p`
(Jacobi symbol `(q/p)`, which is the Legendre symbol since `p` is prime). -/
def omegaN (p x : ℕ) : ℕ :=
  (x.primeFactorsList.filter (fun q : ℕ => jacobiSym (q : ℤ) p = -1)).length

theorem length_filter_le_of_imp {α : Type*} (l : List α) (P Q : α → Bool)
    (h : ∀ a ∈ l, P a = true → Q a = true) : (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun b hb => h b (by simp [hb]))
    simp only [List.filter_cons]
    by_cases hP : P a = true
    · have hQ := h a (by simp) hP
      simp [hP, hQ]; omega
    · by_cases hQ : Q a = true <;> simp [hP, hQ] <;> omega

theorem omegaN_le {p x m : ℕ} [Fact p.Prime] [NeZero m] (hp4 : p % 4 = 1) (hm : 4 * x = p + m)
    (hxm : x.Coprime m) : omegaN p x ≤ omegaNS (qsOf m x) := by
  unfold omegaN omegaNS qsOf
  rw [List.filter_map, List.length_map]
  apply length_filter_le_of_imp
  intro q hq hleg
  simp only [Function.comp, decide_eq_true_eq] at hleg ⊢
  exact not_isSquare_toU hp4 hm (Nat.prime_of_mem_primeFactorsList hq)
    (Nat.dvd_of_mem_primeFactorsList hq)
    (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactorsList hq) hxm)
    (by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hleg)

/-- **Corollary 5 (a), (b)** with `Ω_N(x)` as in the paper (`m = ℓ^j`, `n = φ(m)/2`). -/
theorem corollary5_legendre {p x ℓ j : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hj : 0 < j) (hx : 0 < x) (hm : 4 * x = p + ℓ ^ j) (hxm : x.Coprime (ℓ ^ j))
    (hpm : p.Coprime (ℓ ^ j)) [NeZero (ℓ ^ j)] :
    ((ℓ ^ j).totient / 2 ≤ omegaN p x → IsRatio (ℓ ^ j) x (-1) ∧ Good p x) ∧
    ((ℓ ^ j).totient / 2 ≤ omegaN p x + 1 → (p : ZMod (ℓ ^ j)) ≠ 1 → Good p x) := by
  have hle := omegaN_le (m := ℓ ^ j) hp4 hm hxm
  have c := corollary5 hℓ hℓ2 hj (Fact.out : p.Prime).pos hx hm hxm hpm
  exact ⟨fun h => c.1 (le_trans h hle), fun h => c.2 (by omega)⟩

theorem toU_eq_one_iff {m q : ℕ} (hm1 : 1 < m) (hq : q.Coprime m) : toU m q = 1 ↔ q % m = 1 := by
  rw [Units.ext_iff, coe_toU hq, Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt hm1]

/-- **Corollary 5 (c)** (stated for `m = ℓ^j`; the paper takes `j = 1`): if `n = φ(m)/2` is prime
and `x` has a prime factor that is a non-residue mod `p`, then `x` is good as soon as it has at
least `n` prime factors (with multiplicity) `≢ 1 (mod m)`, or at least `n - 1` of them and
`p ≢ 1 (mod m)`. -/
theorem corollary5c {p x ℓ j : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hj : 0 < j) (hn : ((ℓ ^ j).totient / 2).Prime) (hx : 0 < x)
    (hm : 4 * x = p + ℓ ^ j) (hxm : x.Coprime (ℓ ^ j)) (hpm : p.Coprime (ℓ ^ j))
    [NeZero (ℓ ^ j)] (hN : 1 ≤ omegaN p x) :
    ((ℓ ^ j).totient / 2 ≤ (x.primeFactorsList.filter (fun q => q % ℓ ^ j ≠ 1)).length →
      Good p x) ∧
    ((ℓ ^ j).totient / 2 ≤ (x.primeFactorsList.filter (fun q => q % ℓ ^ j ≠ 1)).length + 1 →
      (p : ZMod (ℓ ^ j)) ≠ 1 → Good p x) := by
  set n := (ℓ ^ j).totient / 2 with hndef
  set cnt := (x.primeFactorsList.filter (fun q => q % ℓ ^ j ≠ 1)).length with hcnt
  have hm1 : 1 < ℓ ^ j := Nat.one_lt_pow hj.ne' hℓ.one_lt
  have key : ¬ Good p x → cnt + 1 + (if toU (ℓ ^ j) p = 1 then 0 else 1) ≤ n := by
    intro hng
    obtain ⟨hodd, hdvd, -, hb⟩ := theorem4 hℓ hℓ2 hj (Fact.out : p.Prime).pos hx hm hxm hpm hng
    rw [ratioSet_eq_qs hx hxm] at hodd hdvd hb
    set Hf := stabF ((qsOf (ℓ ^ j) x).map A).prod with hHf
    have hns : ∀ q : (ZMod (ℓ ^ j))ˣ, ¬ IsSquare q → q ∉ Hf := by
      intro q hq hmem
      rw [card_stabF] at hodd
      rw [mem_stabF_iff] at hmem
      exact hq (isSquare_of_mem_odd _ hodd hmem)
    have hk : 1 ≤ ((qsOf (ℓ ^ j) x).filter (fun q => q ∉ Hf)).length :=
      le_trans hN (le_trans (omegaN_le hp4 hm hxm) (omegaNS_le _ Hf hns))
    rcases (Nat.dvd_prime hn).1 hdvd with h1 | h1
    · have hsing : Hf = {1} := by
        symm; apply Finset.eq_of_subset_of_card_le
        · simpa using one_mem_stabF ((qsOf (ℓ ^ j) x).map A).prod
        · rw [h1, Finset.card_singleton]
      rw [hsing, Finset.card_singleton, Nat.div_one] at hb
      simp only [Finset.mem_singleton] at hb
      have e : ((qsOf (ℓ ^ j) x).filter (fun q => q ∉ ({1} : Finset (ZMod (ℓ ^ j))ˣ))).length
          = cnt := by
        rw [hcnt, qsOf, List.filter_map, List.length_map]
        congr 1
        apply List.filter_congr
        intro q hq
        have hqc := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactorsList hq) hxm
        simp [toU_eq_one_iff hm1 hqc]
      simp only [Finset.mem_singleton] at e
      rw [e] at hb
      exact hb
    · rw [h1, Nat.div_self (hn.pos)] at hb
      split_ifs at hb <;> omega
  constructor
  · intro h; by_contra hng; have := key hng; split_ifs at this <;> omega
  · intro h hp1; by_contra hng
    have := key hng
    have hne : toU (ℓ ^ j) p ≠ 1 := by
      intro e; apply hp1; rw [← coe_toU hpm, e, Units.val_one]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)] at this
    omega

end FirstDenominators
