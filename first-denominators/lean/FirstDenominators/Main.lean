import FirstDenominators.Kneser

/-!
# Theorems 3, 4 and Corollary 5 for the Erdős–Straus first denominators (unconditional)

Setting: `p, x, m` with `4x = p + m`, `gcd(x, m) = gcd(p, m) = 1`, `G = (ZMod m)ˣ`,
`R(x) = ratioSet m x`, `H = stab R(x)` (as the finset `stabF (ratioSet m x)`), and
`qsOf m x` = the prime factors of `x`, with multiplicity, as elements of `G`.
Kneser's theorem is used through `kneserHyp` (vendored `Finset.mul_kneser`).
-/

namespace FirstDenominators

open Pointwise Finset

/-- The prime factors of `x`, with multiplicity, as units modulo `m`. -/
def qsOf (m x : ℕ) : List (ZMod m)ˣ := x.primeFactorsList.map (toU m)

theorem ratioSet_eq_qs {m x : ℕ} [NeZero m] (hx : 0 < x) (hxm : x.Coprime m) :
    ratioSet m x = ((qsOf m x).map A).prod := by
  rw [ratioSet_eq_prod hx hxm, qsOf, List.map_map]; rfl

/-- A bad `x` has `-1 ∉ R(x)` and `-p ∉ R(x)` (easy direction of Theorem 1). -/
theorem not_mem_of_not_good {p x m : ℕ} [NeZero m] (hp : 0 < p) (hx : 0 < x)
    (hm : 4 * x = p + m) (hpm : p.Coprime m) (hng : ¬ Good p x) :
    (-1 : (ZMod m)ˣ) ∉ ratioSet m x ∧ -(toU m p) ∉ ratioSet m x := by
  constructor
  · intro h; apply hng; apply good_of_isRatio hp hx hm; left
    simpa using mem_ratioSet.1 h
  · intro h; apply hng; apply good_of_isRatio hp hx hm; right
    simpa [coe_toU hpm] using mem_ratioSet.1 h

theorem neg_one_inv_mul_neg {m : ℕ} (u : (ZMod m)ˣ) : (-1 : (ZMod m)ˣ)⁻¹ * -u = u := by simp

/-- **Theorem 3** (inverse theorem, every `m`). If `x` is not good, then `H ⊂ R(x)`, `-1 ∉ H`
and `Σ_{q | x} v_q c_H(q) ≤ [G : H] - 2 - δ`, with `δ = 0` iff `p ∈ H`. -/
theorem theorem3 {p x m : ℕ} [NeZero m] (hp : 0 < p) (hx : 0 < x) (hm : 4 * x = p + m)
    (hxm : x.Coprime m) (hpm : p.Coprime m) (hng : ¬ Good p x) :
    stabF (ratioSet m x) ⊆ ratioSet m x ∧ (-1 : (ZMod m)ˣ) ∉ stabF (ratioSet m x) ∧
    ((qsOf m x).map (cH (stabF (ratioSet m x)))).sum + 2 +
        (if toU m p ∈ stabF (ratioSet m x) then 0 else 1) ≤
      (MulAction.stabilizer (ZMod m)ˣ (ratioSet m x)).index := by
  obtain ⟨h1, h2⟩ := not_mem_of_not_good hp hx hm hpm hng
  rw [ratioSet_eq_qs hx hxm] at h1 h2 ⊢
  have a := thm3_abstract kneserHyp (qsOf m x) h1 h2
  have b := thm3_abstract_index kneserHyp (qsOf m x) h1 h2
  rw [neg_one_inv_mul_neg] at b
  exact ⟨a.1, a.2.1, b⟩

/-- In `(ZMod ℓ^j)ˣ`, `ℓ` an odd prime, the only square roots of `1` are `±1`, and `-1` has
order `2` (the group is cyclic of even order). -/
theorem units_prime_pow_facts {ℓ j : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 0 < j) :
    orderOf (-1 : (ZMod (ℓ ^ j))ˣ) = 2 ∧
    ∀ g : (ZMod (ℓ ^ j))ˣ, g ^ 2 = 1 → g = 1 ∨ g = -1 := by
  have h3 : 2 < ℓ ^ j := by
    have : 3 ≤ ℓ := by have := hℓ.two_le; omega
    calc 2 < ℓ := by omega
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ j := Nat.pow_le_pow_right hℓ.pos hj
  have : Fact (2 < ℓ ^ j) := ⟨h3⟩
  have : NeZero (ℓ ^ j) := ⟨by omega⟩
  have hcyc := ZMod.isCyclic_units_of_prime_pow ℓ hℓ hℓ2 j
  have hne : (-1 : (ZMod (ℓ ^ j))ˣ) ≠ 1 := by
    intro h; apply ZMod.neg_one_ne_one (n := ℓ ^ j)
    simpa using congrArg Units.val h
  have hsq : (-1 : (ZMod (ℓ ^ j))ˣ) ^ 2 = 1 := by simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨orderOf_eq_prime hsq hne, isCyclic_sq_eq_one hsq hne⟩

theorem card_units_prime_pow {ℓ j : ℕ} [NeZero (ℓ ^ j)] (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 0 < j) :
    Fintype.card (ZMod (ℓ ^ j))ˣ = 2 * ((ℓ ^ j).totient / 2) := by
  have h3 : 2 < ℓ ^ j := by
    have : 3 ≤ ℓ := by have := hℓ.two_le; omega
    calc 2 < ℓ := by omega
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ j := Nat.pow_le_pow_right hℓ.pos hj
  rw [ZMod.card_units_eq_totient, Nat.two_mul_div_two_of_even (Nat.totient_even h3)]

/-- **Theorem 4** (prime-power `m = ℓ^j`, `n = φ(m)/2`). If `x` is not good, then
`h = |H|` is odd and divides `n`, no prime factor of `x` lies in `-H`, and the number of prime
factors of `x` (with multiplicity) outside `H` is at most `n/h - 1 - δ`. -/
theorem theorem4 {p x ℓ j : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 0 < j) (hp : 0 < p)
    (hx : 0 < x) (hm : 4 * x = p + ℓ ^ j) (hxm : x.Coprime (ℓ ^ j)) (hpm : p.Coprime (ℓ ^ j))
    (hng : ¬ Good p x) [NeZero (ℓ ^ j)] :
    Odd (stabF (ratioSet (ℓ ^ j) x)).card ∧
    (stabF (ratioSet (ℓ ^ j) x)).card ∣ (ℓ ^ j).totient / 2 ∧
    (∀ q ∈ qsOf (ℓ ^ j) x, -1 * q ∉ stabF (ratioSet (ℓ ^ j) x)) ∧
    ((qsOf (ℓ ^ j) x).filter (fun q => q ∉ stabF (ratioSet (ℓ ^ j) x))).length + 1 +
        (if toU (ℓ ^ j) p ∈ stabF (ratioSet (ℓ ^ j) x) then 0 else 1) ≤
      ((ℓ ^ j).totient / 2) / (stabF (ratioSet (ℓ ^ j) x)).card := by
  obtain ⟨h1, h2⟩ := not_mem_of_not_good hp hx hm hpm hng
  obtain ⟨hord, huniq⟩ := units_prime_pow_facts hℓ hℓ2 hj
  rw [ratioSet_eq_qs hx hxm] at h1 h2 ⊢
  have r := thm4_abstract kneserHyp (qsOf (ℓ ^ j) x) (card_units_prime_pow hℓ hℓ2 hj) hord huniq
    h1 h2
  rw [neg_one_inv_mul_neg] at r
  exact r

/-- **Theorem 4, first-kind variant**: if only `-1 ∉ R(x)` is assumed, items 1 and 2 hold with
`δ = 0`. -/
theorem theorem4_first_kind {x ℓ j : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 0 < j)
    (hx : 0 < x) (hxm : x.Coprime (ℓ ^ j)) [NeZero (ℓ ^ j)]
    (hng : ¬ IsRatio (ℓ ^ j) x (-1)) :
    Odd (stabF (ratioSet (ℓ ^ j) x)).card ∧
    (stabF (ratioSet (ℓ ^ j) x)).card ∣ (ℓ ^ j).totient / 2 ∧
    (∀ q ∈ qsOf (ℓ ^ j) x, -1 * q ∉ stabF (ratioSet (ℓ ^ j) x)) ∧
    ((qsOf (ℓ ^ j) x).filter (fun q => q ∉ stabF (ratioSet (ℓ ^ j) x))).length + 1 ≤
      ((ℓ ^ j).totient / 2) / (stabF (ratioSet (ℓ ^ j) x)).card := by
  have h1 : (-1 : (ZMod (ℓ ^ j))ˣ) ∉ ratioSet (ℓ ^ j) x := by
    intro h; apply hng; simpa using mem_ratioSet.1 h
  obtain ⟨hord, huniq⟩ := units_prime_pow_facts hℓ hℓ2 hj
  rw [ratioSet_eq_qs hx hxm] at h1 ⊢
  have r := thm4_abstract kneserHyp (qsOf (ℓ ^ j) x) (card_units_prime_pow hℓ hℓ2 hj) hord huniq
    h1 h1
  rw [inv_mul_cancel, ite_eq_left_of_eq_true _ _ (eq_true (one_mem_stabF _)), add_zero] at r
  exact r

/-- **Corollary 5 (a), (b)** (prime-power `m = ℓ^j`, `n = φ(m)/2`; `Ω'` = number of prime
factors of `x`, with multiplicity, that are non-squares mod `m`).
(a) `Ω' ≥ n` gives a solution of the first kind (`-1 ∈ R(x)`), hence `x` is good;
(b) `Ω' ≥ n - 1` and `p ≢ 1 (mod m)` give that `x` is good. -/
theorem corollary5 {p x ℓ j : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 0 < j) (hp : 0 < p)
    (hx : 0 < x) (hm : 4 * x = p + ℓ ^ j) (hxm : x.Coprime (ℓ ^ j)) (hpm : p.Coprime (ℓ ^ j))
    [NeZero (ℓ ^ j)] :
    ((ℓ ^ j).totient / 2 ≤ omegaNS (qsOf (ℓ ^ j) x) → IsRatio (ℓ ^ j) x (-1) ∧ Good p x) ∧
    ((ℓ ^ j).totient / 2 ≤ omegaNS (qsOf (ℓ ^ j) x) + 1 → (p : ZMod (ℓ ^ j)) ≠ 1 →
      Good p x) := by
  obtain ⟨hord, huniq⟩ := units_prime_pow_facts hℓ hℓ2 hj
  have c := cor5_abstract kneserHyp (qsOf (ℓ ^ j) x) (t := -(toU (ℓ ^ j) p))
    (card_units_prime_pow hℓ hℓ2 hj) hord huniq
  rw [← ratioSet_eq_qs hx hxm, neg_one_inv_mul_neg] at c
  have g1 : (-1 : (ZMod (ℓ ^ j))ˣ) ∈ ratioSet (ℓ ^ j) x → IsRatio (ℓ ^ j) x (-1) := by
    intro h; simpa using mem_ratioSet.1 h
  refine ⟨fun h => ⟨g1 (c.1 h), good_of_isRatio hp hx hm (Or.inl (g1 (c.1 h)))⟩, ?_⟩
  intro h hp1
  have hne : toU (ℓ ^ j) p ≠ 1 := by
    intro e; apply hp1; rw [← coe_toU hpm, e, Units.val_one]
  rcases c.2 h hne with h' | h'
  · exact good_of_isRatio hp hx hm (Or.inl (g1 h'))
  · exact good_of_isRatio hp hx hm (Or.inr (by simpa [coe_toU hpm] using mem_ratioSet.1 h'))

/-- **Subgroup obstruction** (FirstDenominators Prop. 3.4): if every prime factor of `x` lies in
a subgroup `K` of `(ZMod m)ˣ` with `-1 ∉ K` and `-p ∉ K`, then `x` is not good. -/
theorem not_good_of_subgroup {p x m : ℕ} [NeZero m] (hp : p.Prime) (hpx : ¬ p ∣ x) (hx : 0 < x)
    (hm : 4 * x = p + m) (hpm : p.Coprime m) (K : Subgroup (ZMod m)ˣ)
    (hK : ∀ q ∈ qsOf m x, q ∈ K) (h1 : (-1 : (ZMod m)ˣ) ∉ K) (h2 : -(toU m p) ∉ K) :
    ¬ Good p x := by
  have hxm := coprime_of_prime hp hpx hm
  have hsub : ∀ l : List (ZMod m)ˣ, (∀ q ∈ l, q ∈ K) → ∀ g ∈ (l.map A).prod, g ∈ K := by
    intro l
    induction l with
    | nil => intro _ g hg; simp at hg; rw [hg]; exact K.one_mem
    | cons q l ih =>
      intro hl g hg
      rw [List.map_cons, List.prod_cons] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.1 hg
      have hq := hl q (by simp)
      refine K.mul_mem ?_ (ih (fun r hr => hl r (by simp [hr])) b hb)
      rcases mem_A.1 ha with rfl | rfl | rfl
      · exact K.inv_mem hq
      · exact K.one_mem
      · exact hq
  intro hg
  rcases isRatio_of_good hp hpx hx hm hpm hg with h | h
  · apply h1
    apply hsub _ hK
    rw [← ratioSet_eq_qs hx hxm, mem_ratioSet]; simpa using h
  · apply h2
    apply hsub _ hK
    rw [← ratioSet_eq_qs hx hxm, mem_ratioSet]; simpa [coe_toU hpm] using h

/-- **`m = 3`** (Corollary 5 for `n = 1`, FirstDenominators Cor. 3.3): for a prime `p ≠ 3` and
`x = (p+3)/4`, `x` is good iff `p ≡ 2 (mod 3)` or `x` has a prime factor `≡ 2 (mod 3)`. -/
theorem m3 {p x : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hm : 4 * x = p + 3) :
    Good p x ↔ (p % 3 = 2 ∨ ∃ q ∈ x.primeFactorsList, q % 3 = 2) := by
  have hx : 0 < x := by omega
  have hpx : ¬ p ∣ x := fun h => by
    have := Nat.le_of_dvd hx h; have := hp.two_le; omega
  have hpm : p.Coprime 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  rw [good_iff_isRatio hp hpx hx hm hpm]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hp2, hq⟩ := hc
    have hxm := coprime_of_prime hp hpx hm
    -- every prime factor of x is 1 mod 3, so R(x) = {1}
    have hall : ∀ q ∈ x.primeFactorsList, toU 3 q = 1 := by
      intro q hq'
      have hqc : q.Coprime 3 :=
        Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactorsList hq') hxm
      have h1 : q % 3 = 1 := by
        have := hq q hq'
        have h0 : q % 3 ≠ 0 := by
          intro h0; have := Nat.dvd_of_mod_eq_zero h0
          rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three] at hqc
          exact hqc this
        omega
      ext; rw [coe_toU hqc, Units.val_one, ← ZMod.natCast_mod, h1]; rfl
    have hR : ratioSet 3 x = {1} := by
      rw [ratioSet_eq_prod hx hxm]
      generalize x.primeFactorsList = L at hall
      induction L with
      | nil => rfl
      | cons q L ih =>
        rw [List.map_cons, List.prod_cons, hall q (by simp),
          ih (fun r hr => hall r (by simp [hr]))]
        decide
    have hp1 : p % 3 = 1 := by
      have : p % 3 ≠ 0 := by
        intro h0; have := Nat.dvd_of_mod_eq_zero h0
        exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
      omega
    rcases h with ⟨u, v, huv, h⟩ | ⟨u, v, huv, h⟩
    · have hm' : (-1 : (ZMod 3)ˣ) ∈ ratioSet 3 x := mem_ratioSet.2 ⟨u, v, huv, by simpa using h⟩
      rw [hR] at hm'; revert hm'; decide
    · have hpv : (p : ZMod 3) = 1 := by rw [← ZMod.natCast_mod, hp1]; rfl
      have hm' : (-1 : (ZMod 3)ˣ) ∈ ratioSet 3 x :=
        mem_ratioSet.2 ⟨u, v, huv, by rw [hpv] at h; simpa using h⟩
      rw [hR] at hm'; revert hm'; decide
  · rintro (h | ⟨q, hq, h⟩)
    · right; refine ⟨1, 1, by simp, ?_⟩
      have : (p : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h]; rfl
      rw [this]; decide
    · left; refine ⟨q, 1, by simpa using Nat.dvd_of_mem_primeFactorsList hq, ?_⟩
      have : (q : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h]; rfl
      rw [this]; decide

end FirstDenominators
