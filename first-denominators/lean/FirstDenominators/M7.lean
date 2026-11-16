import FirstDenominators.Criterion

/-!
# Corollary 6: complete description of `m = 7`

For a prime `p ≡ 1 (mod 4)` and `x = (p + 7)/4`: `x` is **not** good iff `x` has no prime factor
`≡ 6 (mod 7)` and either (i) no prime factor `≡ 3, 5 (mod 7)`, or (ii) no prime factor
`≡ 2, 4, 5 (mod 7)` and exactly one or two prime factors (with multiplicity) `≡ 3 (mod 7)`.

The proof goes through Theorem 1 (`good_iff_isRatio`) and explicit witnesses / residue
computations in `ZMod 7`; it does not use Kneser's theorem.
-/

namespace FirstDenominators

/-- Number of entries of `l` that are `≡ r (mod 7)`. -/
def cnt7 (r : ℕ) (l : List ℕ) : ℕ := (l.filter (fun q => q % 7 = r)).length

/-- The exceptional set of Corollary 6, in terms of the prime factors of `x` with multiplicity. -/
def Bad7 (x : ℕ) : Prop :=
  cnt7 6 x.primeFactorsList = 0 ∧
  (cnt7 3 x.primeFactorsList + cnt7 5 x.primeFactorsList = 0 ∨
    (cnt7 2 x.primeFactorsList + cnt7 4 x.primeFactorsList = 0 ∧ cnt7 5 x.primeFactorsList = 0 ∧
      (cnt7 3 x.primeFactorsList = 1 ∨ cnt7 3 x.primeFactorsList = 2)))

theorem castmod7 (q : ℕ) : (q : ZMod 7) = ((q % 7 : ℕ) : ZMod 7) := (ZMod.natCast_mod q 7).symm

theorem prod7 (l : List ℕ) (h : ∀ q ∈ l, q % 7 ≠ 0) :
    (l.prod : ZMod 7) = 2 ^ cnt7 2 l * 3 ^ cnt7 3 l * 4 ^ cnt7 4 l * 5 ^ cnt7 5 l * 6 ^ cnt7 6 l := by
  induction l with
  | nil => simp [cnt7]
  | cons q l ih =>
    have hq := h q (by simp)
    have ih := ih (fun r hr => h r (by simp [hr]))
    have hr : q % 7 = 1 ∨ q % 7 = 2 ∨ q % 7 = 3 ∨ q % 7 = 4 ∨ q % 7 = 5 ∨ q % 7 = 6 := by omega
    rw [List.prod_cons, Nat.cast_mul, castmod7 q, ih]
    unfold cnt7
    rcases hr with hr | hr | hr | hr | hr | hr <;>
      simp [List.filter_cons, hr, pow_succ] <;> ring

theorem cnt7_le_of_dvd (r : ℕ) {n x : ℕ} (hn : n ∣ x) (hx : x ≠ 0) :
    cnt7 r n.primeFactorsList ≤ cnt7 r x.primeFactorsList :=
  ((Nat.primeFactorsList_sublist_of_dvd hn hx).filter _).length_le

theorem not_mem_of_cnt7_eq_zero {r : ℕ} {l : List ℕ} (h : cnt7 r l = 0) : ∀ q ∈ l, q % 7 ≠ r := by
  intro q hq hr
  have : q ∈ l.filter (fun q => q % 7 = r) := List.mem_filter.2 ⟨hq, by simpa using hr⟩
  rw [cnt7, List.length_eq_zero_iff] at h
  rw [h] at this; simp at this

theorem exists_of_cnt7_pos {r : ℕ} {l : List ℕ} (h : 0 < cnt7 r l) : ∃ q ∈ l, q % 7 = r := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hq
  exact ⟨q, h1, by simpa using h2⟩

theorem length_filter_or7 (a b : ℕ) (hab : a ≠ b) (l : List ℕ) :
    (l.filter (fun q => q % 7 = a ∨ q % 7 = b)).length = cnt7 a l + cnt7 b l := by
  induction l with
  | nil => simp [cnt7]
  | cons q l ih =>
    unfold cnt7 at ih ⊢
    rw [List.filter_cons, List.filter_cons, List.filter_cons]
    split_ifs <;> simp_all <;> omega

/-- Put a factor `≡ 3` into the numerator and a factor `≡ 5` into the denominator. -/
def split7 (q : ℕ) : ℕ × ℕ := if q % 7 = 3 then (q, 1) else (1, q)

theorem split7_mul (q : ℕ) : (split7 q).1 * (split7 q).2 = q := by
  unfold split7; split_ifs <;> simp

/-- If every prime factor of `n` has residue in a multiplicatively closed `K ∋ 1`, so does `n`. -/
theorem res_mem7 (K : Finset (ZMod 7)) (h1 : (1 : ZMod 7) ∈ K)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K) (l : List ℕ) (hl : ∀ q ∈ l, (q : ZMod 7) ∈ K) :
    (l.prod : ZMod 7) ∈ K := by
  induction l with
  | nil => simpa using h1
  | cons q l ih =>
    rw [List.prod_cons, Nat.cast_mul]
    exact hmul _ (hl q (by simp)) _ (ih (fun r hr => hl r (by simp [hr])))

/-- **Corollary 6** (complete description of `m = 7`). -/
theorem m7 {p x : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (hm : 4 * x = p + 7) :
    Good p x ↔ ¬ Bad7 x := by
  have hx : 0 < x := by omega
  have hx0 : x ≠ 0 := hx.ne'
  have hpx : ¬ p ∣ x := fun h => by
    have := Nat.le_of_dvd hx h; have := hp.two_le; omega
  have hpm : p.Coprime 7 := (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hxm := coprime_of_prime hp hpx hm
  have hpZ : (p : ZMod 7) = 4 * x := by
    have := congrArg (Nat.cast (R := ZMod 7)) hm
    push_cast at this
    rw [this, show (7 : ZMod 7) = 0 by decide, add_zero]
  -- residues of divisors of x are nonzero
  have hres : ∀ n, n ∣ x → ∀ q ∈ n.primeFactorsList, q % 7 ≠ 0 := by
    intro n hn q hq h0
    have hq7 : 7 ∣ x := dvd_trans (Nat.dvd_of_mod_eq_zero h0)
      (dvd_trans (Nat.dvd_of_mem_primeFactorsList hq) hn)
    have := Nat.Coprime.coprime_dvd_left hq7 hxm
    norm_num at this
  have hxprod : (x : ZMod 7) = (x.primeFactorsList.prod : ℕ) := by
    rw [Nat.prod_primeFactorsList hx0]
  rw [good_iff_isRatio hp hpx hx hm hpm]
  set l := x.primeFactorsList with hl
  constructor
  · -- a solution excludes both exceptional cases
    intro h hbad
    unfold Bad7 at hbad; rw [← hl] at hbad
    have key : ∃ u v : ℕ, u * v ∣ x ∧
        ((-1 : ZMod 7) * v = u ∨ (-(4 * (x : ZMod 7))) * v = u) := by
      rcases h with ⟨u, v, huv, h⟩ | ⟨u, v, huv, h⟩
      · exact ⟨u, v, huv, Or.inl h⟩
      · exact ⟨u, v, huv, Or.inr (by rw [← hpZ]; exact h)⟩
    obtain ⟨u, v, huv, hg⟩ := key
    have hu : u ∣ x := dvd_trans (dvd_mul_right u v) huv
    have hv : v ∣ x := dvd_trans (dvd_mul_left v u) huv
    have hu0 : u ≠ 0 := fun h => hx0 (Nat.eq_zero_of_zero_dvd (h ▸ hu))
    have hv0 : v ≠ 0 := fun h => hx0 (Nat.eq_zero_of_zero_dvd (h ▸ hv))
    obtain ⟨h6, h35 | ⟨h24, h5, h3⟩⟩ := hbad
    · -- (i): every residue is in {1, 2, 4}
      set K : Finset (ZMod 7) := {1, 2, 4}
      have hK1 : (1 : ZMod 7) ∈ K := by decide
      have hKmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := by decide
      have hin : ∀ n, n ∣ x → n ≠ 0 → (n : ZMod 7) ∈ K := by
        intro n hn hn0
        rw [← Nat.prod_primeFactorsList hn0]
        apply res_mem7 K hK1 hKmul
        intro q hq
        have hql : q ∈ l := (Nat.primeFactorsList_sublist_of_dvd hn hx0).subset hq
        have a3 := not_mem_of_cnt7_eq_zero (by omega : cnt7 3 l = 0) q hql
        have a5 := not_mem_of_cnt7_eq_zero (by omega : cnt7 5 l = 0) q hql
        have a6 := not_mem_of_cnt7_eq_zero h6 q hql
        have a0 := hres n hn q hq
        rw [castmod7 q]
        have : q % 7 = 1 ∨ q % 7 = 2 ∨ q % 7 = 4 := by omega
        rcases this with h' | h' | h' <;> rw [h'] <;> decide
      have hfin : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K,
          (-1 : ZMod 7) * b ≠ a ∧ (-(4 * c)) * b ≠ a := by decide
      have := hfin _ (hin u hu hu0) _ (hin v hv hv0) _ (hin x dvd_rfl hx0)
      rcases hg with hg | hg
      · exact this.1 hg
      · exact this.2 hg
    · -- (ii): residues in {1, 3}, with one or two factors = 3
      have hpow : ∀ n, n ∣ x → n ≠ 0 →
          (n : ZMod 7) = 3 ^ cnt7 3 n.primeFactorsList ∧
            cnt7 3 n.primeFactorsList ≤ cnt7 3 l := by
        intro n hn hn0
        have c2 := cnt7_le_of_dvd 2 hn hx0
        have c4 := cnt7_le_of_dvd 4 hn hx0
        have c5 := cnt7_le_of_dvd 5 hn hx0
        have c6 := cnt7_le_of_dvd 6 hn hx0
        refine ⟨?_, cnt7_le_of_dvd 3 hn hx0⟩
        conv_lhs => rw [← Nat.prod_primeFactorsList hn0]
        rw [prod7 _ (hres n hn)]
        rw [← hl] at c2 c4 c5 c6
        rw [show cnt7 2 n.primeFactorsList = 0 by omega, show cnt7 4 n.primeFactorsList = 0 by omega,
          show cnt7 5 n.primeFactorsList = 0 by omega, show cnt7 6 n.primeFactorsList = 0 by omega]
        ring
      obtain ⟨eu, cu⟩ := hpow u hu hu0
      obtain ⟨ev, cv⟩ := hpow v hv hv0
      obtain ⟨ex, -⟩ := hpow x dvd_rfl hx0
      rw [eu, ev, ex] at hg
      rw [← hl] at hg
      have hfin : ∀ c ∈ ({1, 2} : Finset ℕ), ∀ a ∈ Finset.range (c + 1),
          ∀ b ∈ Finset.range (c + 1),
          (-1 : ZMod 7) * 3 ^ b ≠ 3 ^ a ∧ (-(4 * 3 ^ c)) * (3 : ZMod 7) ^ b ≠ 3 ^ a := by decide
      have hc : cnt7 3 l ∈ ({1, 2} : Finset ℕ) := by
        rcases h3 with h' | h' <;> simp [h']
      have := hfin (cnt7 3 l) hc (cnt7 3 u.primeFactorsList) (Finset.mem_range.2 (by omega))
        (cnt7 3 v.primeFactorsList) (Finset.mem_range.2 (by omega))
      rcases hg with hg | hg
      · exact this.1 hg
      · exact this.2 hg
  · -- outside the exceptional set a solution exists
    intro hnb
    unfold Bad7 at hnb; rw [← hl] at hnb
    have hdl : ∀ q ∈ l, q ∣ x := fun q hq => Nat.dvd_of_mem_primeFactorsList hq
    by_cases h6 : 0 < cnt7 6 l
    · obtain ⟨q, hq, hr⟩ := exists_of_cnt7_pos h6
      left
      refine ⟨q, 1, by simpa using hdl q hq, ?_⟩
      rw [castmod7 q, hr]; decide
    by_cases h35 : 3 ≤ cnt7 3 l + cnt7 5 l
    · -- three factors = 3 or 5 (with multiplicity)
      left
      rw [← length_filter_or7 3 5 (by norm_num)] at h35
      set F := l.filter (fun q => q % 7 = 3 ∨ q % 7 = 5) with hF
      obtain ⟨a, b, c, rest, hFm⟩ : ∃ a b c rest, F = a :: b :: c :: rest := by
        match F, h35 with
        | a :: b :: c :: rest, _ => exact ⟨a, b, c, rest, rfl⟩
      · have hsub : List.Sublist [a, b, c] l := by
          have h1 : List.Sublist [a, b, c] F := by
            rw [hFm]; exact List.sublist_append_left [a, b, c] rest
          exact h1.trans List.filter_sublist
        have habc : a * b * c ∣ x := by
          have := hsub.prod_dvd_prod
          rw [hl, Nat.prod_primeFactorsList hx0] at this
          simpa [mul_assoc] using this
        have hmemF : ∀ q ∈ [a, b, c], q % 7 = 3 ∨ q % 7 = 5 := by
          intro q hq
          have : q ∈ F := by rw [hFm]; simp at hq ⊢; tauto
          simpa using (List.mem_filter.1 this).2
        have ha := hmemF a (by simp)
        have hb := hmemF b (by simp)
        have hc := hmemF c (by simp)
        let f := split7
        have hf : ∀ q, (f q).1 * (f q).2 = q := split7_mul
        refine ⟨(f a).1 * (f b).1 * (f c).1, (f a).2 * (f b).2 * (f c).2, ?_, ?_⟩
        · have : (f a).1 * (f b).1 * (f c).1 * ((f a).2 * (f b).2 * (f c).2) = a * b * c := by
            calc _ = ((f a).1 * (f a).2) * ((f b).1 * (f b).2) * ((f c).1 * (f c).2) := by ring
              _ = a * b * c := by rw [hf a, hf b, hf c]
          rw [this]; exact habc
        · simp only [f, split7]
          rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
            simp [ha, hb, hc] <;> rw [castmod7 a, castmod7 b, castmod7 c] <;>
            simp [ha, hb, hc] <;> decide
    by_cases h24 : 0 < cnt7 3 l + cnt7 5 l ∧ 0 < cnt7 2 l + cnt7 4 l
    · left
      rw [← length_filter_or7 3 5 (by norm_num)] at h24
      rw [← length_filter_or7 2 4 (by norm_num)] at h24
      obtain ⟨q1, hq1⟩ := List.exists_mem_of_length_pos h24.1
      obtain ⟨q2, hq2⟩ := List.exists_mem_of_length_pos h24.2
      obtain ⟨hq1l, hr1⟩ := List.mem_filter.1 hq1
      obtain ⟨hq2l, hr2⟩ := List.mem_filter.1 hq2
      simp only [decide_eq_true_eq] at hr1 hr2
      have hne : q1 ≠ q2 := by rintro rfl; omega
      have h12 : q1 * q2 ∣ x :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd
          ((Nat.coprime_primes (Nat.prime_of_mem_primeFactorsList hq1l)
            (Nat.prime_of_mem_primeFactorsList hq2l)).2 hne) (hdl q1 hq1l) (hdl q2 hq2l)
      have e1 := castmod7 q1
      have e2 := castmod7 q2
      rcases hr1 with hr1 | hr1 <;> rcases hr2 with hr2 | hr2 <;> rw [hr1] at e1 <;> rw [hr2] at e2
      · exact ⟨q1 * q2, 1, by simpa using h12, by push_cast; rw [e1, e2]; decide⟩
      · exact ⟨q1, q2, h12, by rw [e1, e2]; decide⟩
      · exact ⟨q2, q1, by rwa [mul_comm], by rw [e1, e2]; decide⟩
      · exact ⟨1, q1 * q2, by simpa using h12, by push_cast; rw [e1, e2]; decide⟩
    · -- remaining case: the second target -p
      right
      have h6' : cnt7 6 l = 0 := by omega
      have hb' : cnt7 2 l + cnt7 4 l = 0 := by
        by_contra hc
        apply hnb; refine ⟨h6', Or.inl ?_⟩
        by_contra hc'; exact h24 ⟨by omega, by omega⟩
      have h5 : 0 < cnt7 5 l := by
        by_contra hc
        apply hnb
        refine ⟨h6', ?_⟩
        by_cases h0 : cnt7 3 l + cnt7 5 l = 0
        · exact Or.inl h0
        · exact Or.inr ⟨hb', by omega, by omega⟩
      obtain ⟨q5, hq5, hr5⟩ := exists_of_cnt7_pos h5
      have e5 : (q5 : ZMod 7) = 5 := by rw [castmod7, hr5]; rfl
      have hxZ : (x : ZMod 7) = 3 ^ cnt7 3 l * 5 ^ cnt7 5 l := by
        rw [hxprod, prod7 _ (hres x dvd_rfl), ← hl,
          show cnt7 2 l = 0 by omega, show cnt7 4 l = 0 by omega, h6']
        ring
      rw [hpZ, hxZ]
      have hq5x := hdl q5 hq5
      have : (cnt7 3 l = 0 ∧ cnt7 5 l = 1) ∨ (cnt7 3 l = 1 ∧ cnt7 5 l = 1) ∨
          (cnt7 3 l = 0 ∧ cnt7 5 l = 2) := by omega
      rcases this with ⟨h3, h5'⟩ | ⟨h3, h5'⟩ | ⟨h3, h5'⟩ <;> rw [h3, h5']
      · exact ⟨1, 1, by simp, by decide⟩
      · exact ⟨1, q5, by simpa using hq5x, by rw [e5]; decide⟩
      · exact ⟨q5, 1, by simpa using hq5x, by rw [e5]; decide⟩

end FirstDenominators
