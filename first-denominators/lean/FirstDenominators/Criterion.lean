import FirstDenominators.Identities

/-!
# Theorem 1: the ratio criterion

`IsRatio m x g` says that `g ≡ u/v (mod m)` for some `u, v` with `u v ∣ x`, written without
inverses as `g * v = u` in `ZMod m`.  This is the set `R(x)` of the paper (coprimality of `u, v`
is not needed: dividing both by their gcd gives the same ratio).

`good_iff_isRatio` : for a prime `p ∤ x` with `4x = p + m` and `gcd(p, m) = 1`,
`x` is good for `p` iff `-1 ∈ R(x)` or `-p ∈ R(x)`.
-/

namespace FirstDenominators

/-- `g ∈ R(x)` modulo `m`. -/
def IsRatio (m x : ℕ) (g : ZMod m) : Prop := ∃ u v : ℕ, u * v ∣ x ∧ g * v = u

instance (m x : ℕ) : DecidablePred (IsRatio m x) := fun g =>
  decidable_of_iff (x = 0 ∨ ∃ u ∈ x.divisors, ∃ v ∈ x.divisors, u * v ∣ x ∧ g * v = u) (by
    constructor
    · rintro (rfl | ⟨u, -, v, -, h⟩)
      · exact ⟨0, 0, dvd_refl 0, by simp⟩
      · exact ⟨u, v, h⟩
    · rintro ⟨u, v, huv, h⟩
      by_cases hx : x = 0
      · exact Or.inl hx
      · refine Or.inr ⟨u, Nat.mem_divisors.2 ⟨dvd_trans (dvd_mul_right u v) huv, hx⟩, v,
          Nat.mem_divisors.2 ⟨dvd_trans (dvd_mul_left v u) huv, hx⟩, huv, h⟩)

theorem coprime_of_prime {p x m : ℕ} (hp : p.Prime) (hpx : ¬ p ∣ x) (hm : 4 * x = p + m) :
    Nat.Coprime x m := by
  have h1 : Nat.gcd x m ∣ p := by
    have : Nat.gcd x m ∣ p + m := hm ▸ dvd_mul_of_dvd_right (Nat.gcd_dvd_left x m) 4
    exact (Nat.dvd_add_left (Nat.gcd_dvd_right x m)).1 this
  rcases hp.eq_one_or_self_of_dvd _ h1 with h | h
  · exact h
  · exact absurd (h ▸ Nat.gcd_dvd_left x m) hpx

/-- Easy direction of Theorem 1 (via the explicit identities). -/
theorem good_of_isRatio {p x m : ℕ} (hp : 0 < p) (hx : 0 < x) (hm : 4 * x = p + m)
    (h : IsRatio m x (-1) ∨ IsRatio m x (-(p : ZMod m))) : Good p x := by
  rcases h with ⟨u, v, huv, h⟩ | ⟨u, v, huv, h⟩
  · refine good_of_dvd_first hp hx hm huv ?_
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [← h]; ring
  · refine good_of_dvd_second hp hx hm huv ?_
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [← h]; ring

/-- A divisor `b` of `x²` with `b ≡ g x (mod m)` gives `g ∈ R(x)`. -/
theorem isRatio_of_dvd_sq {m x b : ℕ} {g : ZMod m} (hx : 0 < x) (hxm : Nat.Coprime x m)
    (hb : b ∣ x ^ 2) (h : (b : ZMod m) = g * x) : IsRatio m x g := by
  set G := Nat.gcd b x with hG
  have hG0 : 0 < G := Nat.gcd_pos_of_pos_right _ hx
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_left b x
  obtain ⟨v, hv⟩ := Nat.gcd_dvd_right b x
  rw [← hG] at hu hv
  have hcop : Nat.Coprime u v := by
    have := Nat.coprime_div_gcd_div_gcd (m := b) (n := x) hG0
    rw [← hG] at this
    rwa [hu, hv, Nat.mul_div_cancel_left _ hG0, Nat.mul_div_cancel_left _ hG0] at this
  have hux : u ∣ x := by
    have h1 : G * u ∣ G * (v * x) := by
      rw [← hu]; rw [sq] at hb; rw [show G * (v * x) = (G * v) * x by ring, ← hv]; exact hb
    exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hG0 h1)
  have hvx : v ∣ x := ⟨G, by rw [hv]; ring⟩
  refine ⟨u, v, hcop.mul_dvd_of_dvd_of_dvd hux hvx, ?_⟩
  have hGm : IsUnit (G : ZMod m) :=
    (ZMod.isUnit_iff_coprime G m).2 (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right b x) hxm)
  apply hGm.mul_left_cancel
  have e1 : (b : ZMod m) = G * u := by rw [hu]; push_cast; ring
  have e2 : (x : ZMod m) = G * v := by rw [hv]; push_cast; ring
  rw [e1, e2] at h
  linear_combination -h

/-- Hard direction of Theorem 1. -/
theorem isRatio_of_good {p x m : ℕ} (hp : p.Prime) (hpx : ¬ p ∣ x) (hx : 0 < x)
    (hm : 4 * x = p + m) (hpm : Nat.Coprime p m) (hg : Good p x) :
    IsRatio m x (-1) ∨ IsRatio m x (-(p : ZMod m)) := by
  obtain ⟨y, z, hy, hz, heq⟩ := hg
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hxm := coprime_of_prime hp hpx hm
  -- m y z = p x (y + z)
  have key : (m : ℚ) * y * z = p * x * (y + z) := by
    have h4 : (4 : ℚ) * x = p + m := by exact_mod_cast hm
    have hx' : (0 : ℚ) < x := by exact_mod_cast hx
    have hy' : (0 : ℚ) < y := by exact_mod_cast hy
    have hz' : (0 : ℚ) < z := by exact_mod_cast hz
    field_simp at heq
    linear_combination heq - ((y : ℚ) * z) * h4
  have keyN : m * y * z = p * x * (y + z) := by exact_mod_cast key
  set B := p * x with hB
  have hB0 : 0 < B := Nat.mul_pos hp.pos hx
  -- both factors positive
  have hyB : B < m * y := by
    by_contra hc
    push Not at hc
    have : m * z ≤ B := by
      by_contra hc2; push Not at hc2
      have : (m * y) * z < B * z + B * y := by nlinarith
      nlinarith
    nlinarith
  have hzB : B < m * z := by
    by_contra hc
    push Not at hc
    nlinarith
  set D := m * y - B with hD
  set E := m * z - B with hE
  have hDE : D * E = B ^ 2 := by
    zify [hyB.le, hzB.le] at hD hE ⊢
    have : (m : ℤ) * y * z = B * (y + z) := by exact_mod_cast keyN
    rw [hD, hE]; nlinarith [this]
  have hDm : (D : ZMod m) = -(B : ZMod m) := by
    have : D + B = m * y := by omega
    have h2 : ((D + B : ℕ) : ZMod m) = 0 := by rw [this]; push_cast; simp
    push_cast at h2; linear_combination h2
  have hDdvd : D ∣ p ^ 2 * x ^ 2 := ⟨E, by rw [hDE, hB]; ring⟩
  obtain ⟨a, b, ha, hb, hab⟩ := dvd_mul.1 hDdvd
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 ha
  have hpu : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).2 hpm
  have hxu : IsUnit (x : ZMod m) := (ZMod.isUnit_iff_coprime x m).2 hxm
  rw [hab, hB] at hDm
  push_cast at hDm
  interval_cases i
  · -- D = b
    right
    exact isRatio_of_dvd_sq hx hxm hb (by linear_combination hDm)
  · -- D = p b : b = -x
    left
    refine isRatio_of_dvd_sq hx hxm hb ?_
    apply hpu.mul_left_cancel
    linear_combination hDm
  · -- D = p^2 b : p b = -x, use b' = x^2 / b
    right
    have h1 : (p : ZMod m) * b = -x := by
      apply hpu.mul_left_cancel; linear_combination hDm
    obtain ⟨b', hb'⟩ := hb
    have hb'd : b' ∣ x ^ 2 := ⟨b, by rw [hb']; ring⟩
    refine isRatio_of_dvd_sq hx hxm hb'd ?_
    have hc : ((x ^ 2 : ℕ) : ZMod m) = b * b' := by rw [hb']; push_cast; ring
    push_cast at hc
    apply hxu.mul_left_cancel
    linear_combination (b' : ZMod m) * h1 + (p : ZMod m) * hc

/-- **Theorem 1** (ratio criterion). -/
theorem good_iff_isRatio {p x m : ℕ} (hp : p.Prime) (hpx : ¬ p ∣ x) (hx : 0 < x)
    (hm : 4 * x = p + m) (hpm : Nat.Coprime p m) :
    Good p x ↔ IsRatio m x (-1) ∨ IsRatio m x (-(p : ZMod m)) :=
  ⟨isRatio_of_good hp hpx hx hm hpm, good_of_isRatio hp.pos hx hm⟩

end FirstDenominators
