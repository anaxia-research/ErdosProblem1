import Mathlib

/-!
# Theorem 1: the two explicit identities

`p, x, m` are natural numbers with `4x = p + m`.  For `u, v` with `u * v ∣ x`:

* if `m ∣ u + v`, then `4/p = 1/x + 1/y + 1/z` with
  `y = p (x/v) (u+v)/m`, `z = p (x/u) (u+v)/m`;
* if `m ∣ u + p v`, then `4/p = 1/x + 1/y + 1/z` with
  `y = p (x/u) (u+pv)/m`, `z = (x/v) (u+pv)/m`.

Coprimality of `u` and `v` is not needed.  Divisions are natural-number divisions, which are
exact under the hypotheses.
-/

namespace FirstDenominators

/-- `x` is a good first denominator for `p`. -/
def Good (p x : ℕ) : Prop :=
  ∃ y z : ℕ, 0 < y ∧ 0 < z ∧ (4 : ℚ) / p = 1 / x + 1 / y + 1 / z

theorem identity_first {p x m u v : ℕ} (hp : 0 < p) (hx : 0 < x) (hm : 4 * x = p + m)
    (huv : u * v ∣ x) (hdiv : m ∣ u + v) :
    0 < p * (x / v) * ((u + v) / m) ∧ 0 < p * (x / u) * ((u + v) / m) ∧
    (4 : ℚ) / p = 1 / x + 1 / (p * (x / v) * ((u + v) / m) : ℕ)
      + 1 / (p * (x / u) * ((u + v) / m) : ℕ) := by
  obtain ⟨w, rfl⟩ := huv
  obtain ⟨k, hk⟩ := hdiv
  have hu : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
  have hv : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
  have e1 : u * v * w / v = u * w := by
    rw [show u * v * w = (u * w) * v by ring]; exact Nat.mul_div_cancel _ hv
  have e2 : u * v * w / u = v * w := by
    rw [show u * v * w = (v * w) * u by ring]; exact Nat.mul_div_cancel _ hu
  have e3 : (u + v) / m = k := by rw [hk]; exact Nat.mul_div_cancel_left _ hm0
  rw [e1, e2, e3]
  refine ⟨by positivity, by positivity, ?_⟩
  have hmQ : (m : ℚ) * k = u + v := by exact_mod_cast hk.symm
  have h4 : (4 : ℚ) * (u * v * w) = p + m := by exact_mod_cast hm
  push_cast
  field_simp
  nlinarith [hmQ, h4]

theorem identity_second {p x m u v : ℕ} (hp : 0 < p) (hx : 0 < x) (hm : 4 * x = p + m)
    (huv : u * v ∣ x) (hdiv : m ∣ u + p * v) :
    0 < p * (x / u) * ((u + p * v) / m) ∧ 0 < (x / v) * ((u + p * v) / m) ∧
    (4 : ℚ) / p = 1 / x + 1 / (p * (x / u) * ((u + p * v) / m) : ℕ)
      + 1 / ((x / v) * ((u + p * v) / m) : ℕ) := by
  obtain ⟨w, rfl⟩ := huv
  obtain ⟨k, hk⟩ := hdiv
  have hu : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
  have hv : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hx)
  have hpv : 0 < u + p * v := by positivity
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
  have e1 : u * v * w / v = u * w := by
    rw [show u * v * w = (u * w) * v by ring]; exact Nat.mul_div_cancel _ hv
  have e2 : u * v * w / u = v * w := by
    rw [show u * v * w = (v * w) * u by ring]; exact Nat.mul_div_cancel _ hu
  have e3 : (u + p * v) / m = k := by rw [hk]; exact Nat.mul_div_cancel_left _ hm0
  rw [e1, e2, e3]
  refine ⟨by positivity, by positivity, ?_⟩
  have hmQ : (m : ℚ) * k = u + p * v := by exact_mod_cast hk.symm
  have h4 : (4 : ℚ) * (u * v * w) = p + m := by exact_mod_cast hm
  push_cast
  field_simp
  nlinarith [hmQ, h4]

theorem good_of_dvd_first {p x m u v : ℕ} (hp : 0 < p) (hx : 0 < x) (hm : 4 * x = p + m)
    (huv : u * v ∣ x) (hdiv : m ∣ u + v) : Good p x :=
  let h := identity_first hp hx hm huv hdiv
  ⟨_, _, h.1, h.2.1, h.2.2⟩

theorem good_of_dvd_second {p x m u v : ℕ} (hp : 0 < p) (hx : 0 < x) (hm : 4 * x = p + m)
    (huv : u * v ∣ x) (hdiv : m ∣ u + p * v) : Good p x :=
  let h := identity_second hp hx hm huv hdiv
  ⟨_, _, h.1, h.2.1, h.2.2⟩

end FirstDenominators
