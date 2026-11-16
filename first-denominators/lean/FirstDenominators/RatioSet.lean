import FirstDenominators.Criterion

/-!
# `R(x)` as a product set

In `G = (ZMod m)ˣ`, `R(x) = A_{q₁} ⋯ A_{q_k}` where `q₁, …, q_k` are the prime factors of `x`
with multiplicity and `A_q = {q⁻¹, 1, q}` (proof of Theorem 3, first line).
-/

namespace FirstDenominators

open Pointwise

/-- `A_q = {q⁻¹, 1, q}`. -/
def A {G : Type*} [Group G] [DecidableEq G] (q : G) : Finset G := {q⁻¹, 1, q}

theorem mem_A {G : Type*} [Group G] [DecidableEq G] {q g : G} :
    g ∈ A q ↔ g = q⁻¹ ∨ g = 1 ∨ g = q := by
  simp [A]

/-- A natural number as a unit of `ZMod m` (junk value `1` if it is not coprime to `m`). -/
def toU (m q : ℕ) : (ZMod m)ˣ := if h : q.Coprime m then ZMod.unitOfCoprime q h else 1

theorem coe_toU {m q : ℕ} (h : q.Coprime m) : ((toU m q : (ZMod m)ˣ) : ZMod m) = q := by
  unfold toU
  split
  · exact ZMod.coe_unitOfCoprime q ‹_›
  · contradiction

/-- `R(x) ⊂ (ZMod m)ˣ`. -/
def ratioSet (m x : ℕ) [NeZero m] : Finset (ZMod m)ˣ :=
  Finset.univ.filter (fun g => IsRatio m x (g : ZMod m))

theorem mem_ratioSet {m x : ℕ} [NeZero m] {g : (ZMod m)ˣ} :
    g ∈ ratioSet m x ↔ IsRatio m x (g : ZMod m) := by
  simp [ratioSet]

theorem ratioSet_one (m : ℕ) [NeZero m] : ratioSet m 1 = {1} := by
  ext g
  simp only [mem_ratioSet, Finset.mem_singleton]
  constructor
  · rintro ⟨u, v, huv, h⟩
    rw [Nat.dvd_one, mul_eq_one] at huv
    obtain ⟨rfl, rfl⟩ := huv
    ext; simpa using h
  · rintro rfl; exact ⟨1, 1, by simp, by simp⟩

theorem ratioSet_prime_mul {m n q : ℕ} [NeZero m] (hq : q.Prime) (hqm : q.Coprime m) :
    ratioSet m (q * n) = A (toU m q) * ratioSet m n := by
  ext g
  have hc : ((toU m q : (ZMod m)ˣ) : ZMod m) = q := coe_toU hqm
  have hinv : ((toU m q)⁻¹ : (ZMod m)ˣ).val * q = 1 := by rw [← hc]; simp
  simp only [mem_ratioSet, Finset.mem_mul, mem_A]
  constructor
  · rintro ⟨u, v, huv, h⟩
    by_cases hu : q ∣ u
    · obtain ⟨u', rfl⟩ := hu
      refine ⟨toU m q, Or.inr (Or.inr rfl), (toU m q)⁻¹ * g, ⟨u', v, ?_, ?_⟩, by simp⟩
      · exact Nat.dvd_of_mul_dvd_mul_left hq.pos (by rw [← mul_assoc]; exact huv)
      · push_cast at h ⊢
        rw [mul_assoc, h]; linear_combination (u' : ZMod m) * hinv
    by_cases hv : q ∣ v
    · obtain ⟨v', rfl⟩ := hv
      refine ⟨(toU m q)⁻¹, Or.inl rfl, toU m q * g, ⟨u, v', ?_, ?_⟩, by simp⟩
      · exact Nat.dvd_of_mul_dvd_mul_left hq.pos (by
          rw [show q * (u * v') = u * (q * v') by ring]; exact huv)
      · push_cast at h ⊢; rw [hc, ← h]; ring
    · have hcop : Nat.Coprime (u * v) q := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]
        rintro hd; rcases (Nat.Prime.dvd_mul hq).1 hd with h' | h' <;> contradiction
      refine ⟨1, Or.inr (Or.inl rfl), g, ⟨u, v, ?_, h⟩, by simp⟩
      exact (Nat.Coprime.dvd_mul_left hcop).1 huv
  · rintro ⟨a, ha, b, ⟨u, v, huv, h⟩, rfl⟩
    rcases ha with rfl | rfl | rfl
    · refine ⟨u, q * v, ?_, ?_⟩
      · rw [show u * (q * v) = q * (u * v) by ring]; exact mul_dvd_mul_left q huv
      · push_cast; rw [← h]; linear_combination ((b : ZMod m) * v) * hinv
    · exact ⟨u, v, dvd_mul_of_dvd_right huv q, by simpa using h⟩
    · refine ⟨q * u, v, ?_, ?_⟩
      · rw [mul_assoc]; exact mul_dvd_mul_left q huv
      · push_cast; rw [hc, mul_assoc, h]

theorem ratioSet_list_prod {m : ℕ} [NeZero m] (L : List ℕ) (hL : ∀ q ∈ L, q.Prime)
    (hc : ∀ q ∈ L, q.Coprime m) :
    ratioSet m L.prod = (L.map (fun q => A (toU m q))).prod := by
  induction L with
  | nil => simp only [List.prod_nil, List.map_nil]; rw [ratioSet_one]; rfl
  | cons q L ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [ratioSet_prime_mul (hL q (by simp)) (hc q (by simp)),
      ih (fun r hr => hL r (by simp [hr])) (fun r hr => hc r (by simp [hr]))]

/-- `R(x) = ∏_{q | x} {q⁻¹, 1, q}` over the prime factors of `x` with multiplicity. -/
theorem ratioSet_eq_prod {m x : ℕ} [NeZero m] (hx : 0 < x) (hxm : x.Coprime m) :
    ratioSet m x = (x.primeFactorsList.map (fun q => A (toU m q))).prod := by
  conv_lhs => rw [← Nat.prod_primeFactorsList hx.ne']
  exact ratioSet_list_prod _ (fun q hq => Nat.prime_of_mem_primeFactorsList hq)
    (fun q hq => Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactorsList hq) hxm)

end FirstDenominators
