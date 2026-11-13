/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license; see hybrid-pilot/primecert-port/NOTICE.md.
Adapted from PrimeCert d84a15cacfdc45ae1e96e56dd58158f871787870.
Only the bitwise subtraction and prime mod-6 helpers are retained.
-/
import BJSHybridSieveCore
import Mathlib.Data.Nat.Prime.Basic
set_option maxHeartbeats 1200000
@[simp] theorem Nat.div_eq_div {a b : Nat} : a.div b = a / b := rfl
@[simp] lemma Nat.ldiff_zero_left {b : ℕ} : Nat.ldiff 0 b = 0 :=
  Nat.eq_of_testBit_eq (by simp)

@[simp] lemma Nat.ldiff_zero_right {b : ℕ} : Nat.ldiff b 0 = b :=
  Nat.eq_of_testBit_eq (by simp)

/-- Disjoint OR equals ADD, for `Nat`; hence subtracting a submask acts as bitwise `ldiff`. -/
theorem Nat.and_add_ldiff {a b : ℕ} : (a &&& b) + a.ldiff b = a := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp
  | bit ba a' ih =>
    induction b using Nat.binaryRec with
    | zero => simp
    | bit bb b' _ => grind [Nat.land_bit, Nat.ldiff_bit, Nat.bit_val, cases Bool]

theorem Nat.sub_and_eq_ldiff {a b : ℕ} : a - (a &&& b) = a.ldiff b := by
  grind [Nat.and_add_ldiff]

/-- A prime other than `2` and `3` is coprime to 6. -/
theorem Nat.Prime.mod_six_eq_one_or_five {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (hp₃ : p ≠ 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h₂ : p % 2 = 1 := Nat.odd_iff.mp (hp.eq_two_or_odd'.resolve_left (by lia))
  have h₃ : p % 3 ≠ 0 := by
    rw [ne_eq, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_prime_two_le hp (by lia)]
    lia
  lia

/-- A prime other than `2` and `3` is coprime to 6. -/
theorem Nat.Prime.coprime_six {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (hp₃ : p ≠ 3) :
    p.Coprime 6 := by
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  rcases hp.mod_six_eq_one_or_five hp₂ hp₃ with h | h <;> simp [h]


