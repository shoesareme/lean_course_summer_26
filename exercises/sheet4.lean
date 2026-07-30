import lecture5.examples5

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  constructor
  · intro h
    rw [q_eq] at h
    rw [mod_relation] at h
    rcases h with ⟨k1, hk1⟩
    have h : m1 = n * k1 + m2 := by
      exact Int.sub_eq_iff_eq_add.mp hk1
    set r := m2 % n
    have h1 : m2 % n = r := by
      trivial
    have h1copy := h1
    apply (Int.emod_eq_iff hn).mp at h1
    have hok := h1.right.right
    rcases hok with ⟨k, hk⟩
    have hok1 : r = n * k + m2 := by
      exact Int.sub_eq_iff_eq_add.mp hk
    apply modulo_eq_rest n m1 (k1-k) (m2 % n) hn
    · have h2 := h1.left
      have h3 := h1.right.left
      exact ⟨h2, h3⟩
    · rw [h1copy, hok1]
      ring_nf -- doing the calculations is too painful sorry
      exact h
  · intro h
    rw [q_eq, mod_relation]
    have hcopy := h
    have h2 : m2 % n = m1 % n := by
      symm at h
      exact h
    apply (Int.emod_eq_iff hn).mp at h
    have h1 := h.right.right
    rcases h1 with ⟨k, hk⟩
    -- m2 % n - m1 = n * k
    -- m1 % n - m2 = n * k1 by symmetry
    -- m1 = m2 % n - n * k
    -- m2 = m1 % n - n * k1
    -- m1 - m2 = (m2 % n - n * k) - (m1 % n - n * k1)
    -- m1 - m2 = n * k1 - n * k = n * (k1 - k)
    apply (Int.emod_eq_iff hn).mp at h2
    have h3 := h2.right.right
    rcases h3 with ⟨k1, hk1⟩
    have hok : m1 = m2 % n - n * k := by
      omega -- sorry :skull:
    have hok1 : m2 = m1 % n - n * k1 := by
      omega
    use k1 - k
    rw [hok]
    nth_rewrite 2 [hok1]
    rw [hcopy]
    ring

/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/

lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro h
    have h1 := hR.refl x
    have h2 : x ∈ {z | R x z} := by
      exact Set.mem_setOf.mpr h1
    have h3 : x ∈ {z | R y z} := by
      rw [h] at h2
      exact h2
    have h4 := Set.mem_setOf.mp h3
    exact hR.symm h4
    --hint: use x ∈ {z : α | R x z}
  intro hRxy
  apply Set.Subset.antisymm_iff.mpr -- show both inclusions
  constructor --hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
  · simp only [Set.setOf_subset_setOf]
    intro a h
    have h1 := hR.symm h
    -- #check hR.trans
    have hok := hR.trans h1 hRxy
    exact hR.symm hok
  simp only [Set.setOf_subset_setOf]
  intro a h
  have h1 := hR.symm hRxy
  have h2 := hR.symm h
  have hok := hR.trans h2 h1
  exact hR.symm hok

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  refine Quotient.lift (fun x => Quotient.mk (ℤ_mod_setoid n) (k * x)) ?_
  intro a b h
  have h1 : Quotient.mk (ℤ_mod_setoid n) a = Quotient.mk (ℤ_mod_setoid n) b := by
    exact Quotient.sound h
  apply Quotient.eq.mpr
  apply Quotient.eq.mp at h1
  rcases h1 with ⟨k1, hk1⟩
  use k1 * k
  ring_nf
  have hok : k * (a - b) = k * n * k1 := by
    rw [hk1, mul_assoc]
  ring_nf at hok
  exact hok

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y h1
  have hg : g (f x) = g (f y) := by
    rw [h1]
  rw [h x, h y] at hg
  exact hg

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  intro x
  use g x
  apply h x

-- def helper (n : ℤ) (hn : n ≠ 0) : ℤ → Fin n.natAbs := by
--   intro x
--   have : NeZero n := NeZero.mk hn
--   set s := x % n
--   exact Fin.ofNat n.natAbs s.natAbs
--   -- have h : x % n = s := by rfl
--   -- apply (Int.emod_eq_iff hn).mp at h
--   -- have h1 := h.left
--   -- set s1 := Int.toNat_of_nonneg h1


def q_res_inv (n : ℤ) (hn : n ≠ 0) : ℤ_mod n → Fin n.natAbs := by
  have : NeZero n := NeZero.mk hn
  refine Quotient.lift (fun x => (Fin.ofNat (n.natAbs) (x % n).natAbs : Fin n.natAbs)) ?_
  -- refine Quotient.lift (fun x => helper n hn x) ?_
  intro a b h
  simp only [Fin.ofNat_eq_cast]
  have h1 : Quotient.mk (ℤ_mod_setoid n) a = Quotient.mk (ℤ_mod_setoid n) b := by
    exact Quotient.sound h
  have hm : q n a = q n b := by
    exact q_eq.mpr h
  have hok : a % n = b % n := by
    exact (exercise0 hn).mp h1
  rw [hok]

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  have himp : NeZero n := NeZero.mk hn
  refine ⟨?_, ?_⟩
  · have hlinv : (∀ x : Fin n.natAbs, q_res_inv n hn (q_res n x) = x) := by
      intro x
      have htemp : Quotient.mk (ℤ_mod_setoid n) x = q_res n x := by
        rfl
      simp [q_res]
      simp [q_res_inv]
      set r := x.val % n
      have huseless : x.val % n = r := by
        rfl
      apply (Int.emod_eq_iff hn).mp at huseless
      rcases huseless.right.right with ⟨k, hk⟩
      have hplease : 0 ≤ x ∧ x < n.natAbs := by
        constructor
        · exact Fin.zero_le x
        · exact x.isLt
      have hclaim : k = 0 := by
        by_contra h
        have hmini : k ≥ 1 ∨ k ≤ -1 := by
          omega
        rcases hmini with hl | hr
        · have hyes : (n * k ≥ n ∧ n > 0) ∨ (n * k ≤ n ∧ n < 0) := by
            by_cases h1 : n > 0
            · left
              constructor
              · have hn_nonneg : 0 ≤ n := by omega
                exact le_mul_of_one_le_right hn_nonneg hl
              · exact h1
            · right
              have hbruh : n < 0 := by
                omega
              constructor
              · have hn_nonpos : n ≤ 0 := by omega
                exact mul_le_of_one_le_right hn_nonpos hl
              · exact hbruh
          rcases hyes with hell1 | hell2
          · have hbruh : n = n.natAbs := by
              omega
            rw [← hbruh] at huseless



      rw [hclaim, mul_zero] at hk
      have hclaim1 : r = x := by
        omega
      rw [hclaim1]
      simp only [Int.natAbs_natCast, Fin.cast_val_eq_self]
    exact f_injective_of_left_inverse (q_res n) (q_res_inv n hn) hlinv
  have hrinv : (∀ x : ℤ_mod n, q_res n (q_res_inv n hn x) = x) := by
    intro x
    simp [q_res]
    simp [q_res_inv]

    sorry
  exact f_surjective_of_right_inverse (q_res n) (q_res_inv n hn) hrinv

-- Quotient.exists_rep

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  cases c with
  | zero =>
    use 0
    rw [mul_zero]
  | succ c1 =>
    have h1c := h1
    have h2c := h2
    rcases h1 with ⟨k1, hk1⟩
    rcases h2 with ⟨k2, hk2⟩
    have h1copy := hk1
    have h2copy := hk2
    rw [hk1]
    rw [hk1] at hk2
    have hc : c1 + 1 ≠ 0 := by
      omega
    have ha : a ≠ 0 := by
      rw [h1copy] at hc
      exact Nat.ne_zero_of_mul_ne_zero_left hc
    have hclaim : a ∣ k2 := by
      set c := c1 + 1
      by_cases hm : a = 1
      · use k2
        rw [hm]
        rw [one_mul]
      · by_contra he
        have hok : a > 1 := by
          omega
        have hpr : ∃ p, p.Prime ∧ p ∣ a := by
          exact Nat.exists_prime_and_dvd hm
        rcases hpr with ⟨p, hp⟩
        have hp1 := hp.right
        have hp2 := hp.left
        have hpc : p ∣ c := by
          rcases hp1 with ⟨r, hr⟩
          rw [hk1]
          rw [hr]
          use r*k1
          rw [mul_assoc]
        have hpb : ¬ p ∣ b := by
          by_contra hbro
          have hdude : p ∣ a.gcd b := by
            exact Nat.dvd_gcd hp1 hbro
          rw [h3] at hdude
          have halmost : ¬ p ∣ 1 := by
            exact Nat.Prime.not_dvd_one hp2
          exact halmost hdude
        have hpk2 : ¬ p ∣ k2 := by

        rw [h2copy] at hpc
        have hclose : p ∣ b ∨ p ∣ k2 := by
          exact Nat.Prime.dvd_or_dvd hp2 hpc
        rcases hclose with hl | hr
        · exact hpb hl
        · exact hpk2 hr
    rcases hclaim with ⟨k, hk⟩
    rw [hk] at hk2
    have h : k1 = b * k := by
      ring_nf at hk2
      rw [mul_assoc] at hk2
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) hk2
    rw [h]
    use k
    rw [mul_assoc]
