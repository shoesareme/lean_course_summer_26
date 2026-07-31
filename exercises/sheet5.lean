import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · set x := (⌈1/ε⌉)
    have hok : ⌈1/ε⌉ > 0 := by
      have hbruh : 1/ε > 0 := by exact one_div_pos.mpr hε
      exact Int.ceil_pos.mpr hbruh
    use x.toNat
    constructor
    · have hok1 : (⌈1/ε⌉).toNat > 0 := by
        omega
      exact hok1
    · have hok1 : (⌈1/ε⌉).toNat > 0 := by
        omega
      have hok2 : (1/ε) > 0 := by
        exact one_div_pos.mpr hε
      have hm : (1/ε) ≤ ⌈1/ε⌉  := by exact Int.le_ceil (1/ε)
      have hclose : 1/(1/ε) ≥ 1/(⌈1/ε⌉) := by
        exact one_div_le_one_div_of_le hok2 hm
      have hx : x = ⌈ 1/ε ⌉ := by rfl
      rw [← hx] at hclose
      have hc1 : 1 / (1 / ε) = ε := by exact one_div_one_div ε
      have hx2 : (x) = (x.toNat : ℤ) := by omega
      rw [hc1] at hclose
      rw [hx2] at hclose
      exact le_of_eq_of_le rfl hclose
  use 1
  constructor
  · trivial
  · have ho : ε > 1 := by exact Std.not_le.mp h
    simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, ge_iff_le]
    exact Std.le_of_not_ge h

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  intro ε h
  have h1 := exercise1 h
  rcases h1 with ⟨k, hk⟩
  specialize hx k
  specialize hx hk.left
  rcases hx with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  have hclose := hk.right
  exact Std.lt_of_lt_of_le hN hclose


/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  · intro h ε hε
    specialize h ε hε
    rcases h with ⟨N, hN⟩
    use N
    intro m hm n hn
    specialize hN m hm n hn
    have hxm : x.x m = x.toRealSeq.x m := by
      exact Rat.cast_inj.mpr rfl
    have hxn : x.x n = x.toRealSeq.x n := by
      exact Rat.cast_inj.mpr rfl
    rw [← hxm, ← hxn]
    exact hN
  · intro h ε hε
    specialize h ε hε
    rcases h with ⟨N, hN⟩
    use N
    intro m hm n hn
    specialize hN m hm n hn
    have hxm : x.x m = x.toRealSeq.x m := by
      exact Rat.cast_inj.mpr rfl
    have hxn : x.x n = x.toRealSeq.x n := by
      exact Rat.cast_inj.mpr rfl
    rw [← hxm, ← hxn] at hN
    exact hN

/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  intro ε hε
  have hx2 := hx
  have he : ε/2 > 0 := by exact half_pos hε
  specialize hx (ε/2) he
  rcases hx with ⟨N, hN⟩
  specialize hx2 (ε/2) he
  rcases hx2 with ⟨N1, hN1⟩
  use N+N1
  intro m hm n hn
  have hn1 : n ≥ N1 := by exact Nat.le_of_add_left_le hn
  have hm1 : m ≥ N := by exact Nat.le_of_add_right_le hm
  specialize hN1 n hn1
  specialize hN m hm1
  have hclaim : dist (x.x m) (x.x n) ≤ (dist (x.x m) a) + (dist (x.x n) a) := by
    exact dist_triangle_right (x.x m) (x.x n) a
  have hclose : dist (x.x m) (x.x n) < ε / 2 + ε / 2 := by
    linarith
  linarith

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n

theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  intro h
  rcases h with ⟨a, ha⟩
  simp [tends_toReal] at ha
  specialize ha 1 Real.zero_lt_one
  set b := ⌈a⌉.toNat
  rcases ha with ⟨N, hN⟩
  have hN1 := hN
  specialize hN N (Nat.le_refl N)
  specialize hN1 (N+10) (Nat.le_add_right N 10)
  simp [my_diverging_sequence] at hN
  simp [my_diverging_sequence] at hN1
  have h : dist (N : ℝ ) (N+10 : ℝ ) = 10 := by
    rw [Real.dist_eq]
    have h : (N : ℝ) - (N + 10 : ℝ) = -10 := by ring
    rw [h]
    norm_num
  have hclose : dist (N : ℝ ) (N+10 : ℝ ) ≤ (dist (N : ℝ) a) + (dist (N+10 : ℝ) a) := by
    exact dist_triangle_right (N : ℝ) (N + 10 : ℝ) a
  have hclose : dist (N : ℝ ) (N+10 : ℝ ) < 1 + 1:= by
    linarith
  rw [h] at hclose
  linarith
