import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  exact εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have ngeNs : n ≥ Ns := le_of_max_le_left nge
  have ngeNt : n ≥ Nt := le_of_max_le_right nge
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := by apply abs_add
    _ < ε/2 + ε/2 := by
      apply add_lt_add
      apply hs n ngeNs
      apply ht n ngeNt
    _ = ε := by ring

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨Ns, hs⟩
  use Ns
  intro n nge
  dsimp
  calc
    |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) := by
      exact Iff.mpr (mul_lt_mul_left acpos) (hs n nge)
    _ = ε := by
      apply mul_div_cancel'
      apply ne_of_gt acpos

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  rw [add_comm, ← sub_lt_iff_lt_add]
  calc
    |s n| - |a| ≤  |s n - a| := abs_sub_abs_le_abs_sub (s n) a
    _ < 1 := h n nge

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nge
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left nge
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right nge
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by
      rw [sub_zero, abs_mul, sub_zero]
    _ < B * (ε / B) := by
      apply mul_lt_mul'' (h₀ n ngeN₀)
      apply h₁ n ngeN₁
      apply abs_nonneg
      apply abs_nonneg
    _ = ε := by
      apply mul_div_cancel' _ (ne_of_lt Bpos).symm

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have aneb : a ≠ b := by exact abne
  have : |a - b| > 0 := by
    rw [← sub_ne_zero] at aneb
    apply Iff.mpr abs_pos aneb
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b|:= by
    calc
      |a - b| = |(-(s N - a)) + (s N - b)| := by
        congr
        ring
      _ ≤ |(-(s N - a)) + (s N - b)| := by rfl
      _ ≤ |(-(s N - a))| + |s N - b| := abs_add _ _
      _ = |s N - a| + |s N - b| := by rw [abs_neg]
      _ < ε + ε := add_lt_add absa absb
      _ = |a - b| := by apply add_halves

  exact lt_irrefl _ this

section
variable {α : Type _} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
