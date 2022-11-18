import data.polynomial.basic
import data.polynomial.degree.definitions
import data.real.basic
import data.real.sign
import data.seq.seq
import data.bool.basic
import data.nat.parity
open classical

#check dec

example {a b : ℝ}
: (real.sign a) = (real.sign b) ↔ (a < 0 ∧ b < 0) ∨ (a > 0 ∧ b > 0) ∨ (a = 0 ∧ a = b)
:= sorry

--example (a b : ℝ) : bool := a==b

noncomputable def h (a b : ℝ) := if a = b then 0 else 69

noncomputable def sign_changes_helper (c : ℕ → ℝ) : ℕ → ℝ → ℕ
| 0 := λ x, 0
| (n+1) := λ prev : ℝ,
    if (real.sign prev)=(real.sign (c n))
    then sign_changes_helper n prev
    else
     (if 0=(c n)
      then sign_changes_helper n prev
      else 1 + (sign_changes_helper n (c n)))

#check polynomial.coeff
#check polynomial.degree

noncomputable def sign_changes (p : polynomial ℝ) : ℕ :=
match (polynomial.degree p) with
  | (⊥ : with_bot ℕ) := 0
  | (some n) :=
      sign_changes_helper (polynomial.coeff p) n (polynomial.coeff p n)
end

noncomputable def pos_roots (p : polynomial ℝ) : ℕ := sorry

lemma descartes_rule_of_signs (f : polynomial ℝ) : even (sign_changes f) ↔ even (pos_roots f)
:= sorry
