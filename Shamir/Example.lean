import Shamir.Basic

/-!
# A small example

In `ZMod 7` (the integers modulo 7, a field), share the secret `3` with threshold `2`, so
`k = 1` random coefficient. With the coefficient `2`, the dealer's polynomial is
`p(X) = 3 + 2X`, and the parties at points `1`, `2`, `3` get `5`, `0`, `2`.
-/

namespace Shamir.Example

/-- 7 is prime, so `ZMod 7` is a field. -/
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem share_at_1 : share (3 : ZMod 7) ![2] 1 = 5 := by
  simp [share, poly]; decide

theorem share_at_2 : share (3 : ZMod 7) ![2] 2 = 0 := by
  simp [share, poly]; decide

theorem share_at_3 : share (3 : ZMod 7) ![2] 3 = 2 := by
  simp [share, poly]; decide

/-- One share alone says nothing: whatever the secret, some coefficient gives the share
    `5` to the party at point `1`. -/
example (s : ZMod 7) : ∃ a : Fin 1 → ZMod 7, shares s ![1] a = ![5] :=
  (shares_bijective s ![1] (Function.injective_of_subsingleton _) (by decide)).2 _

end Shamir.Example
