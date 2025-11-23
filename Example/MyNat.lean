import Architect

@[blueprint (statement := /-- Natural numbers. -/)]
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

@[blueprint
  -- You may manually specify a \label
  "def:nat-add"
  (statement := /-- Natural number addition. -/)]
def add (a b : MyNat) : MyNat :=
  match b with
  | zero => a
  | succ b => succ (add a b)

@[simp, blueprint
  (statement := /-- For any natural number $a$, $0 + a = a$, where $+$ is \cref{def:nat-add}. -/)]
theorem zero_add (a : MyNat) : add zero a = a := by
  /-- The proof follows by induction. -/
  induction a <;> simp [*, add]

@[blueprint
  (statement := /-- For any natural numbers $a, b$, $(a + 1) + b = (a + b) + 1$. -/)]
theorem succ_add (a b : MyNat) : add (succ a) b = succ (add a b) := by
  /-- Proof by induction on $b$. -/
  -- If the proof contains sorry, the `\leanok` command will not be added
  sorry

@[blueprint
  (statement := /-- For any natural numbers $a, b$, $a + b = b + a$. -/)]
theorem add_comm (a b : MyNat) : add a b = add b a := by
  induction b with
  | zero =>
    have := trivial
    /-- The base case follows from \cref{MyNat.zero_add}. -/
    simp [add]
  | succ b ih =>
    /-- The inductive case follows from \cref{MyNat.succ_add}. -/
    sorry_using [succ_add]  -- the `sorry_using` tactic declares that the proof uses succ_add

/-! ## Multiplication -/

@[blueprint
  (uses := [add]) -- Manually added dependency
  (statement := /-- Natural number multiplication. -/)]
def mul (a b : MyNat) : MyNat := sorry

@[blueprint
  (statement := /-- For any natural numbers $a, b$, $a * b = b * a$. -/)]
theorem mul_comm (a b : MyNat) : mul a b = mul b a := by sorry

/-! ## Fermat's Last Theorem -/

@[blueprint "thm:flt"
  (statement := /-- Fermat's last theorem. -/)
  (title := "Taylor-Wiles")
  -- You may override the inferred statement dependencies by `uses`.
  (uses := [mul])
  -- Alternatively to docstring tactics and `using` tactics, proof metadata can be specified
  -- by `proof` and `proofUses`.
  (proof := /-- See \cite{Wiles1995, Taylor-Wiles1995}. -/) (proofUses := [mul_comm])
  (notReady := true) (discussion := 1)]
theorem flt : (sorry : Prop) := sorry

end MyNat

-- Finally, these are utility commands for debugging:

-- #show_blueprint Architect.Content
-- #show_blueprint
-- #show_blueprint_json
