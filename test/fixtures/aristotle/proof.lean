theorem cand {S : Type} {p : Poly} (agent : Agent S p) (server : Lens p y)
    (n : Nat) (s : S) : (trace agent server n s).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [trace, List.length_cons]
    exact congrArg Nat.succ (ih (step agent server s))
