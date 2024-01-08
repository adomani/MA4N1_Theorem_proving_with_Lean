namespace ax

/-- By an oversight, we forgot to add `0` as a natural number. -/
inductive Nat
  | succ : Nat → Nat

theorem x (a : Nat) : False :=
  Ne.irrefl (a := a) (fun _ => a.rec (fun _ hn => hn) a a)

/-- No problem: let's add it! -/
axiom zero : Nat

theorem oh_boy : False := x zero


theorem oh_no : False :=
  Ne.irrefl (a := zero) (fun _ => Nat.rec (fun _ hn => hn) zero zero)

theorem Nat_eq_Nat : _root_.Nat = ax.Nat :=
  oh_no.elim

#print axioms Nat_eq_Nat

end ax

#exit

#check Nat.noConfusion

theorem Nat.ind (h : Nat → Sort u)
    (hn : ∀ {n}, h n → h (succ n)) (n : Nat) : h n :=
  n.rec (fun _ => hn)

theorem subsingleton : ∀ m n : Nat, m = n := by
  exact fun m => Nat.rec (fun _ hn => hn) m m
  done


example {a : _root_.Nat}: a ∈ _root_.Nat ↔ a ∈ (Set.univ) := by
  apply
  done

#print Nat.rec
#check ax.Nat.
