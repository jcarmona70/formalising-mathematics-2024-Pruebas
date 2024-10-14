import Mathlib.Tactic

lemma lema1 (P:Prop):P → P := by
  intro p
  exact p


axiom my_not:Prop → Prop

axiom my_not_caracterization (P:Prop):∀ Q:Prop, my_not P → P → Q

#print my_not_caracterization

def my_or (P Q:Prop):Prop := (my_not P) → Q

lemma my_or.introl (P Q:Prop):P → (my_or P Q) := by
  intro p
  intro h
  apply my_not_caracterization P Q
  exact h
  exact p

lemma my_or.intror (P Q:Prop):Q → (my_or P Q) := by
  intro q
  intro h
  apply my_not_caracterization P Q
  exact h

lemma my_or.elim (P Q R:Prop):my_or P Q → (P → R) → (Q → R) → R := by
  intro h
  intro hpr
  intro hqr
#print prefix Or
