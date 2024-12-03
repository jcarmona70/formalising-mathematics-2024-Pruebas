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

axiom A:Type
axiom my_true:Prop
axiom my_trivial:my_true
axiom cosa:A
axiom cosa_de_cosa:cosa
axiom una_prop:Prop
axiom demo_de_una_prop:una_prop
axiom orden_sup:Type 1
#check orden_sup
axiom b:orden_sup
#check b
axiom c:b

#check my_trivial


#check Prop
#check Sort 0
#check A

#print my_not

#print prefix And
