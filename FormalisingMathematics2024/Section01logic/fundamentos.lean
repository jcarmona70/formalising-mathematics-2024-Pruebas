import Mathlib.Tactic

--lemma PL1: ∀ P Q:Prop, P → (Q → P) := by
def my_true:= ∀ P:Prop, P → P

#print my_true

lemma obvio:my_true:= by
  intro P
  intro hP
  exact hP

axiom my_not:Prop → Prop

def PL1:= ∀ P Q:Prop, P → (Q → P)

def PL2:= ∀ P Q R:Prop, (P → (Q → R)) → ((P → Q) → (P → R))

def PL3:= ∀ P Q:Prop, my_not P → (P → Q)

def my_false := my_not my_true

lemma caract_not (pl1:PL1) (pl2:PL2) (pl3:PL3):∀ P:Prop, (my_not P) ↔ (P → my_false):= by
  intro P
  constructor
  exact pl3 P my_false
#print PL1
