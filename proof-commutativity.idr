-- This is the proof that plus is commutative in Nat

unit: (a: Nat) -> plus a Z = a
unit Z = Refl
unit (S k) = rewrite unit k in Refl

unloop : (a: Nat) -> (b: Nat) -> plus a (S b) = S (plus a b) 
unloop Z a = Refl
unloop (S k) b = rewrite unloop k b in Refl

comm: (a: Nat) -> (b: Nat) -> plus a b = plus b a
comm Z b = rewrite unit b in Refl
comm (S k) b = rewrite comm k b in rewrite unloop b k in Refl

