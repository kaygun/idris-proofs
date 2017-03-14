-- This is the proof that + is associative on Nat

assoc : (a, b, c: Nat) -> a `plus` (b `plus` c) = (a `plus` b) `plus` c
assoc Z     b c = Refl
assoc (S a) b c = rewrite assoc a b c in Refl


