unit: (a:Nat) -> (plus a Z) = a
unit Z     = Refl
unit (S k) = rewrite unit k in Refl

unloop: (a: Nat) -> (b: Nat) -> plus a (S b) = S (plus a b) 
unloop Z b = Refl
unloop (S k) b = rewrite unloop k b in Refl

lemma1: (a:Nat) -> (b:Nat) -> (c: Nat) -> a <= b = (plus a c) <= (plus b c)
lemma1 a b Z     = rewrite unit b in 
                     rewrite unit a in Refl
lemma1 a b (S k) = rewrite lemma1 a b (S k) in 
                     rewrite unloop b k in 
                       rewrite unloop a k in Refl


