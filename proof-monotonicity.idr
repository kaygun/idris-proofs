unit: (a:Nat) -> (plus a Z) = a
unit Z = Refl
unit (S k) = rewrite unit k in Refl

unloop: (a: Nat) -> (b: Nat) -> plus a (S b) = S (plus a b) 
unloop Z b = Refl
unloop (S k) b = rewrite unloop k b in Refl

monotone: (a:Nat) -> (b:Nat) -> (S a) <= (S b) = a <= b
monotone Z Z = Refl
monotone a (S k) = ?lemma_rhs_2

cancellative: (a:Nat) -> (b:Nat) -> (c: Nat) -> (plus a c) <= (plus b c) = a <= b 
cancellative a b Z     = rewrite unit b in 
                           rewrite unit a in Refl
cancellative a b (S c) =  rewrite unloop b c in
                            rewrite unloop a c in 
                              rewrite monotone (plus a c) (plus b c) in 
                                rewrite cancellative a b c in Refl

