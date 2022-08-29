Chapter 6 Propositional Logic

6.3 The Language of Propositional Logic

>import Stdm

Exercise 2.

(a) False /\ True = False

=> False

(b) True \/ (not True) = True

=> True

(c) not (False \/ True) = False

=> False

(d) (not (False /\ True)) \/ False = True

=> True

(e) (not True) ==> True = True

=> True

(f) True \/ False ==> True = True

=> True

(g) True ==> (True /\ False) = False

=> False

(h) False ==> False = True

=> True

(i) (not False) <=> True = True

=> True

(j) True <=> (False ==> False) = True

=> True

(k) False <=> (True /\ (False ==> True)) = False

=> False

(l) (not (True \/ False)) <=> False /\ True = True

=> True

Exercise 10. Prove P, Q, R |- P /\ (Q /\ R)

       Q    R
       ------{^I}
 P     Q /\ R
-------------{^I}
 P /\ (Q /\ R)

>th_ex10 = Theorem [P,Q,R] (And P (And Q R))
>pr_ex10 = AndI (
> Assume P, 
> AndI 
>   (Assume Q, Assume R) 
>   (And Q R)) 
> (And P (And Q R))

check_proof th_ex10 pr_ex10 ==> The proof is valid
