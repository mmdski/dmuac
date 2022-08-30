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

6.5 Natural Deduction: Inference Reasoning

6.5.2 And Introduction {/\I}
Exercise 10. Prove P, Q, R |- P /\ (Q /\ R)

       Q    R
       ------{/\I}
 P     Q /\ R
-------------{/\I}
 P /\ (Q /\ R)

>th_ex10 = Theorem [P,Q,R] (And P (And Q R))
>pr_ex10 = AndI (
> Assume P,
> AndI
>   (Assume Q, Assume R)
>   (And Q R))
> (And P (And Q R))

check_proof th_ex10 pr_ex10 ==> The proof is valid

6.5.3 And Elimination {/\E_L}, {/\E_R}

Theorem 38. P, Q /\ R |- P /\ Q

>pr_th38 = AndI
> (Assume P,
>   AndEL (Assume (And Q R)) Q)
> (And P Q)

QED

Theorem 39. (P /\ Q) /\ R |- R /\ Q

>th_th39 = Theorem [And (And P Q) R] (And R Q)
>pr_th39 = AndI
> (AndER
>   (Assume (And (And P Q) R))
>   R,
> AndER
>   (AndEL
>     (Assume (And (And P Q) R))
>     (And P Q))
>   Q)
> (And R Q)

QED

Theorem 40. P /\ Q |- Q /\ P

>th_th40 = Theorem [And P Q] (And Q P)
>pr_th40 =
> AndI
>   (AndER
>     (Assume (And P Q))
>     Q,
>   AndEL
>     (Assume (And P Q))
>     P)
>   (And Q P)

QED
