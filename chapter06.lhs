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

Exercise 12. Prove (P /\ Q) /\ R |- P /\ (Q /\ R)

> -- Isolate P
>th_ex12_1 = Theorem [And (And P Q) R] P
>pr_ex12_1 =
> AndEL
>   (AndEL
>     (Assume (And (And P Q) R))
>     (And P Q))
>   P

> -- Isolate Q
>th_ex12_2 = Theorem [And (And P Q) R] Q
>pr_ex12_2 =
> AndER
>   (AndEL
>     (Assume (And (And P Q) R))
>     (And P Q))
>   Q

> -- Isolate R
>th_ex12_3 = Theorem [And (And P Q) R] R
>pr_ex12_3 = AndER (Assume (And (And P Q) R)) R

> -- Q /\ R
>th_ex12_4 = Theorem [And (And P Q) R] (And Q R)
>pr_ex12_4 = AndI (pr_ex12_2, pr_ex12_3) (And Q R)

> -- P /\ (Q /\ R)
>th_ex12 = Theorem [And (And P Q) R] (And P (And Q R))
>pr_ex12 = AndI (pr_ex12_1, pr_ex12_4) (And P (And Q R))

QED

6.5.4 Imply Elimination {=>E}

Theorem 42. Q /\ P, P /\ Q => R |- R.

Proof.

>th_th42 = Theorem [And Q P, Imp (And P Q) R] R
>pr_th42 =
> ImpE
>   (AndI
>     (AndER
>       (Assume (And Q P))
>       P,
>     AndEL
>       (Assume (And Q P))
>       Q)
>     (And P Q),
>   Assume (Imp (And P Q) R))
>   R
> -- QED
>th42_check = check_proof th_th42 pr_th42

Exercise 13. Prove P, P => Q, (P /\ Q) => (R /\ S) |- S.

>th_ex13 = Theorem [P, Imp P Q, Imp (And P Q) (And R S)] S
>pr_ex13 =
> AndER
>   (ImpE
>     (AndI
>       (Assume P,
>       ImpE
>         (Assume P, Assume (Imp P Q))
>         Q)
>       (And P Q),
>     Assume (Imp (And P Q) (And R S)))
>     (And R S))
>   S
>ex13_check = check_proof th_ex13 pr_ex13

QED

Exercise 14. Prove P => Q, R => S, P /\ R |- S /\ R

th_ex14 = Theorem [Imp P Q, Imp R S, And P R] (And S R)

>th_ex14_1 = Theorem [And P R] R
>pr_ex14_1 =
> AndER
>   (Assume (And P R))
>   R

>th_ex14 = Theorem [Imp P Q, Imp R S, And P R] (And S R)
>pr_ex14 =
> AndI
>   (ImpE
>     (pr_ex14_1,
>     Assume (Imp R S))
>     S,
>   pr_ex14_1)
>   (And S R)

6.5.5 Imply Introduction {=>I}

Theorem 44. |- (P /\ Q) -> Q

>th_th44 = Theorem [] (Imp (And P Q) Q)
>pr_th44 =
> ImpI
>   (AndER
>     (Assume (And P Q))
>     Q)
>   (Imp (And P Q) Q)

Exercise 15. Prove P |- Q => P /\ Q.

>th_ex15 = Theorem [P] (Imp Q (And P Q))
>pr_ex15 =
> ImpI
>   (AndI
>     (Assume P, Assume Q)
>     (And P Q))
>   (Imp Q (And P Q))

QED

>ex15_check = check_proof th_ex15 pr_ex15

Exercise 16. Prove |- P /\ Q => Q /\ P.

>th_ex16 = Theorem [] (Imp (And P Q) (And Q P))
>pr_ex16 =
> ImpI
>   (AndI
>     (AndER
>       (Assume (And P Q))
>       Q,
>     AndEL
>       (Assume (And P Q))
>       P)
>     (And Q P))
>   (Imp (And P Q) (And Q P))

QED

>ex16_check = check_proof th_ex16 pr_ex16

6.5.6 Or Introduction {\/I_L}, {\/I_R}

Theorem 47. P \/ Q |- P \/ Q.

>th_th47 = Theorem [And P Q] (Or P Q)
>pr_th47 =
> OrIL
>   (AndEL
>     (Assume (And P Q))
>     P)
>   (Or P Q)

QED

Exercise 17. Prove P => False \/ P.

>th_ex17 = Theorem [] (Imp P (Or FALSE P))
>pr_ex17 =
> ImpI
>   (OrIR
>     (Assume P)
>     (Or FALSE P))
>   (Imp P (Or FALSE P))
> -- QED
>ex17_check = check_proof th_ex17 pr_ex17

Exercise 18. Prove P, Q |- (P /\ Q) \/ (Q \/ R)

>th_ex18 = Theorem [P,Q] (Or (And P Q) (Or Q R))
>pr_ex18 =
> OrIL
>   (AndI
>     (Assume P, Assume Q)
>     (And P Q))
>   (Or (And P Q) (Or Q R))
> -- QED
>ex18_check = check_proof th_ex18 pr_ex18

6.5.7 Or Elimination {\/E}

Theorem 48. (P /\ Q) \/ (P /\ R) |- P.

>th_th48 = Theorem [Or (And P Q) (And P R)] P
>pr_th48 =
> OrE
>   (Assume (Or (And P Q) (And P R)),
>   AndEL
>     (Assume (And P Q))
>     P,
>   AndEL
>     (Assume (And P R))
>     P)
>   P
> -- QED
>th_48_check = check_proof th_th48 pr_th48

6.5.8 Identity {ID}

Theorem 50. P |- P.

>th_th50 = Theorem [P] P
>pr_th50 =
> ID
>   (Assume P)
>   P
> -- QED

Theorem 51. |- True.

>th_th51 = Theorem [] (Imp FALSE FALSE)
>pr_th51 =
> ImpI
>   (ID
>     (Assume FALSE)
>     FALSE)
>   (Imp FALSE FALSE)
> -- QED

6.5.9 Contradiction {CTR}

Theorem 52. P,~P |- Q

>th_th52 = Theorem [P, Not P] Q
>pr_th52 =
> CTR
>   (ImpE
>     (Assume P,
>     Assume (Imp P FALSE))
>     FALSE)
>   Q
> -- QED

Theorem 53. a \/ b, ~a |- b

>th_th53 = Theorem [Or P Q, Not P] Q
>pr_th53 =
> OrE
>   (Assume (Or P Q),
>   CTR (
>     ImpE
>       (Assume P,
>       Assume (Imp P FALSE))
>       FALSE)
>     Q,
>   ID
>     (Assume Q)
>     Q)
>   Q
> -- QED

6.5.10 Reductio ad Absurdum {RAA}

Theorem 54 (Double negation). ~~a |- a

>th_th54 = Theorem [Not (Not P)] P
>pr_th54 =
> RAA
>   (ImpE
>     (Assume (Imp P FALSE),
>     Assume (Imp (Imp P FALSE) FALSE))
>   FALSE)
>   P
> -- QED

6.5.11 Inferring the Operator Truth Tables

Exercise 19. Prove True /\ True.

>th_ex19_1 = Theorem [] (Imp (And TRUE TRUE) TRUE)
>pr_ex19_1 =
> ImpI
>   (AndEL
>     (Assume (And TRUE TRUE))
>     TRUE)
> (Imp (And TRUE TRUE) TRUE)

>th_ex19_2 = Theorem [] (Imp TRUE (And TRUE TRUE))
>pr_ex19_2 =
> ImpI
>   (AndI
>     (Assume TRUE, Assume TRUE)
>     (And TRUE TRUE))
>   (Imp TRUE (And TRUE TRUE))

6.7 Boolean Algebra: Equational Reasoning

6.7.2 Operations with Constants

Exercise 25. Simplify (P /\ False) \/ (Q /\ True).

(P /\ False) \/ (Q /\ True)
  False \/ (Q /\ True)            {/\ null}
  False \/ Q                      {\/ identity}
  Q \/ False                      {commutativity}
  Q                               {\/ null}

Exercise 26. Prove the equation (P /\ False) /\ True = False.

(P /\ False) /\ True
  False /\ True                   {/\ identity}
  False                           {/\ identity}
