# LOOP INVARANTS

## 1.1 循环不变量基础

Loop invariant 的理解：

* a loop invariant is not just a quantity that remains unchanged throughout executions of the loop body (a notion that has also been studied in the literature), but more speciﬁcally an “inductive invariant”

> 另：Class Invariant： In computer programming, specifically object-oriented programming, a class invariant (or type invariant) is an invariant used to constrain objects of a class. Methods of the class should preserve the invariant. The class invariant constrains the state stored in the object.


* 一个程序的结构

The notion of loop invariant is easy to express in the following loop syntax taken from Eiﬀel: 

    1 from 
    2 Init 
    3 invariant 
    4 Inv 
    5 until 
    6 Exit 
    7 variant 
    8 Var 
    9 loop 
    10 Body 
    11 end

(the variant clause helps establish termination as discussed below). Init and Body are each a compound (a list of instructions to be executed in sequence); either or both can be empty, although Body normally will not. Exit and Inv (the inductive invariant) are both Boolean expressions, that is to say, predicates on the program state. The semantics of the loop is:

    (1) Execute Init.

    (2) Then, if Exit has value True, do nothing; if it has value False, execute Body, and repeat step 2.

Postcondition

> In computer programming, a postcondition is a condition or predicate that must always be true just after the execution of some section of code or after an operation in a formal specification. 


## Questions

1. Lamport-style invariants?
1. invariant occurs in the study of dynamical systems.
1. domain theory?
1. By the transformation technique that yields the invariant from the postcondition . Here we have techniques such as uncoupling and constant relaxation.
1. 