:- module(betaReduction,[betaConv/2]).

:- op(950,yfx,@).
:- op(900, yfx, >).
:- op(850, yfx, v).
:- op(800,yfx, &).
:- op(750, fy, ~).

% Given Term, it spits out the symbol and the list of arguments as a single list
compose(Term,Symbol,ArgList):- 
    Term =.. [Symbol|ArgList].

/*===============================================================
UNIFORM SUBSTITUTION MODULE (Does mindless uniform substitution, to the extent which will be needed by us)
==================================================*/

% In Term, substitute Exp for Var uniformly to produce the Result
substitute(VarTerm, Var, Exp, Result):-
    var(VarTerm),
    VarTerm == Var,
    Result = Exp.

substitute(VarTerm, _, _, Result):-
    var(VarTerm),
    Result = VarTerm.

substitute(lam(Var1,Formula),Var2,Exp,Result):-
    Var1 == Var2,
    substitute(Formula,Var2,Exp,NewRes),
    Result = lam(Exp,NewRes).

substitute(lam(Var1,Formula),Var2,Exp,Result):-
    substitute(Formula,Var2,Exp,NewRes),
    Result = lam(Var1,NewRes).

substitute(some(Var1,Formula),Var2,Exp,Result):-
    Var1 == Var2,
    substitute(Formula,Var2,Exp,NewRes),
    Result = some(Exp,NewRes).

substitute(some(Var1,Formula),Var2,Exp,Result):-
    substitute(Formula,Var2,Exp,NewRes),
    Result = some(Var1,NewRes).

substitute(all(Var1,Formula),Var2,Exp,Result):-
    Var1 == Var2,
    substitute(Formula,Var2,Exp,NewRes),
    Result = all(Exp,NewRes).

substitute(all(Var1,Formula),Var2,Exp,Result):-
    substitute(Formula,Var2,Exp,NewRes),
    Result = all(Var1,NewRes).

substitute(F1 @ F2, Var, Exp, Result):-
    substitute(F1,Var,Exp,Res1),
    substitute(F2,Var,Exp,Res2),
    Result = (Res1 @ Res2).

substitute(F1 & F2, Var, Exp, Result):-
    substitute(F1,Var,Exp,Res1),
    substitute(F2,Var,Exp,Res2),
    Result = (Res1 & Res2).

substitute(F1 v F2, Var, Exp, Result):-
    substitute(F1,Var,Exp,Res1),
    substitute(F2,Var,Exp,Res2),
    Result = (Res1 v Res2).

substitute(F1 > F2, Var, Exp, Result):-
    substitute(F1,Var,Exp,Res1),
    substitute(F2,Var,Exp,Res2),
    Result = (Res1 > Res2).

substitute(~F2, Var, Exp, Result):-
    substitute(F2,Var,Exp,Res1),
    Result = (~Res1).

substitute(Term,Var,Exp,Result):- 
    compose(Term,Operator,ArgList),
    listsubs(ArgList,Var,Exp,ResList),
    compose(Result,Operator,ResList).

% Program that substitutes one element for another in a whole list
listsubs(List,PreElem,PostElem,Result):-
    listsubsAcc(List,[],PreElem,PostElem,Result).

listsubsAcc([H|T],Acc,PreElem,PostElem,Res):-
    H == PreElem,
    append(Acc,[PostElem],NewAcc),
    listsubsAcc(T,NewAcc,PreElem,PostElem,Res).

listsubsAcc([H|T],Acc,PreElem,PostElem,Res):-
    append(Acc,[H],NewAcc),
    listsubsAcc(T,NewAcc,PreElem,PostElem,Res).

listsubsAcc([],Acc,_,_,Acc).

/*==================================
Alpha Conversion module
==================================*/
% takes a Lambda-Term and produces an alpha equivalent lambda term
alphaConv(Term,Term):-
    var(Term).

alphaConv(lam(X,Form),Result):-
    substitute(Form,X,Y,Res),
    alphaConv(Res,FormRes),
    Result = lam(Y,FormRes).

alphaConv(some(X,Form),Result):-
    substitute(Form,X,Y,Res),
    alphaConv(Res,FormRes),
    Result = some(Y,FormRes).

alphaConv(all(X,Form),Result):-
    substitute(Form,X,Y,Res),
    alphaConv(Res,FormRes),
    Result = all(Y,FormRes).

alphaConv(F1 & F2, Result):-
    alphaConv(F1,Res1),
    alphaConv(F2,Res2),
    Result =(Res1 & Res2).

alphaConv(F1 @ F2, Result):-
    alphaConv(F1,Res1),
    alphaConv(F2,Res2),
    Result =(Res1 @ Res2).
alphaConv(F1 v F2, Result):-
    alphaConv(F1,Res1),
    alphaConv(F2,Res2),
    Result =(Res1 v Res2).
alphaConv(F1 v F2, Result):-
    alphaConv(F1,Res1),
    alphaConv(F2,Res2),
    Result =(Res1 v Res2).

alphaConv(F1 > F2, Result):-
    alphaConv(F1,Res1),
    alphaConv(F2,Res2),
    Result =(Res1 > Res2).

alphaConv(~F1, Result):-
    alphaConv(F1,Res),
    Result =(~Res).

alphaConv(Term,Term).



/*====================================
Parallel Reduct does every possible beta conversion in
a term that's visible in one step
===================*/

parallelReduct(Term,Term):-
    var(Term).

parallelReduct(lam(X,T),Res):-
    parallelReduct(T,ResT),
    Res = lam(X,ResT).

parallelReduct(Term @ F, Res):-
    var(Term),
    parallelReduct(F,ResF),
    Res = (Term @ ResF).

parallelReduct((lam(X,T) @ U), Res):-
    parallelReduct(T,ResT),
    parallelReduct(U, ResU),
    alphaConv(ResT,NewT),
    substitute(NewT,X,ResU,Res).

parallelReduct(F1 @ F2, Res):-
    parallelReduct(F1,Res1),
    parallelReduct(F2,Res2),
    Res = (Res1 @ Res2).

parallelReduct(F1 & F2, Res):-
    parallelReduct(F1,Res1),
    parallelReduct(F2,Res2),
    Res = (Res1 & Res2).

parallelReduct(F1 v F2, Res):-
    parallelReduct(F1,Res1),
    parallelReduct(F2,Res2),
    Res = (Res1 v Res2).

parallelReduct(F1 > F2, Res):-
    parallelReduct(F1,Res1),
    parallelReduct(F2,Res2),
    Res = (Res1 > Res2).

parallelReduct(all(X,Term),Res):-
    parallelReduct(Term,ResT),
    Res = all(X,ResT).

parallelReduct(some(X,Term), Res):-
    parallelReduct(Term,ResT),
    Res = some(X,ResT).

parallelReduct(~Term, Res):-
    parallelReduct(Term,ResT),
    Res = (~ ResT).

parallelReduct(Term,Term).

nTimesParallelRed(Term,0,Term).

nTimesParallelRed(Term, N, Res):-
    parallelReduct(Term,OneStepRes),
    M is N - 1,
    nTimesParallelRed(OneStepRes, M, Res).

/*===========================
It counts the number of lambdas. We will do as many parallel reducts
to make sure we have completely reduced the expression.
=====================*/
countLambda(Term,0):-
    var(Term).

countLambda(lam(_,T),Number):-
    countLambda(T,NewNumber),
    Number is NewNumber + 1.

countLambda((F1 @ F2), Number):-
    countLambda(F1, Number1),
    countLambda(F2, Number2),
    Number is (Number1 + Number2).% Operators and their precedence
    
countLambda(_,0).

/*=======
beta conversion is just parallel reduct done enough number of times.
Here we use the fact that no new lambdas are introduced anywhere during beta conversion, and so
doing the parallel reduct as many times as the number of lambdas appearing in the term
will make sure that we have done all possible beta conversions.
=========*/

betaConv(Term,Res):-
    countLambda(Term,N),
    nTimesParallelRed(Term,N,Res).