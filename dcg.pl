:- use_module(betaReduction).


% Operators and their precedence
:- op(950,yfx,@).
:- op(900, yfx, >).
:- op(850, yfx, v).
:- op(800,yfx, &).
:- op(750, fy, ~).

% Composition of semantic representation
s(S) --> np(NP), vp(VP), {betaConv((NP @ VP), S)}.
np(PN) --> pn(PN).
np(NP) --> det(Det), noun(Noun), {betaConv((Det @ Noun), NP)}.
vp(IV) --> iv(IV).
vp(VP) --> tv(TV), np(NP), {betaConv((TV @ NP),VP)}.

% Lexemes and their representations
noun(lam(X,footmassage(X))) --> [foot,massage].
noun(lam(X,woman(X))) --> [woman].
iv(lam(X,walk(X))) --> [walks].

pn(lam(P,P @ vincent)) --> [vincent].
pn(lam(P,P @ mia)) --> [mia].
det(lam(P,lam(Q, all(X, (P @ X) > (Q @ X))))) --> [every].
det(lam(P,lam(Q,some(X,(P @ X) & (Q @ X))))) --> [a].
tv(lam(W, lam(Z, (W @ lam(X, loves(X,Z)))))) --> [loves].
