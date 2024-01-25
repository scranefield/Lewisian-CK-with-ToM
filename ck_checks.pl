%%%%%%%% The conditions for common knowledge %%%%%%%
% These are defined as backward chaining rules, because a candidate A needs to be known first.
% They must be called from Prolog by wrapping them in pfc(...), e.g. ?- pfc(c1([...]).

% Definition of property c1(A). Call within a pfc(...) wrapper.
% Assumes A is ground (e.g. if the Prolog goal "percepts(top, A) ind bel(top, P)" has been run first
% for some specific ground P.

c1(A) <== { forall(member(Ai, A),
      	           (percept(top, Ai), percept(top>>af, Ai))) }.

% Definition of property c2(A). Call within a pfc(...) wrapper.
% Assumes A is ground (e.g. if the Prolog goal "percepts(top, A) ind percepts(top, P)" has been run first.

c2(A) <== { findall(P, af_scope_percept(P), Ps),
	    union(A, Ps, AfAugmentedA),
	    percepts(top>>af, AfAugmentedA) ind percepts(top>>af>>af, A)
	  }.

% Definition of property c3(A,P)). Call within a pfc(...) wrapper.
% Assumes A and P are ground (e.g. if the Prolog goal "percepts(top, A) ind percepts(top, P)" has been run first.

c3(A,P) <== { percepts(top>>af, A) ind bel(top>>af, P) }.

% Definition of property c4(A,P). Call within a pfc(...) wrapper.
% Assumes A and P are ground (e.g. if the Prolog goal "percepts(top, A) ind percepts(top, P)" has been run first.
% implemented for two cases: n=1 and n=2 as another check that theory of mind
% rules are working

c4_n1_and_n2(A,P) <==
    { findall(Pred, af_scope_percept(Pred), Preds),
      append(Preds, A, AWithAfScopePercepts),
      % Case n=1
      percepts(top>>af, A) ind bel(top>>af, P),
      percepts(top>>af>>af, A) ind bel(top>>af>>af, P),
      % Case n=2
      percepts(top>>af, AWithAfScopePercepts) ind bel(top>>af>>af, P),
      percepts(top>>af>>af, AWithAfScopePercepts) ind bel(top>>af>>af>>af, P) }.

% Definition of common knowledge of a belief term. The indication condition
% obtains a set of indicators A for P that any fool would know indicates P.
% Then A can be passed to the C1, C2 and C3 tests. Finally C4 is verified
% via the isomorphic models test.

ck(P) <== { percepts(top>>af, A) ind bel(top>>af, P) },
          c1(A), c2(A), c3(A,P),
	  {  isomorphic_models(top>>af, top>>af>>af) }.

% isomorphic_models/2

isomorphic_models(M1, M2) :-
    ( setof(M1PerceptPred, percept(M1, M1PerceptPred), M1PPs) -> true; M1PPs = []),
    ( setof(M2PerceptPred, percept(M2, M2PerceptPred), M2PPs) -> true; M2PPs = []),
    M1PPs == M2PPs,
    ( setof(M1BelPred, percept(M1, M1BelPred), M1BPs) -> true; M1BPs = []),
    ( setof(M2BelPred, percept(M2, M2BelPred), M2BPs) -> true; M2BPs = []),
    M1BPs = M2BPs,
    ( setof(rule(LConjuncts, RConjuncts),
	    L^R^((L ==> R),
		 comma_list(L, LConjuncts),
		 comma_list(R, RConjuncts),
		 rule_for_model(LConjuncts, RConjuncts, M1)),
	    M1Rules)
       -> true
    ; M1Rules = []
    ),
    ( setof(rule(LConjuncts, RConjuncts),
	    L^R^((L ==> R),
		 comma_list(L, LConjuncts),
		 comma_list(R, RConjuncts),
		 rule_for_model(LConjuncts, RConjuncts, M2)),
	    M2Rules)
      -> true
    ; M2Rules = []
    ),
    same_length(M1Rules, M2Rules),
    maplist(numbervars, M1Rules),
    maplist(numbervars, M2Rules),
    mapsubterms(model_mapped(M1, M2), M1Rules, MappedM1Rules),
    sort(M2Rules, SortedM2Rules), % Needed after numbervars call
    sort(MappedM1Rules, SortedMappedM1Rules),
    SortedM2Rules = SortedMappedM1Rules.

rule_for_model([], RConjuncts, M) :-
    !,
    once(( member(Conj, RConjuncts),
	  percept_or_belief_in_model(Conj, M) )).
rule_for_model(LConjuncts, _, M) :-
    LConjuncts \== [],
    once(( member(Conj, LConjuncts),
	  percept_or_belief_in_model(Conj, M) )).
   
percept_or_belief_in_model(percept(M2,_), M) :-
    % Special handling due to percept constraint rules having M>>Var on LHS
    \+ (M2 \= M).
percept_or_belief_in_model(bel(M,_), M).

model_mapped(M1, M2, M1Found, M2Returned) :-
    M1 = M1Parent>>_,
    M1Found = M1Parent>>V, var_number(V,_), !,
    M2 = M2Parent>>_,
    M2Returned = M2Parent>>V.    
model_mapped(M1, M2, M1, M2).

rules_valid :-
    % TO DO: add check that percept implication beliefs are acyclic.
    % TO DO: add check that rules do not contain the constant af, other than percept implication belief declarations.
    foreach(((L ==> R), comma_list(L, LConjuncts), LConjuncts \= [(_ ==> _)|_], comma_list(R, RConjuncts)),
	   (( setof(M, F^P^(member(LConj, LConjuncts), LConj =.. [F,M,P], memberchk(F, [percept, bel])), LMs) -> true
	    ; LMs = []
	    ),
	    ( setof(M, F^P^(member(RConj, RConjuncts), RConj =.. [F,M,P], memberchk(F, [percept, bel])), RMs) -> true
	    ; RMs = []
	    ),
	    ((LMs = [] ; length(LM, 1)) -> true
	    ; format("!!! Found a rule with more than one model on its left hand side:~n~w~n~n", [(L==>R)]),
	      Failed = 1
	    ),
	    [LM|_] = LMs,
	    ([RM] = RMs -> true
	    ; format("!!! Found a rule with no models or more than one model on its right hand side:~n~w~n~n", [(L==>R)]),
	      Failed = 1
	    ),
	    ((RM == LM ; RM = LM>>_ ; LM = top, RM = top) -> true
	    ; format("!!! Found a rule with a right hand side model (other than top) that is neither the same as on the left hand side or one level deeper:~n~w~n~n", [(L==>R)]),
	      format("LM: ~w; RM: ~w~n", [LM, RM]),
              Failed = 1
	    ),
	    ((\+ (RM = LM, member(bel(M,_), LConjuncts), member(percept(M,_), RConjuncts)) ) -> true
	    ; format("!!! Found a rule deriving fluents from beliefs in the same model:~n~w~n~n", [(L==>R)]),
	      Failed = 1
	    ),
	    ( ( LMs == [top], RMs == top 
              ; \+ (sub_term(T, (L ==> R)), nonvar(T), T =.. [F,_,P], memberchk(F, [percept, bel]), sub_term(S, P), S == af)
	      ) -> true
	    ; format("!!! Found a rule for M \\== top with af appearing within 2nd argument of percept/2 or bel/2:~n~w~n~n", [(L==>R)]),
	      Failed = 1
            )
	   )  
	  ),
  Failed == 1 -> fail ; true.
