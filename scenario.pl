% Initial percepts of the agent
==> percept(top, citizen(me)).
==> percept(top, location(me, agora)).
==> percept(top, states(m27, traitor(hipparchus))).
==> percept(top, affordance(m27, public_information)).

% af scope predicate declarations
==> af_scope_percept(citizen(af)).
==> af_scope_percept(location(af, agora)).

% Create initial af scope percepts:
af_scope_percept(P) ==> percept(top, P).

% ToM 1: Nested models contain the af scope percepts
percept(top, P), af_scope_percept(P),
bel(top, citizen(C)), { interesting_nesting(top>>C) }
==> percept(top>>C, P).

% Percept implication beliefs
==> bel(top, percept_implication(
               location(me, agora),
               states(m27, traitor(hipparchus)))).
==> bel(top, percept_implication(
               location(me, agora),
               affordance(m27, public_information))).

% Create implied percepts
percept(top, P), bel(top, percept_implication(P, Q))
==> percept(top, Q).

% ToM 2: Other citizens share percept implications
percept(top, P), bel(top, percept_implication(P, Q)),
bel(top, citizen(C)), { interesting_nesting(top>>C) }
==> bel(top>>C, percept_implication(P, Q)).

% ToM 3: Believe what you perceive
percept(top, P) ==> bel(top, P).

% ToM 4: Citizens believe they are citizens
bel(top, citizen(C)), { interesting_nesting(top>>C) }
==> bel(top>>C, citizen(me)).

% ToM 5: Believe public information on monuments
bel(top, states(Monument,S)),
percept(top, affordance(Monument, public_information))
==> bel(top, S).

% ToM 6: Agents in the agora perceive they are there
bel(top, location(C, agora)),
{ interesting_nesting(top>>C) }
==> percept(top>>C, location(me, agora)).

% ToM 7: Other citizens have the same rules as me
( Conditions ==> Conclusion ),
{ functor(Conclusion,F,2), memberchk(F, [percept, bel]),
  conjunction_head(Conditions, Condition),
  ( Condition = percept(M1,_) ; Condition = bel(M1,_) ),
  depth(M1, D), D < 2 },
bel(M1, citizen(C)), { interesting_nesting(M1>>C) }
==>
{ mapsubterms(append(M1,C), Conditions, ModifiedConds),
  mapsubterms(append(M1,C), Conclusion, ModifiedConcl)
},
( ModifiedConds ==> ModifiedConcl ).
