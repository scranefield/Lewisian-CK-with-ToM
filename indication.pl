%%%%%%%% Definition of the indication relationship

:- op(90, xfx, ind).
:- use_module(library(clpb)).

% ind/2
% Right hand side must be instantiated

% Case where Indicators are given
percepts(M, Indicators) ind Fact :-
    ground(M), ground(Indicators), ground(Fact),
    ( functor(Fact, percept, 2) ; functor(Fact, bel, 2) ),
    !,
    once(((percepts(M, ComputedIndicators) ind Fact),
	  subset(ComputedIndicators, Indicators) )).

% Case where a minimal set of indicators is computed, i.e. MinIndicators is a var.
% Non-deterministic.

percepts(M, MinIndicators) ind Fact :-
    ground(Fact),
    ( functor(Fact, percept, 2) ; functor(Fact, bel, 2) ),
    !,
    proof_tree(Fact, ProofTree),
    percepts_and_non_redundancy_constraints(M, [], false, ProofTree, Inds, ConstraintVars, ConstraintOnIndInclusion),
    setof(MI,
	  MinIndicators1^MinIndicators1NoAfScope^ConstraintOnIndInclusion^(
	      solve_inclusion_constraints(Inds, ConstraintVars, ConstraintOnIndInclusion, MinIndicators1),
	      exclude([P]>>(af_scope_percept(P)), MinIndicators1, MinIndicators1NoAfScope),
	      percepts_cover(MinIndicators1NoAfScope, M, MI)
	  ),
	  MinIndicatorsOptions),
    member(MinIndicators, MinIndicatorsOptions).

% Case where a percepts/2 term appears on each side of ind/2
% Requires Inds1 to be ground for now
percepts(M1, Inds1) ind percepts(M2, Inds2) :-
    ( ground(Inds1) ->
	forall(member(Ind2, Inds2),
	       (percepts(M1, Inds1) ind percept(M2, Ind2)))
    ; instantiation_error(percepts(M1, Inds1) ind percepts(M2, Inds2))
    ).

% proof_tree/2, for use with Tim Finin's original version of PFC, not the logicmoo version
% Unlike the logicmoo version, justifications only show the last step of reasoning

proof_tree(user, user) :- !.
proof_tree(model_exists(M), t(model_exists(M), [do_not_care])) :- !.
proof_tree(FactOrRule, t(FactOrRule, Tree)) :-
    justifications(FactOrRule, Js),
    (( length(Js, N), N > 1 ) ->
         format("~n!!! Warning: Multiple justifications for ~w:~n~w~n", [FactOrRule, Js])
    ; true
    ),
    [J|_] = Js,
    maplist(proof_tree, J, Tree).

ancestor_of(P1, P2, ProofTree) :-
    once((sub_term(ST, ProofTree), nonvar(ST), ST = t(P2,SubT))),
    once((sub_term(SST, SubT), nonvar(SST), SST = t(P1,_))).

% percepts_and_non_redundancy_constraints/7
%
% Model, PriorInds and ParentWasInd arguments are first for convenient use of maplist. Indexing is not
% affected because SWI Prolog does just-in-time indexing.
% TO DO: Use the lambda predicate notation from module yall in the maplist calls, allowing the proof tree
% to be the first argument of this predicate.
% TO DO: Simplify these clauses by first generating a subtree of the ProofTree containing only the
% percepts in model M.
% Note: Passing PriorInds in the secon argument does not eliminate all duplicated percepts in the results, as a percept can
% appear multiple times at different levels of the proof tree. See the definition of the ind relation
% Any remaining repetitions are handled by solve_inclusion_constraints/4.

percepts_and_non_redundancy_constraints(M, PriorInds, _, t(Fact, Subtrees), Inds, ConstraintVars, *(SubTreeConstraints)) :-
    Fact =.. [_, LongerM, _],
    M \== LongerM,
    sub_term(M, LongerM),
    !,
    maplist(percepts_and_non_redundancy_constraints(M, PriorInds, false), Subtrees, IndsLists, ConstraintVarsLists, SubTreeConstraints),
    flatten(IndsLists, Inds),
    flatten(ConstraintVarsLists, ConstraintVars).
percepts_and_non_redundancy_constraints(M, _, ParentWasInd, t(Fact, _), [], [], Bool) :-
    Fact =.. [_, ShorterM, _],
    M \== ShorterM,
    sub_term(ShorterM, M),
    !,
    ( ParentWasInd -> Bool = 0
    ; Bool = 1
    ).
percepts_and_non_redundancy_constraints(M, PriorInds, ParentWasInd, t((_ ==> _), Subtrees), Inds, ConstraintVars, *(SubtreeConstraints)) :- 
    maplist(percepts_and_non_redundancy_constraints(M, PriorInds, ParentWasInd), Subtrees, IndsLists, ConstraintVarsLists, SubtreeConstraints),
    flatten(IndsLists, Inds),
    flatten(ConstraintVarsLists, ConstraintVars).
percepts_and_non_redundancy_constraints(M, PriorInds, _, t(bel(M, _), Subtrees), Inds, ConstraintVars, *(SubtreeConstraints)) :-
    maplist(percepts_and_non_redundancy_constraints(M, PriorInds, false), Subtrees, IndsLists, ConstraintVarsLists, SubtreeConstraints),
    flatten(IndsLists, Inds),
    flatten(ConstraintVarsLists, ConstraintVars).
percepts_and_non_redundancy_constraints(M, PriorInds, ParentWasInd, t(percept(M, P), _), [], [], Bool) :-
    memberchk(percept(M,P), PriorInds),
    !,
    ( ParentWasInd -> Bool = 0
    ; Bool = 1
    ).
percepts_and_non_redundancy_constraints(M, PriorInds, _, t(percept(M, P), Subtrees), [percept(M, P)|Inds], [X|ConstraintVars], X # *(SubtreeConstraints)) :-
    maplist(percepts_and_non_redundancy_constraints(M, [percept(M, P) | PriorInds], true), Subtrees, IndsLists, ConstraintVarsLists, SubtreeConstraints),
    flatten(IndsLists, Inds),
    flatten(ConstraintVarsLists, ConstraintVars).
percepts_and_non_redundancy_constraints(_, _, ParentWasInd, Term, [], [], Bool) :-
    memberchk(Term, [t(model_exists(_),_), t(af_scope_percept(_),_), user]),
    ( ParentWasInd -> Bool = 0
    ; Bool = 1
    ).

solve_inclusion_constraints(Candidates, ConstraintVars, InclusionConstraints, Selection) :-
    sat(InclusionConstraints),
    findall(Item-Index, nth1(Index, Candidates, Item), ItemIndexPairs),
    sort(ItemIndexPairs, SortedItemIndexPairs),
    group_pairs_by_key(SortedItemIndexPairs, ItemIndicesPairs),
    pairs_values(ItemIndicesPairs, RepeatedElementIndexLists),
    same_vars_constraint(RepeatedElementIndexLists, ConstraintVars, SameItemConstraint),
    sat(SameItemConstraint),
    labeling(ConstraintVars),
    setof(Candidate, I^( nth1(I, ConstraintVars, 1), nth1(I, Candidates, percept(_, Candidate)) ), Selection).

% The lambda predicate notation below ( {...}/[Args]>>Goal ) is supported by the SWI Prolog's yall module

percepts_cover(Ps, M, Cover) :-
    predecessor_list(Ps, M, [], [], PredecessorList),
    keysort(PredecessorList, SortedPredList),
    group_pairs_by_key(SortedPredList, PerceptsToPredecessors),
    pairs_keys(PerceptsToPredecessors, NonLeaves),
    subtract(Ps, NonLeaves, Leaves),
    maplist([X,Y]>>(Y=X-[]), Leaves, LeavesToEmptyLists),
    union(PerceptsToPredecessors, LeavesToEmptyLists, FullPerceptPredsMap),
    keysort(FullPerceptPredsMap, SortedPerceptPredsMap),
    pairs_keys(SortedPerceptPredsMap, AllNodes),
    length(AllNodes, N),
    length(ConstraintVars, N),
    length(Constraints, N),
    maplist(
	{AllNodes,ConstraintVars,Constraints}/[P-Preds,PConstraint]>>predecessor_constraint(P-Preds, AllNodes, ConstraintVars, Constraints, PConstraint),
	SortedPerceptPredsMap,
	PredConstraints
    ),
    findall(Node,
	    ( member(Node-[], SortedPerceptPredsMap),
	      \+ member(_-Node, PredecessorList)
	    ),
	    DisconnectedNodes),
    maplist({AllNodes,ConstraintVars}/[Leaf,LeafConstraint]>>require_node_constraint(Leaf, AllNodes, ConstraintVars, Constraints, LeafConstraint),
	    DisconnectedNodes,
	    DisconnectedNodeConstraints),
    maplist({M}/[Node,P]>>(P = percept(M, Node)), AllNodes, AllPercepts),
    solve_inclusion_constraints(AllPercepts, ConstraintVars, *(PredConstraints) * *(DisconnectedNodeConstraints), Cover).

predecessor_constraint(P-Preds, AllNodes, ConstraintVars, Constraints, PConstraintForParent) :-
    ( node_var_and_constraint(P, AllNodes, ConstraintVars, Constraints, PVar, PConstraint),
      ( Preds == [] ->
	    PConstraint = PVar,
	    PConstraintForParent = 1
      ; maplist({AllNodes, ConstraintVars, Constraints}/[X,XConstraint]>>
		  ( node_var_and_constraint(X, AllNodes, ConstraintVars, Constraints, XVar, XConstraint),
		    XConstraint = XVar
		  ),
		Preds,
		PredsConstraints),
	PConstraintForParent = PVar # *(PredsConstraints)
      )
    ).

require_node_constraint(Leaf, AllNodes, ConstraintVars, Constraints, LeafVar) :-
    node_var_and_constraint(Leaf, AllNodes, ConstraintVars, Constraints, LeafVar, LeafVar).
    

node_var_and_constraint(Node, AllNodes, ConstraintVars, Constraints, Var, Constraint) :-
    nth1(I, AllNodes, Node),
    nth1(I, ConstraintVars, Var),
    nth1(I, Constraints, Constraint).

predecessor_list([], _, _, L, L).
predecessor_list([H|T], M, Seen, PredListSoFar, PredList) :-
    findall(P, bel(M, percept_implication(H, P)), Ps),
    maplist({H}/[P,PredRel]>>(PredRel=P-H), Ps, NewPredsList),
    append(NewPredsList, PredListSoFar, UpdatedPredList),
    ( memberchk(P, Seen) ->
        predecessor_list(T, M, Seen, UpdatedPredList, PredList)
    ; predecessor_list([Seen|T], M, [H|Seen], UpdatedPredList, PredList)
    ).

same_vars_constraint([], _, 1).
same_vars_constraint([IndexList|T], ConstraintVars, Constraint) :-
    length(IndexList,N),
    ( N > 1 ->
          maplist({ConstraintVars}/[Index,SelectedVar]>>nth1(Index,ConstraintVars,SelectedVar), IndexList, SelectedVars),
	  Constraint = card([0,N],SelectedVars) * TailConstraint
    ; Constraint = TailConstraint
    ),
    same_vars_constraint(T, ConstraintVars, TailConstraint).
