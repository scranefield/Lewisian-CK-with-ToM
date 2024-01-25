
%%%%%%%% Utility predicates %%%%%%%%

% From https://stackoverflow.com/questions/31181756/determine-the-maximum-depth-of-a-term
depth(T, D) :-
  compound(T)
  ->  aggregate(max(B+1), P^A^(arg(P, T, A), depth(A, B)), D)
  ;   D = 0.

conjunction_head(Conj, Head) :-
    ( (Head,_) = Conj -> true
    ; Head = Conj
    ).

model_suffix(M, M) :- atom(M).
model_suffix(_>>L, L).

interesting_nesting(_ >> af).

append(M, A, interesting_nesting(M1), interesting_nesting(M2)) :-
    mapsubterms(add_model_name_suffix(M, A), M1, M2).
append(M, A, BelOrPercept, NewBelOrPercept) :-
    BelOrPercept =.. [F, M1, P], memberchk(F, [bel, percept]),
    mapsubterms(add_model_name_suffix(M, A), M1, M2),
    mapsubterms(append(not_relevant, A), P, NewP),
    NewBelOrPercept =.. [F, M2, NewP].

add_model_name_suffix(M, A, M, M>>A).

