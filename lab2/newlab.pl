verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_goal(Goal, Proof),
    valid_proof(Prems, Proof, Proof, []), !.


valid_goal(Goal, Proof) :-
    last_in_list(Proof, Row),
    get_value(Row, Value),
    Goal = Value, !.

    %%****** SUPPORT FUNCTIONS ******


    %% Checks if a given premise is valid
    %% if there are no more premises in the scope the proposed premise is not valid
    premise_exists_in_scope(_, []) :- fail.

    %% if the premise exists in the scope
    premise_exists_in_scope(Value, [Value | _]).

    %% checks the next element by sending the tail
    premise_exists_in_scope(Value, [_ | Tail]) :- premise_exists_in_scope(Value, Tail).
    




    %% ** Finding elements **
    first_in_list([Head |_], Head).

    last_in_list([Head | []], Head).
    last_in_list([_| Tail], Head) :- last_in_list(Tail, Head).

    get_value([_, Head, _], Head).
    get_nr([Nr, _, _], Nr).


    get_value_in_target(_, [],_) :- fail.
    get_value_in_target(Nr, [[Nr, Value, _] | _], Value).
    get_value_in_target(Nr, [_ | Tail], Row) :- get_value_in_target(Nr, Tail, Row).






    %% ******** CHECKING PROOF *******

    %% End of proof
    valid_proof(_, _, [], _) :- !.
    

  %% PREMISE
    valid_proof(Prems, Proof, [[Row, Value, premise] | Tail], Scope) :- 
        %% checks if the premise is valid
        premise_exists_in_scope(Value, Prems), 
        %% continues with the proof-checking, adding the premise to the scope
        valid_proof(Prems, Proof, Tail, [[Row, Value, premise] | Scope]).


%% IMPLICATION ELIMINATION
   valid_proof(Prems, Proof, [[Row, Value, impel(X, Y)] | Tail], Scope) :-

        get_value_in_target(X, Scope, Copy1),
        get_value_in_target(Y, Scope, imp(Copy1, Value)),

        %% adds the row to scope as valid
   valid_proof(Prems, Proof, Tail, [[Row, Value, impel(X, Y)] | Scope]).






