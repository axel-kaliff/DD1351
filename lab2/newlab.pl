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

        %% checks value of x in scope and copies it
        get_value_in_target(X, Scope, Copy1),

        %% checks that the row Y contains a imp(X, Y) rule
        get_value_in_target(Y, Scope, imp(Copy1, Value)),

        %% adds the row to scope as valid and continues with the tail
   valid_proof(Prems, Proof, Tail, [[Row, Value, impel(X, Y)] | Scope]).


%% IMPLICATION INTRODUCTION
%%   valid_proof(Prems, Proof, [[Row, Value, impel(X, Y)] | Tail], Scope) :-





%% AND INTRODUCTION
%% checks validity by pattern-matching the value of each row X and Y
valid_proof(Prems, Proof, [[Row, and(A,B), andint(X, Y)] | Tail], Scope) :-

%%checks if value A is found at row X
get_value_in_target(X, Scope, A),
%%checks if value B is found at row Y 
get_value_in_target(Y, Scope, B),

%% adds row to scope and continues with tail
valid_proof(Prems,Proof, Tail, [[Row, and(A,B), andint(X,Y)] | Scope]).


%% AND ELMINATION 1

valid_proof(Prems,Proof, [[Row, Value, andel1(X)] | Tail], Scope]) :- 

%% checks if the given value is the first argument at row X
get_value_in_target(X, Scope, and(Value, _)),
valid_proof(Prems, Proof, Tail ,[[Row, Value, andel1(X)] | Scope]).


%% AND ELIMINATION 2
valid_proof(Prems,Proof, [[Row, Value, andel2(X)] | Tail], Scope]) :- 

%% checks if the given value is the second argument at row X
get_value_in_target(X, Scope, and(_, Value)),
valid_proof(Prems, Proof, Tail ,[[Row, Value, andel1(X)] | Scope]).


%% OR INTRODUCTION 1
valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint1(X)] | Tail], Scope) :-
%% checks if the scope contains the value A at row X
get_value_in_target(X, Scope, A),
valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint1(X)] | Scope]).

%% OR INTRODUCTION 2
valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint2(X)] | Tail], Scope) :-
get_value_in_target(X, Scope, B),
valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint2(X)] | Scope]).

%% COPY
valid_proof(Prems, Proof, [[Row, Value, copy(X)] | Tail], Scope) :-
get_value_in_target(X, Scope, Value),
valid_proof(Prems, Proof, Tail, [[Row, Value, copy(X)] | Scope]).


%% NEGATIVE ELIMINATION (CONTRADICTION)
valid_proof(Prems, Proof, [[Row, Value, negel(X)] | Tail], Scope) :-

%% checks if A is in scope at row X and simultaneously negative at row Y (if A is both true and untrue in the proof)
get_value_in_target(X, Scope, A),
get_value_in_target(Y, Scope, (A)),

valid_proof(Prems, Proof, [[Row, cont, negel(X, Y)] | Scope]).

%% CONTRADICTION ELIMINATION
valid_proof(Prems, Proof, [[Row, Value, contel(X)] | Tail], Scope) :-
  get_value_in_target(X, Scope, cont),
  valid_proof(Prems, Proof, Tail, [[Row, Value, contel(X)] | Scope]).
  

%% NEGNEG INTRODUCTION
valid_proof(Prems, Proof, [[Row, Value, negnegint(X)] | Tail], Scope) :-
  get_value_in_target(X, Scope, Copy), neg(neg(Copy)) = Value,
  valid_proof(Prems, Proof, Tail, [[Row, Value, negnegint(X)] | Scope]).

%% NEGNEG ELIMINATION
valid_proof(Prems, Proof, [[Row, Value, negnegel(X)] | Tail], Scope) :-
  get_value_in_target(X, Scope, neg(neg(Value))),
  valid_proof(Prems, Proof, Tail, [[Row, Value, negnegel(X)] | Scope]).


