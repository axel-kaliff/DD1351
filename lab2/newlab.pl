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


box_in_interval(_, [], _) :- fail.
box_in_interval([Nr, Value, _], [[[Nr, Value, _] | BoxTail] | _], [[Nr, Value, _] | BoxTail]).
box_in_interval([Nr, Value, _], [ _ | Tail], Box) :- 
    box_in_interval([Nr, Value, _], Tail, Box).


    get_value_in_target(_, [],_) :- fail.
    get_value_in_target(Nr, [[Nr, Value, _] | _], Value).
    get_value_in_target(Nr, [_ | Tail], Row) :- get_value_in_target(Nr, Tail, Row).



    %% ******** CHECKING PROOF *******

    %% End of proof
    valid_proof(_, _, [], _) :- !.

  %% ASSUMPTION

valid_proof(Prems, Proof, [[[Row, Value, assumption] | BoxTail] | Tail], ValidRows) :-
    valid_proof(Prems, Proof, BoxTail, [[Row, Value, assumption] | ValidRows]),
    valid_proof(Prems, Proof, Tail, [[[Row, Value, assumption] | BoxTail] | ValidRows]).

  %% PREMISE
    valid_proof(Prems, Proof, [[Row, Value, premise] | Tail], ValidRows) :-
        %% checks if the premise is valid
        premise_exists_in_scope(Value, Prems),
        %% continues with the proof-checking, adding the premise to the scope
        valid_proof(Prems, Proof, Tail, [[Row, Value, premise] | ValidRows]).


%% IMPLICATION ELIMINATION
   valid_proof(Prems, Proof, [[Row, Value, impel(X, Y)] | Tail], ValidRows) :-

        %% checks value of x in scope and copies it
        get_value_in_target(X, ValidRows, Copy1),

        %% checks that the row Y contains a imp(X, Y) rule
        get_value_in_target(Y, ValidRows, imp(Copy1, Value)),

        %% adds the row to scope as valid and continues with the tail
   valid_proof(Prems, Proof, Tail, [[Row, Value, impel(X, Y)] | ValidRows]).


%% IMPLICATION INTRODUCTION
   valid_proof(Prems, Proof, [[Row, imp(A,B), impint(X, Y)] | Tail], ValidRows) :-
    box_in_interval([X, A, _], ValidRows, Box),
    first_in_list(Box, [X, A, _]),
    last_in_list(Box, [Y, B,_ ]),
    valid_proof(Prems, Proof, Tail, [[Row, imp(A,B), impint(X,Y)] | ValidRows]).




%% AND INTRODUCTION
%% checks validity by pattern-matching the value of each row X and Y
valid_proof(Prems, Proof, [[Row, and(A,B), andint(X, Y)] | Tail], ValidRows) :-

%%checks if value A is found at row X
get_value_in_target(X, ValidRows, A),
%%checks if value B is found at row Y
get_value_in_target(Y, ValidRows, B),

%% adds row to scope and continues with tail
valid_proof(Prems,Proof, Tail, [[Row, and(A,B), andint(X,Y)] | ValidRows]).


%% AND ELMINATION 1

valid_proof(Prems,Proof, [[Row, Value, andel1(X)] | Tail], ValidRows) :-

%% checks if the given value is the first argument at row X
get_value_in_target(X, ValidRows, and(Value, _)),
valid_proof(Prems, Proof, Tail ,[[Row, Value, andel1(X)] | ValidRows]).


%% AND ELIMINATION 2
valid_proof(Prems,Proof, [[Row, Value, andel2(X)] | Tail], ValidRows) :-

%% checks if the given value is the second argument at row X
get_value_in_target(X, ValidRows, and(_, Value)),
valid_proof(Prems, Proof, Tail ,[[Row, Value, andel1(X)] | ValidRows]).

%% OR ELIMINATION
%% Checks (1) wether the value of row R is an or-statement, (2) that rows A and X are the beginning
%% and end of a box and (3) that the last rows of the boxes are in the given value
valid_proof(Prems, Proof, [[Row, Value, orel(R, A, B, X, Y)] | Tail], ValidRows) :-
  get_value_in_target(R, ValidRows, or(P, Q)),
  box_in_interval([A, P, _], ValidRows, first_box),
  box_in_interval([X, Q, _], ValidRows, second_box),
  first_in_list(first_box, [A, P, _]),
  first_in_list(second_box, [X, Q, _]),
  last_in_list(first_box, [B, Value, _]),
  last_in_list(second_box, [Y, Value, _]),
  valid_proof(Prems, Proof, Tail, [[Row, Value, orel(R, R, B, X, Y)] | ValidRows]).



%% OR INTRODUCTION 2
valid_proof(Prems, Proof, [[Row, or(A,B), orint2(X)] | Tail], ValidRows) :-
get_value_in_target(X, ValidRows, B),
valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint2(X)] | ValidRows]).

%% OR INTRODUCTION 1
valid_proof(Prems, Proof, [[Row, or(A,B), orint1(X)] | Tail], ValidRows) :-
%% checks if the scope contains the value A at row X
get_value_in_target(X, ValidRows, A),
valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint1(X)] | ValidRows]).


%% COPY
valid_proof(Prems, Proof, [[Row, Value, copy(X)] | Tail], ValidRows) :-
%% checks wether the value can be found at row X
get_value_in_target(X, ValidRows, Value),
valid_proof(Prems, Proof, Tail, [[Row, Value, copy(X)] | ValidRows]).

%% NEGATIVE INTRODUCTION
valid_proof(Prems, Proof, [[Row, neg(A), negint(X,Y)] | Tail], ValidRows) :-
  box_in_interval([X, A, _], ValidRows, Box),
  first_in_list(Box, [X, A, _]),
  last_in_list(Box, [Y, cont, _]),
  valid_proof(Prems, Proof, Tail, [[Row, neg(A), negint(X, Y)] | ValidRows]).



  


%% NEGATIVE ELIMINATION (CONTRADICTION)
valid_proof(Prems, Proof, [[Row, cont, negel(X, Y)] | Tail], ValidRows) :-

%% checks if A is in scope at row X and simultaneously negative at row Y (if A is both true and untrue in the proof)
get_value_in_target(X, ValidRows, A),
get_value_in_target(Y, ValidRows, (A)),

valid_proof(Prems, Proof, Tail, [[Row, cont, negel(X, Y)] | ValidRows]).

%% CONTRADICTION ELIMINATION
valid_proof(Prems, Proof, [[Row, Value, contel(X)] | Tail], ValidRows) :-
  get_value_in_target(X, ValidRows, cont),
  valid_proof(Prems, Proof, Tail, [[Row, Value, contel(X)] | ValidRows]).


%% NEGNEG INTRODUCTION
valid_proof(Prems, Proof, [[Row, Value, negnegint(X)] | Tail], ValidRows) :-
  get_value_in_target(X, ValidRows, Copy), neg(neg(Copy)) = Value,
  valid_proof(Prems, Proof, Tail, [[Row, Value, negnegint(X)] | ValidRows]).

%% NEGNEG ELIMINATION
valid_proof(Prems, Proof, [[Row, Value, negnegel(X)] | Tail], ValidRows) :-
  get_value_in_target(X, ValidRows, neg(neg(Value))),
  valid_proof(Prems, Proof, Tail, [[Row, Value, negnegel(X)] | ValidRows]).

%% PBC Rule
valid_proof(Prems, Proof, [[Row, Value, pbc(X, Y)] | Tail], ValidRows) :-
  box_in_interval([X, neg(Value), _], ValidRows, Box),
  first_in_list(Box, [X, neg(Value), _]),
  last_in_list(Box, [Y, cont, _]),
  valid_proof(Prems, Proof, Tail, [[Row, Value, pbc(X, Y)] | ValidRows]).

%% MT Rule
valid_proof(Prems, Proof, [[Row, neg(Value), mt(X,Y)] | Tail], ValidRows) :-
  get_value_in_target(X, ValidRows, imp(Value, B)),
  get_value_in_target(Y, ValidRows, neg(B)),
  valid_proof(Prems, Proof, Tail, [[Row, neg(Value), mt(X,Y)] | ValidRows]).

%% LEM
valid_proof(Prems, Proof, [[Row, or(A,B), lem] | Tail], ValidRows) :-
  A = neg(B) ; B = neg(A),
  valid_proof(Prems, Proof, Tail, [[Row, or(A,B), lem] | ValidRows]).




