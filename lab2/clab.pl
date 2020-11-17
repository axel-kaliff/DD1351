verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_goal(Goal, Proof),
    valid_proof(Prems, Proof, Proof, []), !.

%% True if the given goal is the value of the last
%% line in the Proof
valid_goal(Goal, Proof) :-
    get_last(Proof, Row),
    get_value(Row, Value),
    Goal = Value, !.

%% Checks if the given Value exists in the given premise-list
valid_premise(_, []):- fail.
valid_premise(Value, [Value | _]).
valid_premise(Value, [_ | Tail]) :- valid_premise(Value, Tail).

%% Unifies or matches the first element in the list
get_first([Head | _], Head).
%% Unifies or matches the given variable with the last
%% element in the given list.
get_last([Head | []], Head).
get_last([_| Tail], Head) :- get_last(Tail, Head).

%% Unifies or matches the given vairable with the 
%% value (or row-number for get_nr) of the given proof-row
get_value([_, Head, _], Head).
get_nr([Nr, _, _], Nr).

%% Checks if the given proof-row can match the signature of
%% a box in the given scope-list. If the scope-list is empty
%% at any point, it will fail.
%% If Box is not declared it will try to unify with 
%% the matched box in the scope-list.
box_in_scope(_, [], _) :- fail.
box_in_scope([Nr, Value, _], [[[Nr, Value, _] | BoxTail] | _], [[Nr, Value, _] | BoxTail]).
box_in_scope([Nr, Value, _], [ _ | Tail], Box) :- 
    box_in_scope([Nr, Value, _], Tail, Box).

%% Peeks at the proof-row of the scope-list and 
%% tries to unify or match the value and/or 
%% row-number with an element in the given scope-list.
peek(_, [], _) :- fail.
peek(Nr, [[Nr, Value, _] | _], Value).
peek(Nr, [_ | Tail], Row) :- peek(Nr, Tail, Row).       

%% Basecase
%% Returns true in all cases as it symbolizes the end of the current
%% proof-list
valid_proof(_, _, [], _) :- !.

%% Case where it matches for the characteristic signature of 
%% a box. It will be a list in place of a proof-row inside the proof-list.
%% Also, the rule of the row will be an assumption
valid_proof(Prems, Proof, [[[Row, Value, assumption] | BoxTail] | Tail], Scope) :-
    valid_proof(Prems, Proof, BoxTail, [[Row, Value, assumption] | Scope]),
    valid_proof(Prems, Proof, Tail, [[[Row, Value, assumption] | BoxTail] | Scope]).

%% Case where the rule of the row is a premise.
%% It will then call the predicate valid_premise to 
%% check the validity of the assumed premise.
valid_proof(Prems, Proof, [[Row, Value, premise] | Tail], Scope) :-
    valid_premise(Value, Prems),
    valid_proof(Prems, Proof, Tail, [[Row, Value, premise] | Scope]).

%% Case where the rule used to prove Value is implication elimination
%% Checks that the rule follows what's expected of 
%% implication-elimination.
valid_proof(Prems, Proof, [[Row, Value, impel(X,Y)] | Tail], Scope) :-
    peek(X, Scope, Copy1),
    peek(Y, Scope, imp(Copy1, Value)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, impel(X,Y)] | Scope]).

%% Case where the rule used to prove the Value is implication-introduction
%% It checks if the rule follows what's expected of 
%% implication-introduction.
valid_proof(Prems, Proof, [[Row, imp(A,B), impint(X,Y)] | Tail], Scope) :-
    box_in_scope([X, A, _], Scope, Box),
    get_first(Box, [X, A, _]),
    get_last(Box, [Y, B, _]),
    valid_proof(Prems, Proof, Tail, [[Row, imp(A,B), impint(X,Y)] | Scope]).

%% Matches the case where and-introduction is being used.
%% It checks its validity by pattern-match the value of 
%% each row X and Y.
valid_proof(Prems, Proof, [[Row, and(A,B), andint(X,Y)] | Tail], Scope) :-
    peek(X, Scope, A),
    peek(Y, Scope, B),
    valid_proof(Prems, Proof, Tail, [[Row, and(A,B), andint(X,Y)] | Scope]).

%% Matches the case where and-elimination-1 is used. 
%% It checks if Value is the first argument of the
%% and-statement at row X.
valid_proof(Prems, Proof, [[Row, Value, andel1(X)] | Tail], Scope) :-
    peek(X, Scope, and(Value, _a)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, andel1(X)] | Scope]).

%% Matches the case where and-elimination-2 is used. 
%% It checks if Value is the second argument of the
%% and-statement at row X.
valid_proof(Prems, Proof, [[Row, Value, andel2(X)] | Tail], Scope) :-
    peek(X, Scope, and(_a, Value)),
    valid_proof(Prems, Proof, Tail, [[Row, Value, andel2(X)] | Scope]).

%% Matches the case where or-introduction-1 is used.
%% It checks if the first argument of Value is the value of row X.
valid_proof(Prems, Proof, [[Row, or(A,B), orint1(X)] | Tail], Scope) :-
    peek(X, Scope, A),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint1(X)] | Scope]).

%% Matches the case where or-introduction-2 is used.
%% It checks if the second argument of Value is the value of row X.
valid_proof(Prems, Proof, [[Row, or(A,B), orint2(X)] | Tail], Scope) :-
    peek(X, Scope, B),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint2(X)] | Scope]).

%% Or-elimination checks three things: 
%%      - It checks that the value of row R is 
%%      an or-statement
%%      - It checks that rows A and X are row-signatures of 
%%      a box inside the scope.
%%      - It checks that the value of the first row of each box
%%      is present in the or-statement on row R
%%      - It checks that the value of the last rows of the boxes are present
%%      in Value.
valid_proof(Prems, Proof, [[Row, Value, orel(R, A, B, X, Y)] | Tail], Scope) :- 
    peek(R, Scope, or(P,Q)),
    box_in_scope([A, P, _], Scope, Box1),
    box_in_scope([X, Q, _], Scope, Box2),
    get_first(Box1, [A, P, _]),
    get_first(Box2, [X, Q, _]),
    get_last(Box1, [B, Value, _]),
    get_last(Box2, [Y, Value, _]),
    valid_proof(Prems, Proof, Tail, [[Row, Value, orel(R, R, B, X, Y)] | Scope]).

%% Checks if Value is the value on row X
valid_proof(Prems, Proof, [[Row, Value, copy(X)] | Tail], Scope) :-
    peek(X, Scope, Value),
    valid_proof(Prems, Proof, Tail, [[Row, Value, copy(X)] | Scope]).

%% Checks if there is a contradiction in the last row of the box
%% starting at row X to check the valitity of the rule used.
valid_proof(Prems, Proof, [[Row, neg(A), negint(X,Y)] | Tail], Scope) :-
    box_in_scope([X, A, _], Scope, Box),
    get_first(Box, [X, A, _]),
    get_last(Box, [Y, cont, _]),
    valid_proof(Prems, Proof, Tail, [[Row, neg(A), negint(X,Y)] | Scope]).

%% Checks that the contradiction is valid by checking that the
%% value on row Y is the negated value from row X.
valid_proof(Prems, Proof, [[Row, cont, negel(X,Y)] | Tail], Scope) :-
    peek(X, Scope, A),
    peek(Y, Scope, neg(A)),
    valid_proof(Prems, Proof, Tail, [[Row, cont, negel(X,Y)] | Scope]).

%% Checks if there is a contradiction declared on row X
valid_proof(Prems, Proof, [[Row, Value, contel(X)] | Tail], Scope) :-
    peek(X, Scope, cont),
    valid_proof(Prems, Proof, Tail, [[Row, Value, contel(X)] | Scope]).

%% Checks if Value is the double-negated value of the value
%% on row X
valid_proof(Prems, Proof, [[Row, Value, negnegint(X)] | Tail], Scope) :-
    peek(X, Scope, Copy), neg(neg(Copy)) = Value,
    valid_proof(Prems, Proof, Tail, [[Row, Value, negnegint(X)] | Scope]).

%% Checks if the value on row X is the double-negated value 
%% of Value.
valid_proof(Prems, Proof, [[Row, Value, negnegel(X)] | Tail], Scope) :-
    peek(X, Scope, neg(neg(Value))), 
    valid_proof(Prems, Proof, Tail, [[Row, Value, negnegel(X)] | Scope]).

%% Checks if non-negated-Value is on the left-hand-side of the implication
%% on row X. It also checks if the value on row Y is both a negated 
%% value and it's non-negated-value is on the right-hand-side of the
%% implication on row X.
valid_proof(Prems, Proof, [[Row, neg(Value), mt(X,Y)] | Tail], Scope) :-
    peek(X, Scope, imp(Value,B)),
    peek(Y, Scope, neg(B)),
    valid_proof(Prems, Proof, Tail, [[Row, neg(Value), mt(X,Y)] | Scope]).

%% Checks if neg(Value) has been assumed on the top of a box but
%% ended up with a contradiction.
valid_proof(Prems, Proof, [[Row, Value, pbc(X, Y)] | Tail], Scope) :-
    box_in_scope([X, neg(Value), _], Scope, Box),
    get_first(Box, [X, neg(Value), _]),
    get_last(Box, [Y, cont, _]),
    valid_proof(Prems, Proof, Tail, [[Row, Value, pbc(X,Y)] | Scope]). 

%% Checks if the value is for example p or not(p).
valid_proof(Prems, Proof, [[Row, or(A, B), lem] | Tail], Scope) :-
    A = neg(B) ; B = neg(A),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), lem] | Scope]).
