verify(InputFileName) :- 
	see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
	length(Proof, Len), nth1(Len, Proof, [_, Goal, _]),
	solve(Prems, Goal, Proof, 0, [], []), !.

solve(_, _, [], 1, _, _).%:- write('Box closing. ').

solve(Prems,Goal,[], 0, _, _) :-
	member([_, Goal, _], Prems),!.% write('Goal achieved! '), !.

solve(Prems, Goal, [Row | Tail], IsBox, PreviousBox1, PreviousBox2) :- 
	((Row = [RowNumber,  Variable, Rule] , (PrevBox1 = PreviousBox1, PrevBox2 = PreviousBox2,assert(Prems, Goal, Row, PrevBox1, PrevBox2), append(Prems, [Row], NewPrems)));
	(Row = [[RowNumber, Variable, assumption] | _] ,  
		( PrevBox2 = PreviousBox1, PrevBox1 = Row,  solve(Prems, Goal, Row, 1, PrevBox1, PrevBox2),   NewPrems = Prems))) 
	-> solve(NewPrems, Goal, Tail, IsBox, PrevBox1, PrevBox2).

assert(Prems, Goal, [Row, P, assumption], PreviousBox, _)  :-PreviousBox \= [].

assert(Prems, Goal, [Row, P, premise], _, _) :-
	member(P, Prems).%, write('Premise! ').

assert(Prems, Goal, [Row, and(X,Y), andint(B,C)], _, _) :- 
	member([B, X, _],  Prems), member([C, Y, _], Prems).%, write('And-Int! ').

assert(Prems, Goal, [Row, X, impel(B, C)], _, _) :-
	member([B, Y, _], Prems), member([C, imp(Y, X), _], Prems).%, write('Imp-El! ').

assert(Prems, Goal, [Row, X, andel1(B)], _, _) :-
	member([B,and(X,_),_], Prems).%, write('And-El(1)! ').

assert(Prems, Goal, [Row, X, andel2(B)], _, _) :-
	member([B,and(_,X),_], Prems).%, write('And-El(2)! ').

assert(Prems, Goal, [Row, X, copy(B)], _, _) :-
	member([B, X, _], Prems).%, write('Copy! ').

assert(Prems, Goal, [Row, or(X, Y), orint1(B)], _, _) :-
	member([B, X, _], Prems).%, write('Or-Int(1)! ').

assert(Prems, Goal, [Row, or(X, Y), orint2(B)], _, _) :-
	member([B, Y, _], Prems).%, write('Or-Int(2)! ').

assert(Prems, Goal, [Row, neg(X), negint(A, B)], PreviousBox, _) :-
	length(PreviousBox, Len), nth1(1, PreviousBox, [A, X, assumption]), nth1(Len, PreviousBox, [B, cont, _]).%, write('Neg-Int! ').

assert(Prems, Goal, [Row, neg(neg(X)), negnegint(B)], _, _) :-
	member([B, X, _], Prems).%, write('Negnegint! ').

assert(Prems, Goal, [Row, cont, negel(A, B)], _, _) :-
	member([A, X, _], Prems), member([B, neg(X), _], Prems).%, write('Neg-El! ').

assert(Prems, Goal, [Row, imp(X, Y), impint(A, B)], PreviousBox, _) :-
	length(PreviousBox, Len), nth1(1, PreviousBox, [A, X, assumption]), nth1(Len, PreviousBox, [B, Y, _]).%, write('Imp-Int! ').

assert(Prems, Goal, [Row, X, negnegel(B)], _, _) :-
	member([B, neg(neg(X)), _], Prems).%, write('NegNeg-El! ').

assert(Prems, Goal, [Row, neg(X), mt(B,C)], _, _) :-
	member([B, imp(X,Y), _], Prems), member([C, neg(Y) , _], Prems).%, write('MT! ').

assert(Prems, Goal, [Row, X, contel(B)], _, _) :-
	member([B,  cont, _], Prems).%, write('Cont-El! ').

assert(Prems, Goal, [Row, or(neg(X),  X), lem], _, _).% :- write('LEM! ').
assert(Prems, Goal, [Row, or(X, neg(X)), lem], _, _).%:- write('LEM! ').

assert(Prems, Goal, [Row, X, pbc(A, B)], PreviousBox, _) :-
	length(PreviousBox, Len), nth1(1, PreviousBox, [A, neg(X), assumption]), nth1(Len, PreviousBox, [B, cont, _]).%, write('PBC! ').

assert(Prems, Goal, [Row, P, orel(X,Y, U, V, W)], PreviousBox1, PreviousBox2) :- 
	length(PreviousBox1, Len1), length(PreviousBox2, Len2),
	member([X, or(A,  B), _], Prems), 
	nth1(1, PreviousBox2, [Y,A,_]), nth1(Len2, PreviousBox2, [U, P, _]),
	nth1(1, PreviousBox1, [V, B, _]), nth1(Len1, PreviousBox1, [W, P, _]).
	%write('Or-El! ').
