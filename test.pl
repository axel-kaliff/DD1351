
remove_duplicates([], []).
remove_duplicates([H|T], [H|E]) :- remove_duplicates(T, E), \+ (member(H, E)).
remove_duplicates([_|T], E) :- remove_duplicates(T, E).

T=f(a, Y, Z), T=(X, X, b).
