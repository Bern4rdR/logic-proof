/* read input file and run with valid_proof with input data */
verify(InputFileName) :-
    /* reads the file */
    see(InputFileName),
    /* reads the data */
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof, Proof).

verify(Prems, Goal, Proof) :- valid_proof(Prems, Goal, Proof, Proof).

/* get_row retrivies the desired row number given a expression */
    /* base case: head of list is desired row number, then expression and rule = the desired row */
get_row(RowNr, [[RowNr, Expression, Rule] | _], Expression, Rule).

    /* recursivly call, head of list is row, gets the following row */
get_row(RowNr, [[_, _ , _] | Proof], Expression, Rule) :-
    get_row(RowNr, Proof, Expression, Rule).

    /* recursiv call for boxes, head of list is box, gets the following row (within the box) */
get_row(RowNr, [[Row | Box] | _], Expression, Rule) :-
    get_row(RowNr, [Row | Box], Expression, Rule).

    /* recursiv call for boxes, head of list is box and we ignore it to get all rows within box */
get_row(RowNr, [[[_, _, _] | _] | Proof], Expression, Rule) :-
    get_row(RowNr, Proof, Expression, Rule).


/* checks for correct formatting and usage of different rules */

    /* check for correct implemenation of the COPY rule 
    checks that the expression is the same as row X */
check_rule(_, [RowNr, Expression, copy(X)], Proof) :-
    X < RowNr,
    get_row(X, Proof, Expression, Rule),
    not(Rule = box(_)).

    /* checks for correct implementation of AND-introduction 
    format: expression at row X && expression at row Y*/
check_rule(_, [RowNr, and(Expression1, Expression2), andint(X, Y)], Proof) :-
    X < RowNr, Y < RowNr,
    get_row(X, Proof, Expression1, Rule1),
    not(Rule1 = box(_)),
    get_row(Y, Proof, Expression2, Rule2),
    not(Rule2 = box(_)).

    /* checks for correct implementation of AND-elimnation
    left AND-elimination, expression should be same as row Y */
check_rule(_, [RowNr, Expression, andel1(X)], Proof) :-
    X < RowNr,
    get_row(X, Proof, and(Expression, _), Rule),
    not(Rule = box(_)).
    /* right AND-elimination, expression should be same as row X */
check_rule(_, [RowNr, Expression, andel2(X)], Proof) :-
    X < RowNr,
    get_row(X, Proof, and(_, Expression), Rule),
    not(Rule = box(_)).

    /* checks for correct implementation of double negation elimination
    removes the double negation */
check_rule(_, [RowNr, Expression, negnegel(X)], Proof) :-
    X < RowNr,
    get_row(X, Proof, neg(neg(Expression)), Rule),
    not(Rule = box(_)).

    /* checks for correct implementation of implication elimination 
    format: expression1 --> expression2 */
check_rule(_, [RowNr, Expression2, impel(X, Y)], Proof) :-
    X < RowNr, Y < RowNr,
    get_row(X, Proof, Expression1, Rule1),
    not(Rule1 = box(_)),
    get_row(Y, Proof, imp(Expression1, Expression2), Rule2),
    not(Rule2 = box(_)).

    /* checks for correct implementation of negation elimination 
    row X should contain row Y with negation */
check_rule(_, [RowNr, cont, negel(X, Y)], Proof) :-
    X < RowNr, Y < RowNr,
    get_row(X, Proof, Expression, Rule1),
    not(Rule1 = box(_)),
    get_row(Y, Proof, neg(Expression), Rule2),
    not(Rule2 = box(_)).

    /* checks for correct implementation of negation introduction 
    row X has expression which row Y has a negation: neg(expression) */
check_rule(_, [RowNr, neg(Expression), negint(X, Y)], Proof) :-
    X < RowNr, Y < RowNr, X =< Y,
    get_row(X, Proof, Expression, box(X)),
    get_row(Y, Proof, cont, box(X)).

    /* checks for correct implementation of OR-introduction 
    left side OR-introduction */
check_rule(_, [RowNr, or(Expression, _), orint1(X)], Proof) :-
    X < RowNr,
    get_row(X, Proof, Expression, Rule),
    not(Rule = box(_)).
    /* right side OR introduction */
check_rule(_, [RowNr, or(_, Expression), orint2(X)], Proof) :-
    X < RowNr,
    get_row(X, Proof, Expression, Rule),
    not(Rule = box(_)).

    /* checks for correct implementation of OR elimination 
    row Y and V both lead to expression at row U and W */
check_rule(_, [RowNr, Expression, orel(X, Y, U, V, W)], Proof) :-
    X < RowNr, Y < RowNr, U < RowNr, V < RowNr, W < RowNr, Y =< U, V =< W,
    get_row(X, Proof, or(Expression1, Expression2), Rule),
    not(Rule = box(_)),
    get_row(Y, Proof, Expression1, box(Y)),
    get_row(U, Proof, Expression, box(Y)),
    get_row(V, Proof, Expression2, box(V)),
    get_row(W, Proof, Expression, box(V)).

    /* checks for correct implementation of implication introduction 
    expression1 --> expression2 */
check_rule(_, [RowNr, imp(Expression1, Expression2), impint(X, Y)], Proof) :-
    X < RowNr, Y < RowNr, X =< Y,
    get_row(X, Proof, Expression1, box(X)),
    get_row(Y, Proof, Expression2, box(X)).

    /* checks for correct implementation of falsum elimination 
    falsum can prove whatever */
check_rule(_, [RowNr, _, contel(X)], Proof) :-
    X < RowNr,
    get_row(X, Proof, cont, Rule),
    not(Rule = box(_)).

    /* checks for correct implementation of double negation introduction 
    given expression then neg(neg(expression)) is true */
check_rule(_, [RowNr, neg(neg(Expression)), negnegint(X)], Proof) :-
    X < RowNr,
    get_row(X, Proof, Expression, Rule),
    not(Rule = box(_)).

    /* checks for correct implementation of modus tollens 
    neg(expression2) and expression1 --> expression 2, thereby neg(expression1) */
check_rule(_, [RowNr, neg(Expression1), mt(X, Y)], Proof) :-
    X < RowNr, Y < RowNr,
    get_row(X, Proof, imp(Expression1, Expression2), Rule1),
    not(Rule1 = box(_)),
    get_row(Y, Proof, neg(Expression2), Rule2),
    not(Rule2 = box(_)).

    /* checks for correct implementation of proof by contradiction 
    row X is neg(expression) and row Y contradics, therefore making expression be true */
check_rule(_, [RowNr, Expression, pbc(X, Y)], Proof) :-
    X < RowNr, Y < RowNr, X =< Y,
    get_row(X, Proof, neg(Expression), box(X)),
    get_row(Y, Proof, cont, box(X)).

    /* LEM: expression or not expresion is always a ok statement */
check_rule(_, [_, or(Expression, neg(Expression)), lem], _).

    /* assumptions outside of box-oppenings are always false */
check_rule(_, [_, _, assumption], _) :- fail.

    /* checks for correct implementation of premise */
check_rule(Prems, [_, Expression, premise], _) :-
    member(Expression, Prems).

/* checks for a valid proof*/


    /* base case: end of proof, validates rule and checks if expression = goal */
valid_proof(Prems, Goal, [[RowNr, Expression, Rule]], Proof) :-
    last(Proof, [RowNr, Expression, Rule]),
    !,
    check_rule(Prems, [RowNr, Expression, Rule], Proof),
    Expression = Goal.

    /* end of proof, validaties rule */
valid_proof(Prems, _, [[RowNr, Expression, Rule]], Proof) :-
    !,
    check_rule(Prems, [RowNr, Expression, Rule], Proof).

    /* box opens, 1st row must be assumption, 
    recursivly goes through box then "removes box" then checks the rest of the proof */
valid_proof(Prems, Goal, [[[RowNr, _, assumption] | Box] | FollowingProof], Proof) :-
    valid_proof(Prems, Goal, Box, Proof),
    remove_box(RowNr, Proof, NewProof),
    valid_proof(Prems, Goal, FollowingProof, NewProof).

    /* box opens with one row (assumption) and doesnt needs to be validated 
    recursivly goes through the rest of the proof after having "removed the box" */
valid_proof(Prems, Goal, [[[RowNr, _, assumption]] | FollowingProof], Proof) :-
    remove_box(RowNr, Proof, NewProof),
    valid_proof(Prems, Goal, FollowingProof, NewProof).

    /* checks if the row is correct and then goes to the next row */
valid_proof(Prems, Goal, [Row | FollowingProof], Proof) :-
    !,
    check_rule(Prems, Row, Proof),
    valid_proof(Prems, Goal, FollowingProof, Proof).



/* remove_box(RowNr, [proof with box], [proof without box]). */

    /* rowNr is first row in box, 
    proof without box = [rowNr 1 in box with box(rowNr), and rowNr 2 box(rowNr)]
    makes a criterium: rowNr2 is the last row in "proof with box" */
remove_box(RowNr, [[RowNr, Expression, assumption] | Box], [[RowNr, Expression, box(RowNr)], [RowNr2, Expression2, box(RowNr)]]) :-
    last(Box, [RowNr2, Expression2, _]).

    /* proof with box only contains one row thereby proof without boxes = [box(rowNr)] */
remove_box(RowNr, [[RowNr, Expression, assumption]], [[RowNr, Expression, box(RowNr)]]).

    /* inner box found, head at "proof with box" is a box and 
    "proof without box" is also a box, calls its self recursivly */
remove_box(RowNr, [[Row | Box] | Proof], [[NewRow | NewBox] | Proof]) :-
    remove_box(RowNr, [Row | Box], [NewRow | NewBox]).

    /* failsave for when proof with box is a row or box, 
    calls recursivly with the following rows 
    can also failsave if it skipps since it will fail and then backtrack */
remove_box(RowNr, [Row | Proof], [Row | NewProof]) :-
    remove_box(RowNr, Proof, NewProof).


/* Our strategy is check or go through box recursivly 
and then "remove" them and continue the rest of the proof*/