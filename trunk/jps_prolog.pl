% Figure 18.11  A program that induces if-then rules.

% Learning of simple if-then rules

:-  op( 300, xfx, <==).

% learn( Class): collect learning examples into a list, construct and
% output a description for Class, and assert the corresponding rule about Class

learn( Class)  :-
   bagof( example( ClassX, Obj), example( ClassX, Obj), Examples),        % Collect examples
   learn( Examples, Class, Description),                                  % Induce rule   
   nl, write( Class), write('  <== '), nl,                                % Output rule   
   writelist( Description),
   assert( Class  <==  Description).                                      % Assert rule

% learn( Examples, Class, Description):
%    Description covers exactly the examples of class Class in list Examples

learn( Examples, Class, [])  :-
   not(member( example( Class, _ ), Examples)).               % No example to cover 

learn( Examples, Class, [Conj | Conjs])  :-
   learn_conj( Examples, Class, Conj),
   remove( Examples, Conj, RestExamples),                    % Remove examples that match Conj   
   learn( RestExamples, Class, Conjs).                       % Cover remaining examples 

% learn_conj( Examples, Class, Conj):
%    Conj is a list of attribute values satisfied by some examples of class Class and
%    no other class

learn_conj( Examples, Class, [])  :-
   not((member( example( ClassX, _ ), Examples),             % There is no example
   ClassX \== Class)), !.                                    % of different class 

learn_conj( Examples, Class, [Cond | Conds])  :-
   choose_cond( Examples, Class, Cond),                      % Choose attribute value   
   filter( Examples, [ Cond], Examples1),
   learn_conj( Examples1, Class, Conds).

choose_cond( Examples, Class, AttVal)  :-
   findall( AV/Score, score( Examples, Class, AV, Score), AVs),
   best( AVs, AttVal).                                       % Best score attribute value 

best( [ AttVal/_], AttVal).

best( [ AV0/S0, AV1/S1 | AVSlist], AttVal)  :-
   S1  >  S0, !,                                             % AV1 better than AV0   
   best( [AV1/S1 | AVSlist], AttVal)
   ;
   best( [AV0/S0 | AVSlist], AttVal).

% filter( Examples, Condition, Examples1):
%    Examples1 contains elements of Examples that satisfy Condition

filter( Examples, Cond, Examples1)  :-
   findall( example( Class, Obj),
        ( member( example( Class, Obj), Examples), satisfy( Obj, Cond)),
        Examples1).

% remove( Examples, Conj, Examples1):
%    removing from Examples those examples that are covered by Conj gives Examples1

remove( [], _, []).

remove( [example( Class, Obj) | Es], Conj, Es1)  :-
   satisfy( Obj, Conj), !,                                     % First example matches Conj   
   remove( Es, Conj, Es1).                                     % Remove it 

remove( [E | Es], Conj, [E | Es1])  :-                         % Retain first example   
   remove( Es, Conj, Es1).

satisfy( Object, Conj)  :-
   not((member( Att = Val, Conj),
         member( Att = ValX, Object),
         ValX \== Val)).

score( Examples, Class, AttVal, Score)  :-
   candidate( Examples, Class, AttVal),          % A suitable attribute value   
   filter( Examples, [ AttVal], Examples1),      % Examples1 satisfy condition Att = Val     
   length( Examples1, N1),                       % Length of list   
   count_pos( Examples1, Class, NPos1),          % Number of positive examples   
   NPos1 > 0,                                    % At least one positive example matches AttVal
   Score is 2 * NPos1 - N1.

candidate( Examples, Class, Att = Val)  :-
   attribute( Att, Values),                      % An attribute   
   member( Val, Values),                         % A value   
   suitable( Att = Val, Examples, Class).

suitable( AttVal, Examples, Class)  :-            
    % At least one negative example must not match AttVal
   member( example( ClassX, ObjX), Examples),
   ClassX \== Class,                                           % Negative example   
   not(satisfy( ObjX, [ AttVal])), !.                          % that does not match 

% count_pos( Examples, Class, N):
%    N is the number of positive examples of Class

count_pos( [], _, 0).

count_pos( [example( ClassX,_ ) | Examples], Class, N)  :-
   count_pos( Examples, Class, N1),
   ( ClassX = Class, !, N is N1 + 1; N = N1).

writelist( []).

writelist( [X | L])  :-
   tab( 2), write( X), nl,
   writelist( L).
   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

covers(Rule, Example) :-
    match_conseqent(Rule, Example, Bindings),
    match_antecedent(Rule, Bindings).
    
match_antecedent([], _).

match_antecedent([First | RestAntecedents], Bindings) :-
    match_expr(First, Bindings, NewBindings),
    conc(Bindings, NewBindings, Bindings1),
    match_antecedent(RestAntecedents, Bindings1).
    
match_expr(PredExpr, Bindings, NewBindings) :-
    op(Fact),
    functor(Fact, F1, N1),
    functor(PredExpr, F1, N1),
    Fact =.. [_ | ArgList1],
    PredExpr =.. [_ | ArgList2],
    match_arg_lists(ArgList1, ArgList2, Bindings, [], NewBindings).
    
match_arg_lists([], [], _, NewBindings, NewBindings).
    
match_arg_lists([First1 | Rest1], [First2 | Rest2], Bindings, AccIn, NewBindings) :-
    match_args(First1, First2, Bindings, AccIn, AccOut),
    match_arg_lists(Rest1, Rest2, Bindings, AccOut, NewBindings).
    
match_args(Arg1, Arg2, Bindings, AccIn, AccIn). % TODO: to jest niemal na pewno źle

match_args(Arg1, Arg2, Bindings, [First | AccIn], [First | AccOut]). % TODO: to jest niemal na pewno źle

match_conseqent(PredExpr, Example, NewBindings) :- % TODO: może być źle bo liczba argumentów się nie zgadza z tym co na kartce
    functor(Example, F1, N1),
    functor(PredExpr, F1, N1),
    Example =.. [_ | ArgList1],
    PredExpr =.. [_ | ArgList2],
    match_arg_lists(ArgList1, ArgList2, [], [], NewBindings).

%===============================dodane 22.05 ============================================
%------------fakty operacyjne----------
op(man(pawel)).
op(man(michal)).
op(man(gienek)).
op(man(daniel)).
op(man(nowy)).

op(woman(anna)).
op(woman(iwona)).
op(woman(asia)).
op(woman(ania)).
op(woman(zosia)).

op(parent(pawel,daniel)).
op(parent(anna,daniel)).
op(parent(pawel,iwona)).
op(parent(anna,iwona)).
op(parent(iwona,asia)).
op(parent(gienek,asia)).
op(parent(iwona,michal)).
op(parent(daniel,zosia)).
op(parent(ania,zosia)).

%----------------przykłady trenujące--------------

pos(father(pawel,daniel)).
pos(father(pawel,iwona)).
pos(father(gienek,asia)).
pos(father(gienek,michal)).
pos(father(daniel,zosia)).
pos(father(gienek,nowy)).

pos(grandfa(pawel,zosia)).
pos(grandfa(pawel,asia)).
pos(grandfa(pawel,michal)).
pos(grandfa(pawel,nowy)).

pos(ancestor(pawel,iwona)).
pos(ancestor(pawel,zosia)).
pos(ancestor(anna,daniel)).
pos(ancestor(anna,zosia)).
pos(ancestor(anna,asia)).
pos(ancestor(iwona,asia)).
pos(ancestor(gienek,michal)).


predicate(man,1).
predicate(woman,1).
predicate(parent,2).

%-----------------------------------------------procedury----------------------

covers(rule(Conseq,Ants), Example) :-
    match_conseqent(Conseq, Example, Bindings),
    match_antecedent(Ants, Bindings).
    
match_conseqent(PredExpr, Example, NewBindings) :-
	Example=..[_|[ExtractedExample|EmptyRes]],
    functor(ExtractedExample, F1, N1),
    functor(PredExpr, F1, N1),
    ExtractedExample =.. [_ |ArgList1],
    PredExpr =.. [_ | ArgList2],
    match_arg_lists(ArgList1, ArgList2, [], [], NewBindings).

match_antecedent([], _).

match_antecedent([First | RestAntecedents], Bindings) :-
    match_expr(First, Bindings, NewBindings),
    append(Bindings, NewBindings, Bindings1),
    match_antecedent(RestAntecedents, Bindings1).
    
match_expr(PredExpr, Bindings, NewBindings) :-
    op(Fact),
    functor(Fact, F1, N1),
    functor(PredExpr, F1, N1),
    Fact =.. [_ | ArgList1],
    PredExpr =.. [_ | ArgList2],
    match_arg_lists(ArgList1, ArgList2, Bindings, [], NewBindings).
    
match_arg_lists([], [], _, NewBindings, NewBindings).
    
match_arg_lists([First1 | Rest1], [First2 | Rest2], Bindings, AccIn, NewBindings) :-
    match_args(First1, First2, Bindings, AccIn, AccOut),
    match_arg_lists(Rest1, Rest2, Bindings, AccOut, NewBindings).


%zmienna związana (we wcześniejszym poprzedniku)   
match_args(Arg1, Arg2, Bindings,AccIn,AccIn):-
	member(Arg2/Val,Bindings),
	Arg1=Val.

%zmienna związana (w tym poprzedniku)
match_args(Arg1, Arg2, Bindings,AccIn,AccIn):-
	member(Arg2/Val,AccIn),
	Arg1=Val.

%zmienna nie zwiazana (dodaj związanie)
match_args(Arg1, Arg2, Bindings, AccIn, [New|AccIn]):-
	not(member(Arg2/_,Bindings)),
	not(member(Arg2/_,AccIn)),
	New=Arg2/Arg1.

%-----lista wszystkich przykładów negatywnych predykatu Pred------
negEx(Pred,[],[]).

negEx(Pred,[First|Rest],[NewNeg|NegList]):-
	functor(Pred,Name,N),
	New=..[Name|First],
	NewNeg=..[neg|[New]],
	negEx(Pred,Rest,NegList).
	


%-----ResList - lista wszystkich kombinacji argumentów predykatu Pred, które nie występują w przykładach pozytywnych-----
genNegs(Pred,ResList,Ns):-
	functor(Pred,Name,N),
	collectAllArgs(ArgsList,Nargs),
	genComb(ArgsList,N,CombList),
	findall( OneArgList, (pos(A),functor(Pred,Name,N),functor(A,Name,N), A=..[Name|OneArgList]), PosArgList),
	negs(CombList,PosArgList,ResList),
	length(ResList,Ns).


negs(AllList,PosList,ResList):-
	findall(A, ( (member(A,AllList)),not(member(A,PosList))  ) , ResList).


%----lista wszystkich kombinacji N - elementowych list złożonych z obiektów z InList
genComb(InList,N,Res):-
	bagof(ArgList,genArgs(InList,N,ArgList),Res).

genArgs(InList,0,[]).

genArgs(InList,N,[A|Rest]):-
	member(A,InList),
	N>0,
	N1 is N - 1,
	genArgs(InList,N1,Rest).


%-------lista wszystkich obiektów
collectAllArgs(E,N):-
	findall(List,(op(A),A=..[_|List]),Examples),
	oblicz(Examples,[],Pom),
	sort(Pom,E),
	length(E,N).

oblicz([],Wyn,Wyn).
oblicz([First|Rest],Czastk,Wyn):-
	append(First,Czastk,Pom),
	oblicz(Rest,Pom,Wyn).

%------startowa------------------
learn(Pred,H,Examples):-
	bagof( pos(A), (pos(A),functor(Pred,Name,C),functor(A,Name,C)), PosExamples),
	genNegs(Pred,ResList,N1),
	negEx(Pred,ResList,NegExamples),
	append(PosExamples,NegExamples,Examples),
	length(Examples,H).
	

filter(Examples,Rule,RestExamples):-
	findall(A, (member(A,Examples),covers(Rule,A)),RestExamples).


score(Examples,rule(Conseq,Ant),Ant,Score):-
	filter(Examples,rule(Conseq,Ant),Rest),
	length(Rest,CoveredCount),
	countPositives(Rest,CoveredPositives),
	CoveredPositives>0,
	Score is 2*CoveredPositives - CoveredCount.


countPositives([],0).
countPositives([First|Rest],N):-
	countPositives(Rest,N1),
	(functor(First,pos,_),!, N is N1+1; N=N1).


%---------------------------------------CANDIDATE-----------------------------
%range(Low, Low, High).
%range(Out,Low,High) :- NewLow is Low+1, NewLow =< High, range(Out, NewLow, High).

%-----zwraca w 1 arg kolejny argument, Flag(yes,no) oznacza czy użyto istniejącej już zmiennej
%-----argument istniejacy--------
insert_arg(rule_var(X),yes,Lzm,Lzm):-
	varC(H),
	between(1,H,X).

%----nowy argument-------
insert_arg(rule_var(Lzm2),no,Lzm,Lzm2):-
	Lzm2 is Lzm+1.

insert_last_arg(rule_var(X),no,Lzm,Lzm):-
	varC(H),
	between(1,H,X).

insert_last_arg(rule_var(X),yes,Lzm,Lzm):-
	between(1,Lzm,X).

insert_last_arg(rule_var(Lzm2),yes,Lzm,Lzm2):-
	Lzm2 is Lzm+1.

check_flag(yes,no,yes).
check_flag(yes,yes,yes).
check_flag(no,yes,yes).
check_flag(no,no,no).	

build_arg_list(1,[Arg],Flag,Lzm):-
	insert_last_arg(Arg,Flag,Lzm,Lzm2).
	
build_arg_list(N,[Arg|Rest],Flag,Lzm):-
	N>1,
	insert_arg(Arg,Flag1,Lzm,Lzm2),
	check_flag(Flag,Flag1,NewFlag),
	N1 is N-1,
	build_arg_list(N1,Rest,NewFlag,Lzm2).
	

candidate(PredExpr):-
	predicate(Name,N),
	varC(X),
	build_arg_list(N,ArgList,no,X),
	PredExpr=..[Name|ArgList].


%---------testy procedur--------------------------
%	covers(  rule(  grandfa(rule_var(1),rule_var(2)),  [man(rule_var(1)),woman(rule_var(2))] )   ,pos(grandfa(pawel,michal))  ).

%	filter( [pos(grandfa(pawel,michal)),pos(grandfa(pawel,asia))] ,rule(grandfa(rule_var(1),rule_var(2)),  [man(rule_var(1)),woman(rule_var(2))]),RestEx).

%	score([neg(grandfa(pawel,michal)),neg(grandfa(pawel,asia)),pos(grandfa(pawel,zosia))], rule(grandfa(rule_var(1),rule_var(2)), [man(rule_var(1))]), Ant ,Score).

%	countPositives( [pos(grandfa(pawel,michal)),pos(grandfa(pawel,asia)),neg(grandfa(anna,asia))] , C).
	
	