%------------fakty operacyjne----------
op(man(pawel)).
op(man(michal)).
op(man(marcin)).
op(man(andrzej)).
op(man(grzesiek)).

op(woman(anna)).
op(woman(beata)).
op(woman(asia)).
op(woman(marta)).
op(woman(zosia)).

op(parent(pawel,andrzej)).
op(parent(anna,andrzej)).
op(parent(pawel,beata)).
op(parent(anna,beata)).
op(parent(beata,asia)).
op(parent(marcin,asia)).
op(parent(beata,michal)).
op(parent(marcin,michal)).
op(parent(andrzej,zosia)).
op(parent(marta,zosia)).
op(parent(andrzej,grzesiek)).
op(parent(marta,grzesiek)).

%----------------przykłady trenujące--------------

pos(father(pawel,andrzej)).
pos(father(pawel,beata)).
pos(father(marcin,asia)).
pos(father(marcin,michal)).
pos(father(andrzej,zosia)).
pos(father(andrzej,grzesiek)).

pos(grandfa(pawel,zosia)).
pos(grandfa(pawel,grzesiek)).
pos(grandfa(pawel,asia)).
pos(grandfa(pawel,michal)).

pos(grandma(anna,zosia)).
pos(grandma(anna,grzesiek)).
pos(grandma(anna,asia)).
pos(grandma(anna,michal)).

pos(ancestor(pawel,beata)).
pos(ancestor(pawel,andrzej)).
pos(ancestor(pawel,zosia)).
pos(ancestor(pawel,asia)).
pos(ancestor(pawel,michal)).
pos(ancestor(pawel,grzesiek)).
pos(ancestor(anna,andrzej)).
pos(ancestor(anna,beata)).
pos(ancestor(anna,zosia)).
pos(ancestor(anna,asia)).
pos(ancestor(anna,michal)).
pos(ancestor(anna,grzesiek)).
pos(ancestor(beata,asia)).
pos(ancestor(beata,michal)).
pos(ancestor(marcin,michal)).
pos(ancestor(marcin,asia)).
pos(ancestor(marta,zosia)).
pos(ancestor(marta,grzesiek)).
pos(ancestor(andrzej,zosia)).
pos(ancestor(andrzej,grzesiek)).

predicate(man,1).
predicate(woman,1).
predicate(parent,2).


%-----------------------------------------------procedury----------------------

%------startowa ------------------
%Dla zadanego predykatu zbiera przykłady pozytywne, generuje wszystkie negatywne i łączy w 1 listę - Examples,
%następnie wywołuje learn1.
learn(Conseq,H,Rules):-
	assert(actLimit(2)),
	bagof( pos(A), (pos(A),functor(Conseq,Name,C),functor(A,Name,C)), PosExamples),
	genNegs(Conseq,ResList,N1),
	negEx(Conseq,ResList,NegExamples),
	append(PosExamples,NegExamples,Examples),
	learn1(Examples,Conseq,Rules),!,
	length(Examples,H).

%sprawdza czy dotychczasowymi regułami pokryto wszystkie przykłady pozytywne, kończy działanie.
learn1(Examples,Conseq,[]):-
	not((member(pos(_),Examples))).

%Po znalezieniu kolejnej reguły usuwa przykłady, które były pokrywane przez tą regułę.
learn1(Examples,Conseq,[Rule|RestRules]):-
	actLimit(Limit),
	memberDet(pos(_),Examples),
	functor(Conseq,_,VarBound),
	learn_conj(Examples,Limit,rule(Conseq,[]),Rule,VarBound),
	remove(Examples,Rule,RestExamples),
	learn1(RestExamples,Conseq,RestRules).


%Wrapper na learn_conj1 dodany na potrzeby nowej heurystyki (do zwiększania limitu poprzedników w pojedyńczej regule)
learn_conj(Examples,Limit,PartialRule,Rule,VarBound):-
	actLimit(Limit),
	learn_conj1(Examples,0,Limit,PartialRule,Rule,VarBound).	%odciecie

learn_conj(Examples,Limit,PartialRule,Rule,VarBound):-
	Limit1 is Limit+1,
	retract(actLimit(_)),
	assert(actLimit(Limit1)),
	learn_conj(Examples,Limit1,PartialRule,Rule,VarBound).

%sprawdza czy dotychczas zbudowana reguła pokrywa jedynie przykłady pozytywne
learn_conj1(Examples,N,Limit,PartialRule,PartialRule,VarBound):-
	not(member(neg(_),Examples)),
	memberDet(pos(_),Examples).

%buduje pojedyńczą regułe z kolejnych poprzedników
learn_conj1(Examples,N,Limit,rule(Conseq,Ants),Rule,VarBound):-
	N1 is N+1,
	N1=<Limit,
	choose_ants(Examples,Conseq,FirstNAnts,VarBound),
	member(PredExpr/NewVarBound,FirstNAnts),
	not(member(PredExpr,Ants)),
	append(Ants,[PredExpr],NewAnts),
	filter(Examples,rule(Conseq,NewAnts),RestExamples),
	learn_conj1(RestExamples,N1,Limit,rule(Conseq,NewAnts),Rule,NewVarBound).

%dlugosc listy, z której learn_conj1 wybiera poprzednika reguły (-: warianty w kolejnych nawrotach :-)
scoreListLength(6).	

%buduje listę N kandydatów (zmienna zadawana - scoreListLength) na poprzednika reguły uszeregowanych wg kryteriów przydatności
choose_ants(Examples,Conseq,FirstNAnts,VarBound):-	
	findall(   Score-Ant/NewVarBound,   (  score(Examples,rule(Conseq,[Ant]),Ant,Score,VarBound,NewVarBound)  )  , AllAnts  ),
	keysort(AllAnts,AllAntsSorted),
	reverse(AllAntsSorted,AllAntsSortedRising),
	scoreListLength(N),
	takeFirstN(N,AllAntsSortedRising,FirstNAnts).

%podlista pierwszych N elementów listy wejściowej
takeFirstN(_,[],[]).
takeFirstN(1,[Score-First|RestInput],[First]).
takeFirstN(N,[Score-First|RestInput],[First|Rest]):-
	N>1,
	N1 is N-1,
	takeFirstN(N1,RestInput,Rest).

%---------------------------------------CANDIDATE-----------------------------

%ocena przydatności dla każdego kandydata na poprzednika reguły
score(Examples,rule(Conseq,[Ant]),Ant,Score,VarBound,NewVarBound):-
	candidate(Ant,VarBound,NewVarBound),
	filter(Examples,rule(Conseq,[Ant]),Rest),
	length(Rest,CoveredCount),
	countPositives(Rest,CoveredPositives),
	CoveredPositives>0,
	Score is 2*CoveredPositives - CoveredCount.

%buduje kandydata na poprzednika (niedeterministyczna - zwróci każdą kombinację argumentów wszystkich predykatów faktów operacyjnych)
candidate(PredExpr,VarBound,NewVarBound):-
	predicate(Name,N),
	build_arg_list(N,ArgList,no,VarBound,VarBound,NewVarBound),
	PredExpr=..[Name|ArgList].

%buduje N elementową listę argumentów(niedetrministyczna - każda możliwa kombinacja)
build_arg_list(1,[Arg],Flag,VarBound,Lzm,Lzm2):-
	insert_last_arg(Arg,Flag,VarBound,Lzm,Lzm2).
	
build_arg_list(N,[Arg|Rest],Flag,VarBound,Lzm,NewVarBound):-
	N>1,
	insert_arg(Arg,Flag1,VarBound,Lzm,Lzm2),
	check_flag(Flag,Flag1,NewFlag),
	N1 is N-1,
	build_arg_list(N1,Rest,NewFlag,VarBound,Lzm2,NewVarBound).

%-----zwraca w 1 arg kolejny argument, Flag(yes,no) oznacza czy użyto istniejącej już zmiennej
%-----argument istniejacy--------
insert_arg(rule_var(X),yes,VarBound,Lzm,Lzm):-
	between(1,VarBound,X).

%----powtorzenie zmiennej, która pojawiła się dopiero w tym predykacie we wcześniejszym argumencie
insert_arg(rule_var(X),no,VarBound,Lzm,Lzm):-
	H1 is VarBound+1,
	between(H1,Lzm,X).

%----nowy argument-------
insert_arg(rule_var(Lzm2),no,VarBound,Lzm,Lzm2):-
	Lzm2 is Lzm+1.

insert_last_arg(rule_var(X),no,VarBound,Lzm,Lzm):-
	between(1,VarBound,X).

insert_last_arg(rule_var(X),yes,VarBound,Lzm,Lzm):-
	between(1,Lzm,X).

insert_last_arg(rule_var(Lzm2),yes,VarBound,Lzm,Lzm2):-
	Lzm2 is Lzm+1.

check_flag(yes,no,yes).
check_flag(yes,yes,yes).
check_flag(no,yes,yes).
check_flag(no,no,no).	


%-------------COVERS--------------
%sprawdzenie czy reguła pokrywa podany przykład
covers(rule(Conseq,Ants), Example) :-
	match_conseqent(Conseq, Example, Bindings),!,
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
	match_expr(First, Bindings, NewBindings),!,
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

%generuje 1 listę (niedeterministyczna - wszystkie kombinacje)
genArgs(InList,0,[]).

genArgs(InList,N,[A|Rest]):-
	member(A,InList),
	N>0,
	N1 is N - 1,
	genArgs(InList,N1,Rest).


%-------lista wszystkich obiektów, występujących we wszystkich faktach operacyjnych (sort usuwa powtórzenia)
collectAllArgs(E,N):-
	findall(List,(op(A),A=..[_|List]),Examples),
	transformIt(Examples,[],Pom),
	sort(Pom,E),
	length(E,N).

%z postaci listy list zmienia wynik na listę jednowymiarową
transformIt([],Wyn,Wyn).
transformIt([First|Rest],Czastk,Wyn):-
	append(First,Czastk,Pom),
	transformIt(Rest,Pom,Wyn).

%przesiewa przykłady przez regułę
filter(Examples,Rule,RestExamples):-
	findall(A, (member(A,Examples),covers(Rule,A)),RestExamples).


countPositives([],0).
countPositives([First|Rest],N):-
	countPositives(Rest,N1),
	(functor(First,pos,_),!, N is N1+1; N=N1).

%deterministyczna odmiana member
memberDet(X,[X|Rest]).
memberDet(X,[Y|Rest]):-
	X/=Y,
	memberDet(X,Rest).

%-----usuwa przykłady, które pokrywa reguła
remove([],_,[]).

remove([FirstEx|RestEx],Rule,Rest):-
	covers(Rule,FirstEx),!,
	remove(RestEx,Rule,Rest).

remove([FirstEx|RestEx],Rule,[FirstEx|Rest]):-
	remove(RestEx,Rule,Rest).
	

%---------testy procedur--------------------------
%	covers(  rule(  grandfa(rule_var(1),rule_var(2)),  [man(rule_var(1)),woman(rule_var(2))] )   ,pos(grandfa(pawel,michal))  ).
%	covers(  rule(grandfa(rule_var(1),rule_var(2)), [parent(rule_var(3),rule_var(2))])   ,neg(grandfa(pawel,michal))  ).

%	filter( [pos(grandfa(pawel,michal)),pos(grandfa(pawel,asia))] ,rule(grandfa(rule_var(1),rule_var(2)),  [man(rule_var(1)),woman(rule_var(2))]),RestEx).

%	score([neg(grandfa(pawel,michal)),neg(grandfa(pawel,asia)),pos(grandfa(pawel,zosia))], rule(grandfa(rule_var(1),rule_var(2)), [man(rule_var(1))]), Ant ,Score).
%	score([neg(grandfa(pawel,michal)),neg(grandfa(pawel,asia)),pos(grandfa(pawel,zosia))], rule(grandfa(rule_var(1),rule_var(2)), [Ant]), Ant ,Score).

%	countPositives( [pos(grandfa(pawel,michal)),pos(grandfa(pawel,asia)),neg(grandfa(anna,asia))] , C).

%	remove( [neg(grandfa(pawel,michal)),neg(grandfa(pawel,asia)),pos(grandfa(pawel,zosia))], rule(grandfa(rule_var(1),rule_var(2)), [man(rule_var(1)),woman(rule_var(2))] ), R  ).	

%	choose_ants( [neg(grandfa(pawel,michal)),neg(grandfa(pawel,asia)),pos(grandfa(pawel,zosia))], grandfa(rule_var(1),rule_var(2)), Ants).

%	[pos(father(pawel, daniel)), pos(father(pawel, iwona)), pos(father(gienek, asia)), pos(father(gienek, michal)), pos(father(daniel, zosia)), neg(father(ania, ania)), neg(father(ania, anna))

%-----------testy całości:-----------------------
%	learn(father(rule_var(1),rule_var(2)),E,R).

%	learn(grandfa(rule_var(1),rule_var(2)),E,R).
%	learn(grandma(rule_var(1),rule_var(2)),E,R).

%	learn(ancestor(rule_var(1),rule_var(2)),E,R).