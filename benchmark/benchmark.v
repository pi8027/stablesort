From Coq Require Import NArith.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect.
From stablesort Require Import stablesort.

Elpi Command sort_benchmark.
Elpi Accumulate lp:{{

% [positive-constant N T] states that [T] is a Coq term of type [positive]
% corresponding to [N].
pred positive-constant o:int, o:term.
positive-constant N _ :- N < 1, !, fail.
positive-constant 1 {{ lib:num.pos.xH }} :- !.
positive-constant N {{ lib:num.pos.xO lp:T }} :-
  0 is N mod 2, !, positive-constant {calc (N div 2)} T.
positive-constant N {{ lib:num.pos.xI lp:T }} :-
  1 is N mod 2, !, positive-constant {calc (N div 2)} T.

% [n-constant N T] states that [T] is a Coq term of type [BinNums.N]
% corresponding to [N].
pred n-constant o:int, o:term.
n-constant N _ :- N < 0, !, fail.
n-constant 0 {{ lib:num.N.N0 }} :- !.
n-constant N {{ lib:num.N.Npos lp:T }} :- !, positive-constant {calc N} T.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred random-N-inner-list i:int, i:int, o:term.
random-N-inner-list 0 _ {{ @nil N }} :- !.
random-N-inner-list N Bound {{ @cons N lp:H lp:T }} :- std.do! [
  n-constant {random.int Bound} H,
  random-N-inner-list {calc (N - 1)} Bound T
].

pred random-N-list-rec i:int, i:int, o:term.
random-N-list-rec N _ _ :- N < 0, !, fail.
random-N-list-rec N Bound Out :- N =< 10000, !, random-N-inner-list N Bound Out.
random-N-list-rec N Bound {{ @cat N lp:Out1 lp:Out2 }} :- !,
  random-N-inner-list 10000 Bound Out1, !,
  random-N-list-rec {calc (N - 10000)} Bound Out2.

% [random-N-list N Bound NS] unifies [NS] with a list of size [N] consists of
% random values of type [BinNums.N] between [0] and [Bound - 1].
pred random-N-list i:int, i:int, o:term.
random-N-list N Bound Out :- !, random-N-list-rec N Bound Out.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred insert i:A, i:list A, o:list A.
insert X [] [X] :- !.
insert X [Y|YS] [X, Y|YS] :- X =< Y, !.
insert X [Y|YS] [Y|YS']   :- Y < X,  !, insert X YS YS'.

pred sort i:list A, o:list A.
sort [] [] :- !.
sort [X|XS] RS :- !, sort XS XS', !, insert X XS' RS.

pred median i:list float, o:float.
median TS Out :-
  1 is {std.length TS} mod 2, !,
  std.nth {calc ({std.length TS} div 2)} {sort TS} Out.

pred time-median-rec i:int, i:prop, i:list float, o:float.
time-median-rec 0 _ TS Out :- !, median TS Out.
time-median-rec N P TS Out :- !,
  0 < N, !,
  std.time P Time, !,
  time-median-rec {calc (N - 1)} P [Time|TS] Out.

pred time-median i:int, i:prop, o:float.
time-median N P Out :- !, time-median-rec N P [] Out.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred benchmark-case i:string, i:(term -> term -> term -> prop),
                    i:list (pair string term), i:int.
benchmark-case RedStr Red Config Size :- std.do! [
  coq.env.begin-section "Sec",
  random-N-list Size Size Input,
  ID is "input_" ^ { std.any->string {new_int} },
  @local! => coq.env.add-const ID Input {{ list N }} @transparent! C,
  std.map Config (c\ r\ sigma Name Func Computation Time TimeStr\ std.do! [
    c = pr Name Func,
    Computation = {{ lp:Func N N.leb lp:{{ global (const C) }} }},
    std.assert-ok! (coq.typecheck Computation {{ list N }}) "bad term",
    time-median 5 (Red Computation {{ list N }} _) Time,
    std.any->string Time TimeStr,
    r is Name ^ ": " ^ TimeStr
  ]) RS,
  Str is RedStr ^ ", size: " ^ {std.any->string Size} ^ ", " ^
         {std.string.concat ", " RS},
  coq.say Str,
  coq.env.end-section
].

pred benchmark i:string, i:(term -> term -> term -> prop),
               i:list (pair string term), i:int, i:int, i:int.
benchmark _ _ _ 0 _ _ :- !.
benchmark RedStr Red Config Repeat Incr CurrentSize :- std.do! [
  0 < Repeat,
  NextSize is CurrentSize + Incr,
  benchmark-case RedStr Red Config NextSize,
  benchmark RedStr Red Config {calc (Repeat - 1)} Incr NextSize
].

pred get-reduction-machine i:string, o:(term -> term -> term -> prop).
get-reduction-machine "lazy" Red :- !,
  Red = t\ _\ tred\ coq.reduction.lazy.whd_all t tred.
get-reduction-machine "cbv"  Red :- !,
  Red = t\ _\ tred\ coq.reduction.cbv.whd_all t tred.
get-reduction-machine "vm_compute" coq.reduction.vm.whd_all :- !.

pred parse-config i:list argument, o: list (pair string term).
parse-config [] [] :- !.
parse-config [str Name, trm Func | ConfList] [pr Name Func | Conf] :- !,
  parse-config ConfList Conf.
parse-config _ _ :- coq.error "ill-formed arguments".

main [str RedStr, int Repeat, int Incr | ConfList] :- std.do! [
  0 < Repeat, 0 < Incr,
  benchmark RedStr {get-reduction-machine RedStr} {parse-config ConfList}
            Repeat Incr 0
].
main _ :- coq.error "ill-formed arguments".

}}.
Elpi Typecheck.

Elpi sort_benchmark
  "lazy"       100 100
  "sort"       (sort)
  "CBN.sort"   (CBN.sort)
  "CBV.sort"   (CBV.sort).

Elpi sort_benchmark
  "cbv"        100 100
  "sort"       (sort)
  "CBN.sort"   (CBN.sort)
  "CBV.sort"   (CBV.sort).

Elpi sort_benchmark
  "vm_compute" 100 100
  "sort"       (sort)
  "CBN.sort"   (CBN.sort)
  "CBV.sort"   (CBV.sort).
