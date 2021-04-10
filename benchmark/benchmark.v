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

% [random-N-list N Bound NS] unifies [NS] with a list of size [N] consists of
% random values of type [BinNums.N] between [0] and [Bound - 1].
pred random-N-list i:int, i:int, o:term.
random-N-list 0 _ {{ @nil N }} :- !.
random-N-list N Bound {{ @cons N lp:H lp:T }} :- std.do! [
  n-constant {random.int Bound} H,
  random-N-list {calc (N - 1)} Bound T
].

pred benchmark-case i:(term -> term -> term -> prop),
                    i:list (pair string term), i:int.
benchmark-case Red Config Size :- std.do! [
  random-N-list Size Size Input,
  ListTy = {{ list N }},
  std.map Config (c\ r\ sigma Name Func Computation Time TimeStr\ std.do! [
    c = pr Name Func,
    Computation = {{ lp:Func N N.leb lp:Input }},
    std.assert-ok! (coq.typecheck Computation ListTy) "bad term",
    std.time (Red Computation ListTy _) Time,
    std.any->string Time TimeStr,
    r is Name ^ ": " ^ TimeStr
  ]) RS,
  Str is "[size: " ^ {std.any->string Size} ^ "] " ^
         {std.string.concat ", " RS},
  coq.say Str
].

pred benchmark i:(term -> term -> term -> prop),
               i:list (pair string term), i:int, i:int, i:int.
benchmark _ _ 0 _ _ :- !.
benchmark Red Config Repeat Incr CurrentSize :- std.do! [
  0 < Repeat,
  NextSize is CurrentSize + Incr,
  benchmark-case Red Config NextSize,
  benchmark Red Config {calc (Repeat - 1)} Incr NextSize
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

main [str Redtac, int Repeat, int Incr | ConfList] :- std.do! [
  0 < Repeat, 0 < Incr,
  benchmark {get-reduction-machine Redtac} {parse-config ConfList}
            Repeat Incr 0
].
main _ :- coq.error "ill-formed arguments".

}}.
Elpi Typecheck.

Elpi sort_benchmark
  "lazy"       10 1000
  "sort"       (sort)
  "CBN.sort"   (CBN.sort)
  "CBV.sort"   (CBV.sort).
Elpi sort_benchmark
  "cbv"        10 1000
  "sort"       (sort)
  "CBN.sort"   (CBN.sort)
  "CBV.sort"   (CBV.sort).
Elpi sort_benchmark
  "vm_compute" 10 1000
  "sort"       (sort)
  "CBN.sort"   (CBN.sort)
  "CBV.sort"   (CBV.sort).
