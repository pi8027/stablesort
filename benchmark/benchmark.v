From Coq Require Import NArith.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect.
From stablesort Require Import stablesort.

Elpi Command sort_benchmark.
Elpi Accumulate lp:{{

kind triple type -> type -> type -> type.
type triple A -> B -> C -> triple A B C.

% [eucldiv N D M R] N = D * M + R
pred eucldiv o:int, i:int, o:int, i:int.
eucldiv N D M R :- var N, var M, !, declare_constraint (eucldiv N D M R) [N, M].
eucldiv N D M R :- var N, N is D * M + R.
eucldiv N D M R :- var M, M is N div D, R is N mod D.

pred positive-constant o:int, o:term.
positive-constant 1 {{ lib:num.pos.xH }}.
positive-constant N {{ lib:num.pos.xO lp:T }} :-
  eucldiv N 2 M 0, positive-constant M T.
positive-constant N {{ lib:num.pos.xI lp:T }} :-
  eucldiv N 2 M 1, positive-constant M T.

pred n-constant o:int, o:term.
n-constant N _ :- not (var N), N < 0, !, fail.
n-constant 0 {{ lib:num.N.N0 }} :- !.
n-constant N {{ lib:num.N.Npos lp:T }} :- !, positive-constant N T.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% [random-N-list N Bound NS] unifies [NS] with a list of size [N] consists of
% random values of type [BinNums.N] between [0] and [Bound - 1].
pred random-N-list i:int, i:int, o:term.
random-N-list N _ _ :- N < 0, !, fail.
random-N-list 0 _ {{ @nil N }} :- !.
random-N-list N Bound {{ @cons N lp:H lp:T }} :- std.do! [
  n-constant {random.int Bound} H,
  random-N-list {calc (N - 1)} Bound T
].

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

pred time-median-rec
  i:int, i:prop, i:list float, i:list float, o:float, o:float.
time-median-rec 0 _ TS WS TOut WOut :- !, median TS TOut, median WS WOut.
time-median-rec N P TS WS TOut WOut :- std.do! [
  0 < N,
  % invoke GC explicitly before each measurement
  gc.compact,
  % change the verbosity to observe automatic GC invocation
  gc.get _ _ _ Verbose _ _ _ _,
  gc.set _ _ _ 31 _ _ _ _,
  % check for the amount of memory allocated
  gc.quick-stat Minor1 Promoted1 Major1 _ _ _ _ _ _ _,
  % measurement
  std.time P Time,
  % check for the amount of memory allocated, again
  gc.quick-stat Minor2 Promoted2 Major2 _ _ _ _ _ _ _,
  % restore the verbosity
  gc.set _ _ _ Verbose _ _ _ _,
  Words is ((Minor2 + Major2 - Promoted2) - (Minor1 + Major1 - Promoted1)),
  time-median-rec {calc (N - 1)} P [Time|TS] [Words|WS] TOut WOut
].

pred time-median i:int, i:prop, o:float, o:float.
time-median N P Time Words :- !, time-median-rec N P [] [] Time Words.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred benchmark-case
  i:string, i:(term -> term -> term -> prop),
  i:list (pair string term), i:int, o:list string, o:list string.
benchmark-case RedStr Red Config Size TS MS :- std.do! [
  coq.env.begin-section "Sec",
  random-N-list Size Size Input,
  if (RedStr = "native_compute")
     (Cname is "input" ^ {std.any->string {new_int} },
      @global! => coq.env.add-const Cname Input {{ list N }} @transparent! C,
      Red (global (const C)) _ _)
     (@local! => coq.env.add-const "input" Input {{ list N }} @transparent! C),
  std.map Config
    (c\ r\ sigma Name Func Comp CompTy Time Words Mem TStr MStr\ std.do! [
      c = pr Name Func,
      Comp = {{ lp:Func lp:{{ global (const C) }} }},
      std.assert-ok! (coq.typecheck Comp CompTy) "bad term",
      time-median 3 (Red Comp CompTy _) Time Words,
      std.any->string Time TStr,
      Mem is Words / (128.0 * 1024.0), % memory consumption in MBs
      std.any->string Mem MStr,
      r is triple Name TStr MStr
    ]) RS,
  std.any->string Size SizeStr,
  Str is RedStr ^ ", size: " ^ SizeStr ^ "; " ^
         {std.string.concat "; "
            {std.map RS (r\ s\ sigma Name TStr MStr\
               r = triple Name TStr MStr,
               s is Name ^ ": " ^ TStr ^ "s, " ^ MStr ^ "MB")} },
  coq.say Str,
  std.map RS (r\ s\ sigma Name TStr MStr\
    r = triple Name TStr MStr,
    s is "(" ^ SizeStr ^ ", " ^ TStr ^ ")"
  ) TS,
  std.map RS (r\ s\ sigma Name TStr MStr\
    r = triple Name TStr MStr,
    s is "(" ^ SizeStr ^ ", " ^ MStr ^ ")"
  ) MS,
  coq.env.end-section
].

pred benchmark
  i:string, i:(term -> term -> term -> prop), i:list (pair string term), i:term,
  o:list (list string), o:list (list string).
benchmark RedStr Red Config Size TSS MSS :-
  benchmark_aux RedStr Red Config {coq.reduction.lazy.whd_all Size} TSS MSS.

pred benchmark_aux
  i:string, i:(term -> term -> term -> prop), i:list (pair string term), i:term,
  o:list (list string), o:list (list string).
benchmark_aux _ _ Config {{ @nil _ }} SS SS :- !,
  std.map Config (_\ r\ r = []) SS.
benchmark_aux RedStr Red Config {{ @cons _ lp:SizeH lp:Size }} TSS' MSS' :-
  std.do! [
    n-constant SizeH' {coq.reduction.cbv.norm SizeH},
    benchmark-case RedStr Red Config SizeH' TS MS,
    benchmark RedStr Red Config Size TSS MSS,
    std.map2 TS TSS (t\ ts\ ts'\ ts' = [t|ts]) TSS',
    std.map2 MS MSS (m\ ms\ ms'\ ms' = [m|ms]) MSS'
  ].
benchmark_aux _ _ _ _ _ _ :-
  coq.error "benchmark_aux: the head symbol of Size is not a constructor".

pred get-reduction-machine i:string, o:(term -> term -> term -> prop).
get-reduction-machine "lazy" Red :- !,
  Red = t\ _\ tred\ coq.reduction.lazy.whd_all t tred.
get-reduction-machine "compute"  Red :- !,
  Red = t\ _\ tred\ coq.reduction.cbv.norm t tred.
get-reduction-machine "vm_compute" coq.reduction.vm.norm :- !.
get-reduction-machine "native_compute" coq.reduction.native.norm :- !,
  coq.reduction.native.available?.

pred parse-config i:list argument, o: list (pair string term).
parse-config [] [] :- !.
parse-config [str Name, trm Func | ConfList] [pr Name Func | Conf] :- !,
  parse-config ConfList Conf.
parse-config _ _ :- coq.error "ill-formed arguments".

main [str FileName, str RedStr, trm Size | ConfList] :- std.do! [
  std.assert-ok! (coq.typecheck Size {{ seq N }}) "bad term",
  parse-config ConfList Config,
  % enlarge the minor heap to 4GB
  gc.get Minor _ _ _ _ _ _ _,
  gc.set {calc (512 * 1024 * 1024)} _ _ _ _ _ _ _,
  % benchmark
  benchmark RedStr {get-reduction-machine RedStr} Config Size TSS MSS,
  % restore the initial size of the minor heap
  gc.set Minor _ _ _ _ _ _ _,
  % pgfplot
  open_out {calc (FileName ^ ".time.out")} TStream,
  output TStream "% time consumption\n",
  std.forall TSS (ts\ sigma Str\
    output TStream "\\addplot coordinates {",
    std.string.concat " " ts Str,
    output TStream Str,
    output TStream "};\n"),
  output TStream "\\legend{",
  output TStream
    {std.string.concat ", " {std.map Config (c\ n\ sigma T\ c = pr n T)} },
  output TStream "}\n",
  close_out TStream,
  open_out {calc (FileName ^ ".mem.out")} MStream,
  output MStream "% memory consumption\n",
  std.forall MSS (ms\ sigma Str\
    output MStream "\\addplot coordinates {",
    std.string.concat " " ms Str,
    output MStream Str,
    output MStream "};\n"),
  output MStream "\\legend{",
  output MStream
    {std.string.concat ", " {std.map Config (c\ n\ sigma T\ c = pr n T)} },
  output MStream "}\n",
  close_out MStream
].
main _ :- !, coq.error "ill-formed arguments".

}}.
Elpi Typecheck.

Definition N_iota (n m : N) : seq N :=
  N.iter m (fun f n => n :: f (N.succ n)) (fun => [::]) n.

Definition lazy_bench
  (sort : forall T : Type, rel T -> seq T -> seq T) (xs : seq N) :=
  sorted N.leb (take 10 (sort _ N.leb xs)).

Definition eager_bench
  (sort : forall T : Type, rel T -> seq T -> seq T) (xs : seq N) :=
  sorted N.leb (sort _ N.leb xs).
