From Coq Require Import NArith.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect.
From stablesort Require Import stablesort.

Elpi Command sort_benchmark.
Elpi Accumulate lp:{{

kind triple type -> type -> type -> type.
type triple A -> B -> C -> triple A B C.

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
  @local! => coq.env.add-const "input" Input {{ list N }} @transparent! C,
  std.map Config
    (c\ r\ sigma Name Func Comp CompTy Time Words Mem TStr MStr\ std.do! [
      c = pr Name Func,
      Comp = {{ lp:Func lp:{{ global (const C) }} }},
      std.assert-ok! (coq.typecheck Comp CompTy) "bad term",
      time-median 5 (Red Comp CompTy _) Time Words,
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
  i:string, i:(term -> term -> term -> prop),
  i:list (pair string term), i:int, i:int, i:int,
  o:list (list string), o:list (list string).
benchmark _ _ Config 0 _ _ SS SS :- !,
  std.map Config (_\ r\ r = []) SS.
benchmark RedStr Red Config Repeat Incr CurrentSize TSS' MSS' :- std.do! [
  0 < Repeat,
  NextSize is CurrentSize + Incr,
  benchmark-case RedStr Red Config NextSize TS MS,
  benchmark RedStr Red Config {calc (Repeat - 1)} Incr NextSize TSS MSS,
  std.map2 TS TSS (t\ ts\ ts'\ ts' = [t|ts]) TSS',
  std.map2 MS MSS (m\ ms\ ms'\ ms' = [m|ms]) MSS'
].

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

main [str TimeFile, str MemFile, str RedStr, int Repeat, int Incr |
      ConfList] :- std.do! [
  0 < Repeat,
  0 < Incr,
  parse-config ConfList Config,
  % enlarge the minor heap to 4GB
  gc.get Minor _ _ _ _ _ _ _,
  gc.set {calc (512 * 1024 * 1024)} _ _ _ _ _ _ _,
  % benchmark
  benchmark RedStr {get-reduction-machine RedStr} Config Repeat Incr 0 TSS MSS,
  % restore the initial size of the minor heap
  gc.set Minor _ _ _ _ _ _ _,
  % pgfplot
  open_out TimeFile TStream,
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
  open_out MemFile MStream,
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

Definition CBN_sort_lazy_bench xs :=
  sorted N.leb (take 10 (CBN.sort N.leb xs)).
Definition CBNOpt_sort_lazy_bench xs :=
  sorted N.leb (take 10 (CBNOpt.sort N.leb xs)).
Definition CBV_sort_lazy_bench xs :=
  sorted N.leb (take 10 (CBV.sort N.leb xs)).
Definition CBVOpt_sort_lazy_bench xs :=
  sorted N.leb (take 10 (CBVOpt.sort N.leb xs)).
Definition CBN_sort_bench xs    := sorted N.leb (CBN.sort N.leb xs).
Definition CBNOpt_sort_bench xs := sorted N.leb (CBNOpt.sort N.leb xs).
Definition CBV_sort_bench xs    := sorted N.leb (CBV.sort N.leb xs).
Definition CBVOpt_sort_bench xs := sorted N.leb (CBVOpt.sort N.leb xs).

Elpi sort_benchmark
  "lazy1.time.out" "lazy1.mem.out" "lazy" 50 100
  "CBN.sort"     (CBN_sort_lazy_bench)
  "CBNOpt.sort"  (CBNOpt_sort_lazy_bench)
  "CBV.sort"     (CBV_sort_lazy_bench)
  "CBVOpt.sort"  (CBVOpt_sort_lazy_bench).

Elpi sort_benchmark
  "lazy2.time.out" "lazy2.mem.out" "lazy" 50 100
  "CBN.sort"     (CBN_sort_bench)
  "CBNOpt.sort"  (CBNOpt_sort_bench)
  "CBV.sort"     (CBV_sort_bench)
  "CBVOpt.sort"  (CBVOpt_sort_bench).

Elpi sort_benchmark
  "compute.time.out" "compute.mem.out" "compute" 50 100
  "CBN.sort"     (CBN_sort_bench)
  "CBNOpt.sort"  (CBNOpt_sort_bench)
  "CBV.sort"     (CBV_sort_bench)
  "CBVOpt.sort"  (CBVOpt_sort_bench).

Elpi sort_benchmark
  "vm.time.out" "vm.mem.out" "vm_compute" 50 1000
  "CBN.sort"     (CBN_sort_bench)
  "CBNOpt.sort"  (CBNOpt_sort_bench)
  "CBV.sort"     (CBV_sort_bench)
  "CBVOpt.sort"  (CBVOpt_sort_bench).

Elpi sort_benchmark
  "native.time.out" "native.mem.out" "native_compute" 50 1000
  "CBN.sort"     (CBN_sort_bench)
  "CBNOpt.sort"  (CBNOpt_sort_bench)
  "CBV.sort"     (CBV_sort_bench)
  "CBVOpt.sort"  (CBVOpt_sort_bench).
