From Coq Require Import NArith.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  i:string, i:(term -> term -> term -> prop), i:int, i:list (pair string term),
  i:term, i:term, i:int, o:list string, o:list string.
benchmark-case RedStr Red MedianOf Config Preproc SizeC Size TS MS :- std.do! [
  coq.env.begin-section "Sec",
  coq.reduction.vm.norm
    (app [Preproc, {random-N-list Size Size}]) {{ list N }} Input,
  if (RedStr = "native_compute")
     (Cname is "input" ^ {std.any->string {new_int} },
      @global! => coq.env.add-const Cname Input {{ list N }} @transparent! C,
      Red (global (const C)) _ _)
     (@local! => coq.env.add-const "input" Input {{ list N }} @transparent! C),
  std.map Config
    (c\ r\ sigma Name Func Comp SimplComp CompTy Time Words Mem TStr MStr\
      std.do! [
        c = pr Name Func,
        Comp = {{ lp:Func lp:SizeC lp:{{ global (const C) }} }},
        std.assert-ok! (coq.typecheck Comp CompTy) "bad term",
        hd-beta-zeta-reduce Comp SimplComp,
        time-median MedianOf (Red SimplComp CompTy _) Time Words,
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
  std.map RS (r\ s\ r = triple _ s _) TS,
  std.map RS (r\ s\ r = triple _ _ s) MS,
  coq.env.end-section
].

pred benchmark
  i:string, i:(term -> term -> term -> prop), i:int, i:list (pair string term),
  i:term, i:term, o:list (list string), o:list (list string).
benchmark RedStr Red MedianOf Config Preproc Size TSS MSS :- !,
  benchmark_aux RedStr Red MedianOf Config Preproc
                {coq.reduction.lazy.whd_all Size} TSS MSS.

pred benchmark_aux
  i:string, i:(term -> term -> term -> prop), i:int, i:list (pair string term),
  i:term, i:term, o:list (list string), o:list (list string).
benchmark_aux _ _ _ _ _ {{ @nil _ }} [] [] :- !.
benchmark_aux RedStr Red MedianOf Config Preproc {{ @cons _ lp:SizeH lp:Size }}
              [[SizeHStr|TS]|TSS] [[SizeHStr|MS]|MSS] :- std.do! [
  coq.reduction.cbv.norm SizeH SizeH',
  n-constant SizeH'' SizeH',
  std.any->string SizeH'' SizeHStr,
  benchmark-case RedStr Red MedianOf Config Preproc SizeH' SizeH'' TS MS,
  benchmark RedStr Red MedianOf Config Preproc Size TSS MSS
].
benchmark_aux _ _ _ _ _ _ _ _ :-
  coq.error "benchmark_aux: the head symbol of Size is not a constructor".

pred get-reduction-machine i:string, o:(term -> term -> term -> prop).
get-reduction-machine "lazy" Red :- !,
  Red = t\ _\ tred\ coq.reduction.lazy.whd_all t tred.
get-reduction-machine "compute"  Red :- !,
  Red = t\ _\ tred\ coq.reduction.cbv.norm t tred.
get-reduction-machine "vm_compute" coq.reduction.vm.norm :- !.
get-reduction-machine "native_compute" coq.reduction.native.norm :-
  coq.reduction.native.available?, !.
get-reduction-machine M _ :-
  coq.error "Reduction machine" M "is not available".

pred parse-config i:list argument, o: list (pair string term).
parse-config [] [] :- !.
parse-config [str Name, trm Func | ConfList] [pr Name Func | Conf] :- !,
  parse-config ConfList Conf.
parse-config _ _ :- coq.error "ill-formed arguments".

main [str FileName, str RedStr, int MedianOf, trm Size, trm Preproc |
      ConfList] :- std.do! [
  std.assert-ok! (coq.typecheck Size {{ seq N }}) "bad term",
  std.assert-ok! (coq.typecheck Preproc {{ seq N -> seq N }}) "bad term",
  parse-config ConfList Config,
  % enlarge the minor heap to 16GB
  gc.get Minor _ _ _ _ _ _ _,
  gc.set {calc (2 * 1024 * 1024 * 1024)} _ _ _ _ _ _ _,
  % benchmark
  benchmark RedStr {get-reduction-machine RedStr} MedianOf Config Preproc Size
            TSS MSS,
  % restore the initial size of the minor heap
  gc.set Minor _ _ _ _ _ _ _,
  % pgfplot
  open_out {calc (FileName ^ ".time.csv")} TStream,
  output TStream "Size",
  std.forall Config (conf\ sigma Name\
    conf = pr Name _,
    output TStream ", ",
    output TStream Name),
  output TStream "\n",
  std.forall TSS (ts\ sigma T TS\
    ts = [T|TS],
    output TStream T,
    std.forall TS (t\ output TStream ", ", output TStream t),
    output TStream "\n"),
  close_out TStream,
  open_out {calc (FileName ^ ".mem.csv")} MStream,
  output MStream "Size",
  std.forall Config (conf\ sigma Name\
    conf = pr Name _,
    output MStream ", ",
    output MStream Name),
  output MStream "\n",
  std.forall MSS (ms\ sigma M MS\
    ms = [M|MS],
    output MStream M,
    std.forall MS (m\ output MStream ", ", output MStream m),
    output MStream "\n"),
  close_out MStream
].
main _ :- !, coq.error "ill-formed arguments".

}}.
Elpi Typecheck.

Definition N_iota (n m : N) : seq N :=
  N.iter m (fun f n => n :: f (N.succ n)) (fun => [::]) n.

Notation lazy_bench sort :=
  (fun n xs => sorted N.leb (take 10 (sort _ N.leb xs))).

Notation eager_bench sort :=
  (fun n xs => sorted N.leb (sort _ N.leb xs)).

Fixpoint sort_blocks (T : Type) (leT : rel T) (n : nat) (xs : seq T) :=
  if xs is x :: xs' then
    sort leT (take n xs) ++ sort_blocks leT n (drop n.-1 xs') else [::].
