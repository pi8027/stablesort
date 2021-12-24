
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

type reflect =
| ReflectT
| ReflectF

(** val ssr_have : 'a1 -> ('a1 -> 'a2) -> 'a2 **)

let ssr_have step rest =
  rest step

type alt_spec =
| AltTrue
| AltFalse

(** val altP : bool -> reflect -> alt_spec **)

let altP _ = function
| ReflectT -> AltTrue
| ReflectF -> AltFalse

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

(** val boolP : bool -> alt_spec **)

let boolP b1 =
  altP b1 (idP b1)

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op m =
    m.op

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

(** val nilP : 'a1 list -> reflect **)

let nilP = function
| [] -> ReflectT
| _::_ -> ReflectF

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x::s1' -> x::(cat s1' s2)



(** val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec merge leT s1 = match s1 with
| [] -> (fun x -> x)
| x1::s1' ->
  let rec merge_s1 s2 = match s2 with
  | [] -> s1
  | x2::s2' ->
    if leT x1 x2 then x1::(merge leT s1' s2) else x2::(merge_s1 s2')
  in merge_s1

type bool_R =
| Bool_R_true_R
| Bool_R_false_R

type ('x0, 'x, 'a_R) list_R =
| List_R_nil_R
| List_R_cons_R of 'x0 * 'x * 'a_R * 'x0 list * 'x list
   * ('x0, 'x, 'a_R) list_R

type ('x0, 'x, 't_R) pred_R = 'x0 -> 'x -> 't_R -> bool_R

type ('x0, 'x, 't_R) rel_R = 'x0 -> 'x -> 't_R -> ('x0, 'x, 't_R) pred_R

module StableSort =
 struct
  type 't trace =
  | Coq_branch_trace of bool * 't trace * 't trace
  | Coq_leaf_trace of Equality.sort * 't list

  (** val empty_trace : 'a1 rel -> 'a1 trace **)

  let empty_trace _ =
    Coq_leaf_trace ((Obj.magic false), [])

  (** val flatten_trace : 'a1 rel -> 'a1 trace -> 'a1 list **)

  let rec flatten_trace leT = function
  | Coq_branch_trace (_, l, r) ->
    cat (flatten_trace leT l) (flatten_trace leT r)
  | Coq_leaf_trace (_, s) -> s

  (** val sort_trace : 'a1 rel -> 'a1 trace -> 'a1 list **)

  let rec sort_trace leT = function
  | Coq_branch_trace (b, l, r) ->
    if b
    then merge leT (sort_trace leT l) (sort_trace leT r)
    else List.rev
           (merge (fun x y -> leT y x) (List.rev (sort_trace leT r))
             (List.rev (sort_trace leT l)))
  | Coq_leaf_trace (b, s) -> if Obj.magic b then s else List.rev s

  type 't trace_nil_spec =
  | TraceNil
  | TraceNotNil

  (** val trace_nilP : 'a1 rel -> 'a1 trace -> 'a1 trace_nil_spec **)

  let trace_nilP leT t =
    match nilP (sort_trace leT t) with
    | ReflectT ->
      (match nilP (flatten_trace leT t) with
       | ReflectT ->
         ssr_have __ (fun _ _ -> ssr_have __ (fun _ _ -> TraceNil)) __ __
       | ReflectF -> assert false (* absurd case *))
    | ReflectF ->
      (match nilP (flatten_trace leT t) with
       | ReflectT -> assert false (* absurd case *)
       | ReflectF -> TraceNotNil)

  type sort_ty_R =
    __ -> __ -> __ -> __ rel -> __ rel -> (__, __, __) rel_R -> __ list -> __
    list -> (__, __, __) list_R -> (__, __, __) list_R

  type coq_function = { apply : (__ -> __ rel -> __ list -> __ list);
                        coq_function__1 : sort_ty_R;
                        coq_function__2 : (__ -> __ rel -> __ list -> __
                                          trace sig2) }
 end

module type MergeSig =
 sig
  val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val merge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R
 end

module type RevmergeSig =
 sig
  val revmerge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val revmerge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R
 end

module Merge =
 struct
  (** val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

  let rec merge leT xs ys =
    match xs with
    | [] -> ys
    | x::xs' ->
      let rec merge' ys0 = match ys0 with
      | [] -> xs
      | y::ys' -> if leT x y then x::(merge leT xs' ys0) else y::(merge' ys')
      in merge' ys

  (** val merge_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
      list_R -> ('a1, 'a2, 'a3) list_R **)

  let rec merge_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_ xs_R ys_UU2081_ ys_UU2082_ ys_R =
    match xs_R with
    | List_R_nil_R -> ys_R
    | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, xs'_UU2081_, xs'_UU2082_,
                     xs'_R) ->
      let rec merge'_R ys_UU2081_0 ys_UU2082_0 ys_R0 = match ys_R0 with
      | List_R_nil_R -> xs_R
      | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, ys'_UU2081_, ys'_UU2082_,
                       ys'_R) ->
        (match leT_R x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R with
         | Bool_R_true_R ->
           List_R_cons_R (x_UU2081_, x_UU2082_, x_R,
             (let rec merge0 leT xs ys =
                match xs with
                | [] -> ys
                | x::xs' ->
                  let rec merge' ys0 = match ys0 with
                  | [] -> xs
                  | y::ys' ->
                    if leT x y
                    then x::(merge0 leT xs' ys0)
                    else y::(merge' ys')
                  in merge' ys
              in merge0 leT_UU2081_ xs'_UU2081_ ys_UU2081_0),
             (let rec merge0 leT xs ys =
                match xs with
                | [] -> ys
                | x::xs' ->
                  let rec merge' ys0 = match ys0 with
                  | [] -> xs
                  | y::ys' ->
                    if leT x y
                    then x::(merge0 leT xs' ys0)
                    else y::(merge' ys')
                  in merge' ys
              in merge0 leT_UU2082_ xs'_UU2082_ ys_UU2082_0),
             (merge_R leT_UU2081_ leT_UU2082_ leT_R xs'_UU2081_ xs'_UU2082_
               xs'_R ys_UU2081_0 ys_UU2082_0 ys_R0))
         | Bool_R_false_R ->
           List_R_cons_R (y_UU2081_, y_UU2082_, y_R,
             (let rec merge' ys = match ys with
              | [] -> xs_UU2081_
              | y::ys' ->
                if leT_UU2081_ x_UU2081_ y
                then x_UU2081_::(let rec merge0 leT xs ys0 =
                                   match xs with
                                   | [] -> ys0
                                   | x::xs' ->
                                     let rec merge'0 ys1 = match ys1 with
                                     | [] -> xs
                                     | y0::ys'0 ->
                                       if leT x y0
                                       then x::(merge0 leT xs' ys1)
                                       else y0::(merge'0 ys'0)
                                     in merge'0 ys0
                                 in merge0 leT_UU2081_ xs'_UU2081_ ys)
                else y::(merge' ys')
              in merge' ys'_UU2081_),
             (let rec merge' ys = match ys with
              | [] -> xs_UU2082_
              | y::ys' ->
                if leT_UU2082_ x_UU2082_ y
                then x_UU2082_::(let rec merge0 leT xs ys0 =
                                   match xs with
                                   | [] -> ys0
                                   | x::xs' ->
                                     let rec merge'0 ys1 = match ys1 with
                                     | [] -> xs
                                     | y0::ys'0 ->
                                       if leT x y0
                                       then x::(merge0 leT xs' ys1)
                                       else y0::(merge'0 ys'0)
                                     in merge'0 ys0
                                 in merge0 leT_UU2082_ xs'_UU2082_ ys)
                else y::(merge' ys')
              in merge' ys'_UU2082_),
             (merge'_R ys'_UU2081_ ys'_UU2082_ ys'_R)))
      in merge'_R ys_UU2081_ ys_UU2082_ ys_R
 end

module MergeAcc =
 struct
  (** val merge_rec : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

  let rec merge_rec leT xs ys =
    match xs with
    | [] -> ys
    | x::xs' ->
      (match ys with
       | [] -> xs
       | y::ys' ->
         if leT x y
         then x::(merge_rec leT xs' ys)
         else y::(merge_rec leT xs ys'))

  (** val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

  let merge =
    merge_rec

  (** val merge_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
      list_R -> ('a1, 'a2, 'a3) list_R **)

  let rec merge_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_ xs_R ys_UU2081_ ys_UU2082_ ys_R =
    match xs_R with
    | List_R_nil_R -> ys_R
    | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, xs'_UU2081_, xs'_UU2082_,
                     xs'_R) ->
      (match ys_R with
       | List_R_nil_R -> xs_R
       | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, ys'_UU2081_, ys'_UU2082_,
                        ys'_R) ->
         (match leT_R x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R with
          | Bool_R_true_R ->
            List_R_cons_R (x_UU2081_, x_UU2082_, x_R,
              (let rec merge_rec0 leT xs ys =
                 match xs with
                 | [] -> ys
                 | x::xs' ->
                   (match ys with
                    | [] -> xs
                    | y::ys' ->
                      if leT x y
                      then x::(merge_rec0 leT xs' ys)
                      else y::(merge_rec0 leT xs ys'))
               in merge_rec0 leT_UU2081_ xs'_UU2081_ ys_UU2081_),
              (let rec merge_rec0 leT xs ys =
                 match xs with
                 | [] -> ys
                 | x::xs' ->
                   (match ys with
                    | [] -> xs
                    | y::ys' ->
                      if leT x y
                      then x::(merge_rec0 leT xs' ys)
                      else y::(merge_rec0 leT xs ys'))
               in merge_rec0 leT_UU2082_ xs'_UU2082_ ys_UU2082_),
              (merge_R leT_UU2081_ leT_UU2082_ leT_R xs'_UU2081_ xs'_UU2082_
                xs'_R ys_UU2081_ ys_UU2082_ ys_R))
          | Bool_R_false_R ->
            List_R_cons_R (y_UU2081_, y_UU2082_, y_R,
              (let rec merge_rec0 leT xs ys =
                 match xs with
                 | [] -> ys
                 | x::xs' ->
                   (match ys with
                    | [] -> xs
                    | y::ys' ->
                      if leT x y
                      then x::(merge_rec0 leT xs' ys)
                      else y::(merge_rec0 leT xs ys'))
               in merge_rec0 leT_UU2081_ xs_UU2081_ ys'_UU2081_),
              (let rec merge_rec0 leT xs ys =
                 match xs with
                 | [] -> ys
                 | x::xs' ->
                   (match ys with
                    | [] -> xs
                    | y::ys' ->
                      if leT x y
                      then x::(merge_rec0 leT xs' ys)
                      else y::(merge_rec0 leT xs ys'))
               in merge_rec0 leT_UU2082_ xs_UU2082_ ys'_UU2082_),
              (merge_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_
                xs_R ys'_UU2081_ ys'_UU2082_ ys'_R))))
 end

module Revmerge =
 struct
  (** val merge_rec :
      'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list **)

  let rec merge_rec leT xs ys accu =
    match xs with
    | [] -> List.rev_append ys accu
    | x::xs' ->
      let rec merge_rec' ys0 accu0 =
        match ys0 with
        | [] -> List.rev_append xs accu0
        | y::ys' ->
          if leT x y
          then merge_rec leT xs' ys0 (x::accu0)
          else merge_rec' ys' (y::accu0)
      in merge_rec' ys accu

  (** val revmerge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

  let revmerge leT xs ys =
    merge_rec leT xs ys []

  (** val revmerge_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
      list_R -> ('a1, 'a2, 'a3) list_R **)

  let revmerge_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_ xs_R ys_UU2081_ ys_UU2082_ ys_R =
    let rec merge_rec_R leT_UU2081_0 leT_UU2082_0 leT_R0 xs_UU2081_0 xs_UU2082_0 xs_R0 ys_UU2081_0 ys_UU2082_0 ys_R0 accu_UU2081_ accu_UU2082_ accu_R =
      match xs_R0 with
      | List_R_nil_R ->
        let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
          match s1_R with
          | List_R_nil_R -> s2_R
          | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s1'_UU2081_,
                           s1'_UU2082_, s1'_R) ->
            catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R (x_UU2081_::s2_UU2081_)
              (x_UU2082_::s2_UU2082_) (List_R_cons_R (x_UU2081_, x_UU2082_,
              x_R, s2_UU2081_, s2_UU2082_, s2_R))
        in catrev_R ys_UU2081_0 ys_UU2082_0 ys_R0 accu_UU2081_ accu_UU2082_
             accu_R
      | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, xs'_UU2081_, xs'_UU2082_,
                       xs'_R) ->
        let rec merge_rec'_R ys_UU2081_1 ys_UU2082_1 ys_R1 accu_UU2081_0 accu_UU2082_0 accu_R0 =
          match ys_R1 with
          | List_R_nil_R ->
            let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
              match s1_R with
              | List_R_nil_R -> s2_R
              | List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, s1'_UU2081_,
                               s1'_UU2082_, s1'_R) ->
                catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                  (x_UU2081_0::s2_UU2081_) (x_UU2082_0::s2_UU2082_)
                  (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, s2_UU2081_,
                  s2_UU2082_, s2_R))
            in catrev_R xs_UU2081_0 xs_UU2082_0 xs_R0 accu_UU2081_0
                 accu_UU2082_0 accu_R0
          | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, ys'_UU2081_,
                           ys'_UU2082_, ys'_R) ->
            (match leT_R0 x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R with
             | Bool_R_true_R ->
               merge_rec_R leT_UU2081_0 leT_UU2082_0 leT_R0 xs'_UU2081_
                 xs'_UU2082_ xs'_R ys_UU2081_1 ys_UU2082_1 ys_R1
                 (x_UU2081_::accu_UU2081_0) (x_UU2082_::accu_UU2082_0)
                 (List_R_cons_R (x_UU2081_, x_UU2082_, x_R, accu_UU2081_0,
                 accu_UU2082_0, accu_R0))
             | Bool_R_false_R ->
               merge_rec'_R ys'_UU2081_ ys'_UU2082_ ys'_R
                 (y_UU2081_::accu_UU2081_0) (y_UU2082_::accu_UU2082_0)
                 (List_R_cons_R (y_UU2081_, y_UU2082_, y_R, accu_UU2081_0,
                 accu_UU2082_0, accu_R0)))
        in merge_rec'_R ys_UU2081_0 ys_UU2082_0 ys_R0 accu_UU2081_
             accu_UU2082_ accu_R
    in merge_rec_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_ xs_R
         ys_UU2081_ ys_UU2082_ ys_R [] [] List_R_nil_R
 end

module RevmergeAcc =
 struct
  (** val merge_rec :
      'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list **)

  let rec merge_rec leT xs ys accu =
    match xs with
    | [] -> List.rev_append ys accu
    | x::xs' ->
      (match ys with
       | [] -> List.rev_append xs accu
       | y::ys' ->
         if leT x y
         then merge_rec leT xs' ys (x::accu)
         else merge_rec leT xs ys' (y::accu))

  (** val revmerge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

  let revmerge leT xs ys =
    merge_rec leT xs ys []

  (** val revmerge_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
      list_R -> ('a1, 'a2, 'a3) list_R **)

  let revmerge_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_ xs_R ys_UU2081_ ys_UU2082_ ys_R =
    let rec merge_rec_R leT_UU2081_0 leT_UU2082_0 leT_R0 xs_UU2081_0 xs_UU2082_0 xs_R0 ys_UU2081_0 ys_UU2082_0 ys_R0 accu_UU2081_ accu_UU2082_ accu_R =
      match xs_R0 with
      | List_R_nil_R ->
        let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
          match s1_R with
          | List_R_nil_R -> s2_R
          | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s1'_UU2081_,
                           s1'_UU2082_, s1'_R) ->
            catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R (x_UU2081_::s2_UU2081_)
              (x_UU2082_::s2_UU2082_) (List_R_cons_R (x_UU2081_, x_UU2082_,
              x_R, s2_UU2081_, s2_UU2082_, s2_R))
        in catrev_R ys_UU2081_0 ys_UU2082_0 ys_R0 accu_UU2081_ accu_UU2082_
             accu_R
      | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, xs'_UU2081_, xs'_UU2082_,
                       xs'_R) ->
        (match ys_R0 with
         | List_R_nil_R ->
           let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
             match s1_R with
             | List_R_nil_R -> s2_R
             | List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, s1'_UU2081_,
                              s1'_UU2082_, s1'_R) ->
               catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                 (x_UU2081_0::s2_UU2081_) (x_UU2082_0::s2_UU2082_)
                 (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, s2_UU2081_,
                 s2_UU2082_, s2_R))
           in catrev_R xs_UU2081_0 xs_UU2082_0 xs_R0 accu_UU2081_
                accu_UU2082_ accu_R
         | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, ys'_UU2081_,
                          ys'_UU2082_, ys'_R) ->
           (match leT_R0 x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R with
            | Bool_R_true_R ->
              merge_rec_R leT_UU2081_0 leT_UU2082_0 leT_R0 xs'_UU2081_
                xs'_UU2082_ xs'_R ys_UU2081_0 ys_UU2082_0 ys_R0
                (x_UU2081_::accu_UU2081_) (x_UU2082_::accu_UU2082_)
                (List_R_cons_R (x_UU2081_, x_UU2082_, x_R, accu_UU2081_,
                accu_UU2082_, accu_R))
            | Bool_R_false_R ->
              merge_rec_R leT_UU2081_0 leT_UU2082_0 leT_R0 xs_UU2081_0
                xs_UU2082_0 xs_R0 ys'_UU2081_ ys'_UU2082_ ys'_R
                (y_UU2081_::accu_UU2081_) (y_UU2082_::accu_UU2082_)
                (List_R_cons_R (y_UU2081_, y_UU2082_, y_R, accu_UU2081_,
                accu_UU2082_, accu_R))))
    in merge_rec_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_ xs_R
         ys_UU2081_ ys_UU2082_ ys_R [] [] List_R_nil_R
 end

module CBN_ =
 functor (M:MergeSig) ->
 struct
  (** val merge_sort_push :
      'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list **)

  let rec merge_sort_push leT s stack = match stack with
  | [] -> s::stack
  | s'::stack' ->
    (match s' with
     | [] -> s::stack'
     | _::_ -> []::(merge_sort_push leT (M.merge leT s' s) stack'))

  (** val merge_sort_pop :
      'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list **)

  let rec merge_sort_pop leT s1 = function
  | [] -> s1
  | s2::stack' -> merge_sort_pop leT (M.merge leT s2 s1) stack'

  (** val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

  let rec sort1rec leT stack = function
  | [] -> merge_sort_pop leT [] stack
  | x::s0 -> sort1rec leT (merge_sort_push leT (x::[]) stack) s0

  (** val sort1 : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sort1 leT =
    sort1rec leT []

  (** val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

  let rec sort2rec leT stack s = match s with
  | [] -> merge_sort_pop leT s stack
  | x1::l ->
    (match l with
     | [] -> merge_sort_pop leT s stack
     | x2::s' ->
       sort2rec leT
         (merge_sort_push leT
           (if leT x1 x2 then x1::(x2::[]) else x2::(x1::[])) stack) s')

  (** val sort2 : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sort2 leT =
    sort2rec leT []

  (** val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

  let rec sort3rec leT stack s = match s with
  | [] -> merge_sort_pop leT s stack
  | x1::l ->
    (match l with
     | [] -> merge_sort_pop leT s stack
     | x2::l0 ->
       (match l0 with
        | [] ->
          merge_sort_pop leT (if leT x1 x2 then s else x2::(x1::[])) stack
        | x3::s' ->
          sort3rec leT
            (merge_sort_push leT
              (if leT x1 x2
               then if leT x2 x3
                    then x1::(x2::(x3::[]))
                    else if leT x1 x3
                         then x1::(x3::(x2::[]))
                         else x3::(x1::(x2::[]))
               else if leT x1 x3
                    then x2::(x1::(x3::[]))
                    else if leT x2 x3
                         then x2::(x3::(x1::[]))
                         else x3::(x2::(x1::[]))) stack) s'))

  (** val sort3 : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sort3 leT =
    sort3rec leT []

  (** val sortNrec :
      'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list **)

  let sortNrec leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT (x::[]) stack
    | y::s0 ->
      if leT x y then incr0 stack y s0 (x::[]) else decr0 stack y s0 (x::[])
    and incr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT (List.rev_append accu (x::[])) stack
      | y::s0 ->
        if leT x y
        then incr0 stack y s0 (x::accu)
        else sortNrec0
               (merge_sort_push leT (List.rev_append accu (x::[])) stack) y s0
    and decr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT (x::accu) stack
      | y::s0 ->
        if leT x y
        then sortNrec0 (merge_sort_push leT (x::accu) stack) y s0
        else decr0 stack y s0 (x::accu)
    in sortNrec0

  (** val incr :
      'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list **)

  let incr leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT (x::[]) stack
    | y::s0 ->
      if leT x y then incr0 stack y s0 (x::[]) else decr0 stack y s0 (x::[])
    and incr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT (List.rev_append accu (x::[])) stack
      | y::s0 ->
        if leT x y
        then incr0 stack y s0 (x::accu)
        else sortNrec0
               (merge_sort_push leT (List.rev_append accu (x::[])) stack) y s0
    and decr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT (x::accu) stack
      | y::s0 ->
        if leT x y
        then sortNrec0 (merge_sort_push leT (x::accu) stack) y s0
        else decr0 stack y s0 (x::accu)
    in incr0

  (** val decr :
      'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list **)

  let decr leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT (x::[]) stack
    | y::s0 ->
      if leT x y then incr0 stack y s0 (x::[]) else decr0 stack y s0 (x::[])
    and incr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT (List.rev_append accu (x::[])) stack
      | y::s0 ->
        if leT x y
        then incr0 stack y s0 (x::accu)
        else sortNrec0
               (merge_sort_push leT (List.rev_append accu (x::[])) stack) y s0
    and decr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT (x::accu) stack
      | y::s0 ->
        if leT x y
        then sortNrec0 (merge_sort_push leT (x::accu) stack) y s0
        else decr0 stack y s0 (x::accu)
    in decr0

  (** val sortN : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sortN leT = function
  | [] -> []
  | x::s0 -> sortNrec leT [] x s0

  (** val merge_sort_pushP :
      'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
      StableSort.trace list sig2 **)

  let rec merge_sort_pushP leT t = function
  | [] -> t::[]
  | y::l ->
    (match StableSort.trace_nilP leT y with
     | StableSort.TraceNil -> t::l
     | StableSort.TraceNotNil ->
       ssr_have
         (merge_sort_pushP leT (StableSort.Coq_branch_trace (true, y, t)) l)
         (fun __top_assumption_ ->
         (StableSort.empty_trace leT)::__top_assumption_))

  (** val merge_sort_popP :
      'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
      StableSort.trace sig2 **)

  let rec merge_sort_popP leT t = function
  | [] -> t
  | y::l ->
    ssr_have
      (merge_sort_popP leT (StableSort.Coq_branch_trace (true, y, t)) l)
      (fun __top_assumption_ -> __top_assumption_)

  (** val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2 **)

  let sort1P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec f l stack =
          match l with
          | [] -> merge_sort_popP leT (StableSort.empty_trace leT) stack
          | y::l0 ->
            f l0
              (merge_sort_pushP leT (StableSort.Coq_leaf_trace
                ((Obj.magic true), (y::[]))) stack)
        in f s []))

  (** val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2 **)

  let sort2P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec iHs stack = function
        | [] ->
          merge_sort_popP leT (StableSort.Coq_leaf_trace ((Obj.magic true),
            [])) stack
        | a::l ->
          (match l with
           | [] ->
             merge_sort_popP leT (StableSort.Coq_leaf_trace
               ((Obj.magic true), (a::[]))) stack
           | a0::l0 ->
             iHs
               (merge_sort_pushP leT (StableSort.Coq_leaf_trace
                 ((Obj.magic leT a a0), (a::(a0::[])))) stack) l0)
        in iHs [] s))

  (** val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2 **)

  let sort3P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        ssr_have __ (fun _ ->
          let rec iHs stack = function
          | [] ->
            merge_sort_popP leT (StableSort.Coq_leaf_trace ((Obj.magic true),
              [])) stack
          | a::l ->
            (match l with
             | [] ->
               merge_sort_popP leT (StableSort.Coq_leaf_trace
                 ((Obj.magic true), (a::[]))) stack
             | a0::l0 ->
               (match l0 with
                | [] ->
                  merge_sort_popP leT (StableSort.Coq_leaf_trace
                    ((Obj.magic leT a a0), (a::(a0::[])))) stack
                | a1::l1 ->
                  ssr_have __ (fun _ _ ->
                    iHs
                      (merge_sort_pushP leT (StableSort.Coq_branch_trace
                        (false, (StableSort.Coq_leaf_trace
                        ((Obj.magic leT a a0), (a::(a0::[])))),
                        (StableSort.Coq_leaf_trace ((Obj.magic true),
                        (a1::[]))))) stack) l1) __))
          in iHs [] s)))

  (** val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2 **)

  let sortNP leT = function
  | [] -> StableSort.empty_trace leT
  | a::l ->
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec iHs stack x = function
        | [] ->
          merge_sort_popP leT (StableSort.Coq_leaf_trace ((Obj.magic true),
            (x::[]))) stack
        | a0::l0 ->
          ssr_have __
            (ssr_have __ (fun _ _ ->
              let rec f l1 ord x0 acc =
                match l1 with
                | [] ->
                  merge_sort_popP leT (StableSort.Coq_leaf_trace
                    ((Obj.magic ord), (List.rev (x0::acc)))) stack
                | y::l2 ->
                  if ord
                  then (match boolP (leT x0 y) with
                        | AltTrue ->
                          ssr_have __ (fun _ -> f l2 true y (x0::acc))
                        | AltFalse ->
                          iHs
                            (merge_sort_pushP leT (StableSort.Coq_leaf_trace
                              ((Obj.magic true), (List.rev (x0::acc)))) stack)
                            y l2)
                  else (match boolP (leT x0 y) with
                        | AltTrue ->
                          iHs
                            (merge_sort_pushP leT (StableSort.Coq_leaf_trace
                              ((Obj.magic false), (List.rev (x0::acc))))
                              stack) y l2
                        | AltFalse ->
                          ssr_have __ (fun _ -> f l2 false y (x0::acc)))
              in f l0 (leT x a0) a0 (x::[])))
        in iHs [] a l))

  (** val merge_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
      list_R -> ('a1, 'a2, 'a3) list_R **)

  let merge_R =
    M.merge_R

  (** val merge_sort_push_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
      'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1 list, 'a2 list, ('a1,
      'a2, 'a3) list_R) list_R **)

  let rec merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R s_UU2081_ s_UU2082_ s_R stack_UU2081_ stack_UU2082_ stack_R = match stack_R with
  | List_R_nil_R ->
    List_R_cons_R (s_UU2081_, s_UU2082_, s_R, stack_UU2081_, stack_UU2082_,
      stack_R)
  | List_R_cons_R (s'_UU2081_, s'_UU2082_, s'_R, stack'_UU2081_,
                   stack'_UU2082_, stack'_R) ->
    (match s'_R with
     | List_R_nil_R ->
       List_R_cons_R (s_UU2081_, s_UU2082_, s_R, stack'_UU2081_,
         stack'_UU2082_, stack'_R)
     | List_R_cons_R (_, _, _, _, _, _) ->
       List_R_cons_R ([], [], List_R_nil_R,
         (let rec merge_sort_push0 s stack = match stack with
          | [] -> s::stack
          | s'::stack' ->
            (match s' with
             | [] -> s::stack'
             | _::_ ->
               []::(merge_sort_push0 (M.merge leT_UU2081_ s' s) stack'))
          in merge_sort_push0 (M.merge leT_UU2081_ s'_UU2081_ s_UU2081_)
               stack'_UU2081_),
         (let rec merge_sort_push0 s stack = match stack with
          | [] -> s::stack
          | s'::stack' ->
            (match s' with
             | [] -> s::stack'
             | _::_ ->
               []::(merge_sort_push0 (M.merge leT_UU2082_ s' s) stack'))
          in merge_sort_push0 (M.merge leT_UU2082_ s'_UU2082_ s_UU2082_)
               stack'_UU2082_),
         (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
           (M.merge leT_UU2081_ s'_UU2081_ s_UU2081_)
           (M.merge leT_UU2082_ s'_UU2082_ s_UU2082_)
           (merge_R leT_UU2081_ leT_UU2082_ leT_R s'_UU2081_ s'_UU2082_ s'_R
             s_UU2081_ s_UU2082_ s_R) stack'_UU2081_ stack'_UU2082_ stack'_R)))

  (** val merge_sort_pop_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
      'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1, 'a2, 'a3) list_R **)

  let rec merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R s1_UU2081_ s1_UU2082_ s1_R _ _ = function
  | List_R_nil_R -> s1_R
  | List_R_cons_R (s2_UU2081_, s2_UU2082_, s2_R, stack'_UU2081_,
                   stack'_UU2082_, stack'_R) ->
    merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R
      (M.merge leT_UU2081_ s2_UU2081_ s1_UU2081_)
      (M.merge leT_UU2082_ s2_UU2082_ s1_UU2082_)
      (merge_R leT_UU2081_ leT_UU2082_ leT_R s2_UU2081_ s2_UU2082_ s2_R
        s1_UU2081_ s1_UU2082_ s1_R) stack'_UU2081_ stack'_UU2082_ stack'_R

  (** val sort1_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R **)

  let sort1_R leT_UU2081_ leT_UU2082_ leT_R =
    let rec sort1rec_R stack_UU2081_ stack_UU2082_ stack_R _ _ = function
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R [] [] List_R_nil_R
        stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s_UU2081_, s_UU2082_, s_R0) ->
      sort1rec_R (merge_sort_push leT_UU2081_ (x_UU2081_::[]) stack_UU2081_)
        (merge_sort_push leT_UU2082_ (x_UU2082_::[]) stack_UU2082_)
        (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R (x_UU2081_::[])
          (x_UU2082_::[]) (List_R_cons_R (x_UU2081_, x_UU2082_, x_R, [], [],
          List_R_nil_R)) stack_UU2081_ stack_UU2082_ stack_R) s_UU2081_
        s_UU2082_ s_R0
    in sort1rec_R [] [] List_R_nil_R

  (** val sort2_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R **)

  let sort2_R leT_UU2081_ leT_UU2082_ leT_R =
    let rec sort2rec_R stack_UU2081_ stack_UU2082_ stack_R s_UU2081_ s_UU2082_ s_R = match s_R with
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R s_UU2081_ s_UU2082_ s_R
        stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R, _, _, l_R) ->
      (match l_R with
       | List_R_nil_R ->
         merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R s_UU2081_ s_UU2082_
           s_R stack_UU2081_ stack_UU2082_ stack_R
       | List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R, s'_UU2081_, s'_UU2082_,
                        s'_R) ->
         let s1_UU2081_ =
           if leT_UU2081_ x1_UU2081_ x2_UU2081_
           then x1_UU2081_::(x2_UU2081_::[])
           else x2_UU2081_::(x1_UU2081_::[])
         in
         let s1_UU2082_ =
           if leT_UU2082_ x1_UU2082_ x2_UU2082_
           then x1_UU2082_::(x2_UU2082_::[])
           else x2_UU2082_::(x1_UU2082_::[])
         in
         sort2rec_R (merge_sort_push leT_UU2081_ s1_UU2081_ stack_UU2081_)
           (merge_sort_push leT_UU2082_ s1_UU2082_ stack_UU2082_)
           (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R s1_UU2081_
             s1_UU2082_
             (match leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_ x2_UU2082_
                      x2_R with
              | Bool_R_true_R ->
                List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R,
                  (x2_UU2081_::[]), (x2_UU2082_::[]), (List_R_cons_R
                  (x2_UU2081_, x2_UU2082_, x2_R, [], [], List_R_nil_R)))
              | Bool_R_false_R ->
                List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R,
                  (x1_UU2081_::[]), (x1_UU2082_::[]), (List_R_cons_R
                  (x1_UU2081_, x1_UU2082_, x1_R, [], [], List_R_nil_R))))
             stack_UU2081_ stack_UU2082_ stack_R) s'_UU2081_ s'_UU2082_ s'_R)
    in sort2rec_R [] [] List_R_nil_R

  (** val sort3_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R **)

  let sort3_R leT_UU2081_ leT_UU2082_ leT_R =
    let rec sort3rec_R stack_UU2081_ stack_UU2082_ stack_R s_UU2081_ s_UU2082_ s_R = match s_R with
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R s_UU2081_ s_UU2082_ s_R
        stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R, _, _, l_R) ->
      (match l_R with
       | List_R_nil_R ->
         merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R s_UU2081_ s_UU2082_
           s_R stack_UU2081_ stack_UU2082_ stack_R
       | List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R, _, _, l0_R) ->
         (match l0_R with
          | List_R_nil_R ->
            merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R
              (if leT_UU2081_ x1_UU2081_ x2_UU2081_
               then s_UU2081_
               else x2_UU2081_::(x1_UU2081_::[]))
              (if leT_UU2082_ x1_UU2082_ x2_UU2082_
               then s_UU2082_
               else x2_UU2082_::(x1_UU2082_::[]))
              (match leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_ x2_UU2082_
                       x2_R with
               | Bool_R_true_R -> s_R
               | Bool_R_false_R ->
                 List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R,
                   (x1_UU2081_::[]), (x1_UU2082_::[]), (List_R_cons_R
                   (x1_UU2081_, x1_UU2082_, x1_R, [], [], List_R_nil_R))))
              stack_UU2081_ stack_UU2082_ stack_R
          | List_R_cons_R (x3_UU2081_, x3_UU2082_, x3_R, s'_UU2081_,
                           s'_UU2082_, s'_R) ->
            let s1_UU2081_ =
              if leT_UU2081_ x1_UU2081_ x2_UU2081_
              then if leT_UU2081_ x2_UU2081_ x3_UU2081_
                   then x1_UU2081_::(x2_UU2081_::(x3_UU2081_::[]))
                   else if leT_UU2081_ x1_UU2081_ x3_UU2081_
                        then x1_UU2081_::(x3_UU2081_::(x2_UU2081_::[]))
                        else x3_UU2081_::(x1_UU2081_::(x2_UU2081_::[]))
              else if leT_UU2081_ x1_UU2081_ x3_UU2081_
                   then x2_UU2081_::(x1_UU2081_::(x3_UU2081_::[]))
                   else if leT_UU2081_ x2_UU2081_ x3_UU2081_
                        then x2_UU2081_::(x3_UU2081_::(x1_UU2081_::[]))
                        else x3_UU2081_::(x2_UU2081_::(x1_UU2081_::[]))
            in
            let s1_UU2082_ =
              if leT_UU2082_ x1_UU2082_ x2_UU2082_
              then if leT_UU2082_ x2_UU2082_ x3_UU2082_
                   then x1_UU2082_::(x2_UU2082_::(x3_UU2082_::[]))
                   else if leT_UU2082_ x1_UU2082_ x3_UU2082_
                        then x1_UU2082_::(x3_UU2082_::(x2_UU2082_::[]))
                        else x3_UU2082_::(x1_UU2082_::(x2_UU2082_::[]))
              else if leT_UU2082_ x1_UU2082_ x3_UU2082_
                   then x2_UU2082_::(x1_UU2082_::(x3_UU2082_::[]))
                   else if leT_UU2082_ x2_UU2082_ x3_UU2082_
                        then x2_UU2082_::(x3_UU2082_::(x1_UU2082_::[]))
                        else x3_UU2082_::(x2_UU2082_::(x1_UU2082_::[]))
            in
            sort3rec_R (merge_sort_push leT_UU2081_ s1_UU2081_ stack_UU2081_)
              (merge_sort_push leT_UU2082_ s1_UU2082_ stack_UU2082_)
              (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R s1_UU2081_
                s1_UU2082_
                (match leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_ x2_UU2082_
                         x2_R with
                 | Bool_R_true_R ->
                   (match leT_R x2_UU2081_ x2_UU2082_ x2_R x3_UU2081_
                            x3_UU2082_ x3_R with
                    | Bool_R_true_R ->
                      List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R,
                        (x2_UU2081_::(x3_UU2081_::[])),
                        (x2_UU2082_::(x3_UU2082_::[])), (List_R_cons_R
                        (x2_UU2081_, x2_UU2082_, x2_R, (x3_UU2081_::[]),
                        (x3_UU2082_::[]), (List_R_cons_R (x3_UU2081_,
                        x3_UU2082_, x3_R, [], [], List_R_nil_R)))))
                    | Bool_R_false_R ->
                      (match leT_R x1_UU2081_ x1_UU2082_ x1_R x3_UU2081_
                               x3_UU2082_ x3_R with
                       | Bool_R_true_R ->
                         List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R,
                           (x3_UU2081_::(x2_UU2081_::[])),
                           (x3_UU2082_::(x2_UU2082_::[])), (List_R_cons_R
                           (x3_UU2081_, x3_UU2082_, x3_R, (x2_UU2081_::[]),
                           (x2_UU2082_::[]), (List_R_cons_R (x2_UU2081_,
                           x2_UU2082_, x2_R, [], [], List_R_nil_R)))))
                       | Bool_R_false_R ->
                         List_R_cons_R (x3_UU2081_, x3_UU2082_, x3_R,
                           (x1_UU2081_::(x2_UU2081_::[])),
                           (x1_UU2082_::(x2_UU2082_::[])), (List_R_cons_R
                           (x1_UU2081_, x1_UU2082_, x1_R, (x2_UU2081_::[]),
                           (x2_UU2082_::[]), (List_R_cons_R (x2_UU2081_,
                           x2_UU2082_, x2_R, [], [], List_R_nil_R)))))))
                 | Bool_R_false_R ->
                   (match leT_R x1_UU2081_ x1_UU2082_ x1_R x3_UU2081_
                            x3_UU2082_ x3_R with
                    | Bool_R_true_R ->
                      List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R,
                        (x1_UU2081_::(x3_UU2081_::[])),
                        (x1_UU2082_::(x3_UU2082_::[])), (List_R_cons_R
                        (x1_UU2081_, x1_UU2082_, x1_R, (x3_UU2081_::[]),
                        (x3_UU2082_::[]), (List_R_cons_R (x3_UU2081_,
                        x3_UU2082_, x3_R, [], [], List_R_nil_R)))))
                    | Bool_R_false_R ->
                      (match leT_R x2_UU2081_ x2_UU2082_ x2_R x3_UU2081_
                               x3_UU2082_ x3_R with
                       | Bool_R_true_R ->
                         List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R,
                           (x3_UU2081_::(x1_UU2081_::[])),
                           (x3_UU2082_::(x1_UU2082_::[])), (List_R_cons_R
                           (x3_UU2081_, x3_UU2082_, x3_R, (x1_UU2081_::[]),
                           (x1_UU2082_::[]), (List_R_cons_R (x1_UU2081_,
                           x1_UU2082_, x1_R, [], [], List_R_nil_R)))))
                       | Bool_R_false_R ->
                         List_R_cons_R (x3_UU2081_, x3_UU2082_, x3_R,
                           (x2_UU2081_::(x1_UU2081_::[])),
                           (x2_UU2082_::(x1_UU2082_::[])), (List_R_cons_R
                           (x2_UU2081_, x2_UU2082_, x2_R, (x1_UU2081_::[]),
                           (x1_UU2082_::[]), (List_R_cons_R (x1_UU2081_,
                           x1_UU2082_, x1_R, [], [], List_R_nil_R))))))))
                stack_UU2081_ stack_UU2082_ stack_R) s'_UU2081_ s'_UU2082_
              s'_R))
    in sort3rec_R [] [] List_R_nil_R

  (** val sortN_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R **)

  let sortN_R leT_UU2081_ leT_UU2082_ leT_R _ _ = function
  | List_R_nil_R -> List_R_nil_R
  | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s_UU2081_, s_UU2082_, s_R0) ->
    let rec sortNrec_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ = function
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R (x_UU2081_0::[])
        (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [],
        [], List_R_nil_R)) stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
      (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
       | Bool_R_true_R ->
         incr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
           s_UU2081_0 s_UU2082_0 s_R2 (x_UU2081_0::[]) (x_UU2082_0::[])
           (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [], [],
           List_R_nil_R))
       | Bool_R_false_R ->
         decr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
           s_UU2081_0 s_UU2082_0 s_R2 (x_UU2081_0::[]) (x_UU2082_0::[])
           (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [], [],
           List_R_nil_R)))
    and incr_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ s_R1 accu_UU2081_ accu_UU2082_ accu_R =
      match s_R1 with
      | List_R_nil_R ->
        merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R
          (List.rev_append accu_UU2081_ (x_UU2081_0::[]))
          (List.rev_append accu_UU2082_ (x_UU2082_0::[]))
          (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
             match s1_R with
             | List_R_nil_R -> s2_R
             | List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s1'_UU2081_,
                              s1'_UU2082_, s1'_R) ->
               catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                 (x_UU2081_1::s2_UU2081_) (x_UU2082_1::s2_UU2082_)
                 (List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s2_UU2081_,
                 s2_UU2082_, s2_R))
           in catrev_R accu_UU2081_ accu_UU2082_ accu_R (x_UU2081_0::[])
                (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0,
                x_R0, [], [], List_R_nil_R))) stack_UU2081_ stack_UU2082_
          stack_R
      | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
        (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
         | Bool_R_true_R ->
           incr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2 (x_UU2081_0::accu_UU2081_)
             (x_UU2082_0::accu_UU2082_) (List_R_cons_R (x_UU2081_0,
             x_UU2082_0, x_R0, accu_UU2081_, accu_UU2082_, accu_R))
         | Bool_R_false_R ->
           sortNrec_R
             (merge_sort_push leT_UU2081_
               (List.rev_append accu_UU2081_ (x_UU2081_0::[])) stack_UU2081_)
             (merge_sort_push leT_UU2082_
               (List.rev_append accu_UU2082_ (x_UU2082_0::[])) stack_UU2082_)
             (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
               (List.rev_append accu_UU2081_ (x_UU2081_0::[]))
               (List.rev_append accu_UU2082_ (x_UU2082_0::[]))
               (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                  match s1_R with
                  | List_R_nil_R -> s2_R
                  | List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s1'_UU2081_,
                                   s1'_UU2082_, s1'_R) ->
                    catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                      (x_UU2081_1::s2_UU2081_) (x_UU2082_1::s2_UU2082_)
                      (List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1,
                      s2_UU2081_, s2_UU2082_, s2_R))
                in catrev_R accu_UU2081_ accu_UU2082_ accu_R (x_UU2081_0::[])
                     (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0,
                     x_R0, [], [], List_R_nil_R))) stack_UU2081_
               stack_UU2082_ stack_R) y_UU2081_ y_UU2082_ y_R s_UU2081_0
             s_UU2082_0 s_R2)
    and decr_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ s_R1 accu_UU2081_ accu_UU2082_ accu_R =
      match s_R1 with
      | List_R_nil_R ->
        merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R
          (x_UU2081_0::accu_UU2081_) (x_UU2082_0::accu_UU2082_)
          (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, accu_UU2081_,
          accu_UU2082_, accu_R)) stack_UU2081_ stack_UU2082_ stack_R
      | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
        (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
         | Bool_R_true_R ->
           sortNrec_R
             (merge_sort_push leT_UU2081_ (x_UU2081_0::accu_UU2081_)
               stack_UU2081_)
             (merge_sort_push leT_UU2082_ (x_UU2082_0::accu_UU2082_)
               stack_UU2082_)
             (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
               (x_UU2081_0::accu_UU2081_) (x_UU2082_0::accu_UU2082_)
               (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, accu_UU2081_,
               accu_UU2082_, accu_R)) stack_UU2081_ stack_UU2082_ stack_R)
             y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2
         | Bool_R_false_R ->
           decr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2 (x_UU2081_0::accu_UU2081_)
             (x_UU2082_0::accu_UU2082_) (List_R_cons_R (x_UU2081_0,
             x_UU2082_0, x_R0, accu_UU2081_, accu_UU2082_, accu_R)))
    in sortNrec_R [] [] List_R_nil_R x_UU2081_ x_UU2082_ x_R s_UU2081_
         s_UU2082_ s_R0

  (** val sort1_stable : StableSort.coq_function **)

  let sort1_stable =
    { StableSort.apply = (fun _ -> sort1); StableSort.coq_function__1 =
      (fun _ _ _ -> sort1_R); StableSort.coq_function__2 = (fun _ -> sort1P) }

  (** val sort2_stable : StableSort.coq_function **)

  let sort2_stable =
    { StableSort.apply = (fun _ -> sort2); StableSort.coq_function__1 =
      (fun _ _ _ -> sort2_R); StableSort.coq_function__2 = (fun _ -> sort2P) }

  (** val sort3_stable : StableSort.coq_function **)

  let sort3_stable =
    { StableSort.apply = (fun _ -> sort3); StableSort.coq_function__1 =
      (fun _ _ _ -> sort3_R); StableSort.coq_function__2 = (fun _ -> sort3P) }

  (** val sortN_stable : StableSort.coq_function **)

  let sortN_stable =
    { StableSort.apply = (fun _ -> sortN); StableSort.coq_function__1 =
      (fun _ _ _ -> sortN_R); StableSort.coq_function__2 = (fun _ -> sortNP) }
 end

module CBN = CBN_(Merge)

module CBNAcc = CBN_(MergeAcc)

module CBV_ =
 functor (M:RevmergeSig) ->
 struct
  (** val merge_sort_push :
      'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list **)

  let rec merge_sort_push leT xs stack = match stack with
  | [] -> xs::stack
  | ys::stack0 ->
    (match ys with
     | [] -> xs::stack0
     | _::_ ->
       (match stack0 with
        | [] -> []::((M.revmerge leT ys xs)::stack0)
        | zs::stack1 ->
          (match zs with
           | [] -> []::((M.revmerge leT ys xs)::stack1)
           | _::_ ->
             []::([]::(merge_sort_push leT
                        (M.revmerge (fun x y -> leT y x)
                          (M.revmerge leT ys xs) zs) stack1)))))

  (** val merge_sort_pop :
      'a1 rel -> bool -> 'a1 list -> 'a1 list list -> 'a1 list **)

  let rec merge_sort_pop leT mode xs = function
  | [] -> if mode then List.rev xs else xs
  | ys::stack0 ->
    (match ys with
     | [] ->
       (match stack0 with
        | [] -> merge_sort_pop leT (not mode) (List.rev xs) stack0
        | l::stack1 ->
          (match l with
           | [] -> merge_sort_pop leT mode xs stack1
           | _::_ -> merge_sort_pop leT (not mode) (List.rev xs) stack0))
     | _::_ ->
       if mode
       then merge_sort_pop leT false (M.revmerge (fun x y -> leT y x) xs ys)
              stack0
       else merge_sort_pop leT true (M.revmerge leT ys xs) stack0)

  (** val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

  let rec sort1rec leT stack = function
  | [] -> merge_sort_pop leT false [] stack
  | x::s0 -> sort1rec leT (merge_sort_push leT (x::[]) stack) s0

  (** val sort1 : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sort1 leT =
    sort1rec leT []

  (** val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

  let rec sort2rec leT stack s = match s with
  | [] -> merge_sort_pop leT false s stack
  | x1::l ->
    (match l with
     | [] -> merge_sort_pop leT false s stack
     | x2::s' ->
       sort2rec leT
         (merge_sort_push leT
           (if leT x1 x2 then x1::(x2::[]) else x2::(x1::[])) stack) s')

  (** val sort2 : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sort2 leT =
    sort2rec leT []

  (** val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

  let rec sort3rec leT stack s = match s with
  | [] -> merge_sort_pop leT false s stack
  | x1::l ->
    (match l with
     | [] -> merge_sort_pop leT false s stack
     | x2::l0 ->
       (match l0 with
        | [] ->
          merge_sort_pop leT false (if leT x1 x2 then s else x2::(x1::[]))
            stack
        | x3::s' ->
          sort3rec leT
            (merge_sort_push leT
              (if leT x1 x2
               then if leT x2 x3
                    then x1::(x2::(x3::[]))
                    else if leT x1 x3
                         then x1::(x3::(x2::[]))
                         else x3::(x1::(x2::[]))
               else if leT x1 x3
                    then x2::(x1::(x3::[]))
                    else if leT x2 x3
                         then x2::(x3::(x1::[]))
                         else x3::(x2::(x1::[]))) stack) s'))

  (** val sort3 : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sort3 leT =
    sort3rec leT []

  (** val sortNrec :
      'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list **)

  let sortNrec leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT false (x::[]) stack
    | y::s0 ->
      if leT x y then incr0 stack y s0 (x::[]) else decr0 stack y s0 (x::[])
    and incr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT false (List.rev_append accu (x::[])) stack
      | y::s0 ->
        if leT x y
        then incr0 stack y s0 (x::accu)
        else sortNrec0
               (merge_sort_push leT (List.rev_append accu (x::[])) stack) y s0
    and decr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT false (x::accu) stack
      | y::s0 ->
        if leT x y
        then sortNrec0 (merge_sort_push leT (x::accu) stack) y s0
        else decr0 stack y s0 (x::accu)
    in sortNrec0

  (** val incr :
      'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list **)

  let incr leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT false (x::[]) stack
    | y::s0 ->
      if leT x y then incr0 stack y s0 (x::[]) else decr0 stack y s0 (x::[])
    and incr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT false (List.rev_append accu (x::[])) stack
      | y::s0 ->
        if leT x y
        then incr0 stack y s0 (x::accu)
        else sortNrec0
               (merge_sort_push leT (List.rev_append accu (x::[])) stack) y s0
    and decr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT false (x::accu) stack
      | y::s0 ->
        if leT x y
        then sortNrec0 (merge_sort_push leT (x::accu) stack) y s0
        else decr0 stack y s0 (x::accu)
    in incr0

  (** val decr :
      'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list **)

  let decr leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT false (x::[]) stack
    | y::s0 ->
      if leT x y then incr0 stack y s0 (x::[]) else decr0 stack y s0 (x::[])
    and incr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT false (List.rev_append accu (x::[])) stack
      | y::s0 ->
        if leT x y
        then incr0 stack y s0 (x::accu)
        else sortNrec0
               (merge_sort_push leT (List.rev_append accu (x::[])) stack) y s0
    and decr0 stack x s accu =
      match s with
      | [] -> merge_sort_pop leT false (x::accu) stack
      | y::s0 ->
        if leT x y
        then sortNrec0 (merge_sort_push leT (x::accu) stack) y s0
        else decr0 stack y s0 (x::accu)
    in decr0

  (** val sortN : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sortN leT = function
  | [] -> []
  | x::s0 -> sortNrec leT [] x s0

  (** val merge_sort_pushP :
      'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
      StableSort.trace list sig2 **)

  let rec merge_sort_pushP leT t = function
  | [] -> t::[]
  | a::l ->
    (match l with
     | [] ->
       ssr_have (fun _ -> nilP) (fun __top_assumption_ ->
         match __top_assumption_ __ (StableSort.flatten_trace leT a) with
         | ReflectT -> t::[]
         | ReflectF ->
           (StableSort.empty_trace leT)::((StableSort.Coq_branch_trace (true,
             a, t))::[]))
     | a0::l0 ->
       ssr_have (fun _ -> nilP) (fun __top_assumption_ ->
         match __top_assumption_ __ (StableSort.flatten_trace leT a) with
         | ReflectT -> t::(a0::l0)
         | ReflectF ->
           ssr_have (fun _ -> nilP) (fun __top_assumption_0 ->
             match __top_assumption_0 __ (StableSort.flatten_trace leT a0) with
             | ReflectT ->
               (StableSort.empty_trace leT)::((StableSort.Coq_branch_trace
                 (true, a, t))::l0)
             | ReflectF ->
               ssr_have
                 (merge_sort_pushP leT (StableSort.Coq_branch_trace (false,
                   a0, (StableSort.Coq_branch_trace (true, a, t)))) l0)
                 (fun __top_assumption_1 ->
                 (StableSort.empty_trace leT)::((StableSort.empty_trace leT)::__top_assumption_1)))))

  (** val merge_sort_popP :
      'a1 rel -> bool -> 'a1 StableSort.trace -> 'a1 StableSort.trace list ->
      'a1 StableSort.trace sig2 **)

  let rec merge_sort_popP leT mode t = function
  | [] -> t
  | a::l ->
    (match StableSort.trace_nilP leT a with
     | StableSort.TraceNil ->
       (match l with
        | [] -> t
        | a0::l0 ->
          (match StableSort.trace_nilP leT a0 with
           | StableSort.TraceNil -> merge_sort_popP leT mode t l0
           | StableSort.TraceNotNil ->
             merge_sort_popP leT mode (StableSort.Coq_branch_trace (mode, a0,
               t)) l0))
     | StableSort.TraceNotNil ->
       merge_sort_popP leT (not mode) (StableSort.Coq_branch_trace
         ((not mode), a, t)) l)

  (** val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2 **)

  let sort1P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec f l stack =
          match l with
          | [] -> merge_sort_popP leT false (StableSort.empty_trace leT) stack
          | y::l0 ->
            f l0
              (merge_sort_pushP leT (StableSort.Coq_leaf_trace
                ((Obj.magic true), (y::[]))) stack)
        in f s []))

  (** val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2 **)

  let sort2P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec iHs stack = function
        | [] ->
          merge_sort_popP leT false (StableSort.Coq_leaf_trace
            ((Obj.magic true), [])) stack
        | a::l ->
          (match l with
           | [] ->
             merge_sort_popP leT false (StableSort.Coq_leaf_trace
               ((Obj.magic true), (a::[]))) stack
           | a0::l0 ->
             iHs
               (merge_sort_pushP leT (StableSort.Coq_leaf_trace
                 ((Obj.magic leT a a0), (a::(a0::[])))) stack) l0)
        in iHs [] s))

  (** val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2 **)

  let sort3P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        ssr_have __ (fun _ ->
          let rec iHs stack = function
          | [] ->
            merge_sort_popP leT false (StableSort.Coq_leaf_trace
              ((Obj.magic true), [])) stack
          | a::l ->
            (match l with
             | [] ->
               merge_sort_popP leT false (StableSort.Coq_leaf_trace
                 ((Obj.magic true), (a::[]))) stack
             | a0::l0 ->
               (match l0 with
                | [] ->
                  merge_sort_popP leT false (StableSort.Coq_leaf_trace
                    ((Obj.magic leT a a0), (a::(a0::[])))) stack
                | a1::l1 ->
                  ssr_have __ (fun _ _ ->
                    iHs
                      (merge_sort_pushP leT (StableSort.Coq_branch_trace
                        (false, (StableSort.Coq_leaf_trace
                        ((Obj.magic leT a a0), (a::(a0::[])))),
                        (StableSort.Coq_leaf_trace ((Obj.magic true),
                        (a1::[]))))) stack) l1) __))
          in iHs [] s)))

  (** val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2 **)

  let sortNP leT = function
  | [] -> StableSort.empty_trace leT
  | a::l ->
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec iHs stack x = function
        | [] ->
          merge_sort_popP leT false (StableSort.Coq_leaf_trace
            ((Obj.magic true), (x::[]))) stack
        | a0::l0 ->
          ssr_have __
            (ssr_have __ (fun _ _ ->
              let rec f l1 ord x0 acc =
                match l1 with
                | [] ->
                  merge_sort_popP leT false (StableSort.Coq_leaf_trace
                    ((Obj.magic ord), (List.rev (x0::acc)))) stack
                | y::l2 ->
                  if ord
                  then (match boolP (leT x0 y) with
                        | AltTrue ->
                          ssr_have __ (fun _ -> f l2 true y (x0::acc))
                        | AltFalse ->
                          iHs
                            (merge_sort_pushP leT (StableSort.Coq_leaf_trace
                              ((Obj.magic true), (List.rev (x0::acc)))) stack)
                            y l2)
                  else (match boolP (leT x0 y) with
                        | AltTrue ->
                          iHs
                            (merge_sort_pushP leT (StableSort.Coq_leaf_trace
                              ((Obj.magic false), (List.rev (x0::acc))))
                              stack) y l2
                        | AltFalse ->
                          ssr_have __ (fun _ -> f l2 false y (x0::acc)))
              in f l0 (leT x a0) a0 (x::[])))
        in iHs [] a l))

  (** val revmerge_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
      list_R -> ('a1, 'a2, 'a3) list_R **)

  let revmerge_R =
    M.revmerge_R

  (** val merge_sort_push_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
      'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1 list, 'a2 list, ('a1,
      'a2, 'a3) list_R) list_R **)

  let merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R =
    let geT_UU2081_ = fun x y -> leT_UU2081_ y x in
    let geT_UU2082_ = fun x y -> leT_UU2082_ y x in
    let fix_merge_sort_push_1 =
      let rec merge_sort_push0 xs stack = match stack with
      | [] -> xs::stack
      | ys::stack0 ->
        (match ys with
         | [] -> xs::stack0
         | _::_ ->
           (match stack0 with
            | [] -> []::((M.revmerge leT_UU2081_ ys xs)::stack0)
            | zs::stack1 ->
              (match zs with
               | [] -> []::((M.revmerge leT_UU2081_ ys xs)::stack1)
               | _::_ ->
                 []::([]::(merge_sort_push0
                            (M.revmerge geT_UU2081_
                              (M.revmerge leT_UU2081_ ys xs) zs) stack1)))))
      in merge_sort_push0
    in
    let fix_merge_sort_push_2 =
      let rec merge_sort_push0 xs stack = match stack with
      | [] -> xs::stack
      | ys::stack0 ->
        (match ys with
         | [] -> xs::stack0
         | _::_ ->
           (match stack0 with
            | [] -> []::((M.revmerge leT_UU2082_ ys xs)::stack0)
            | zs::stack1 ->
              (match zs with
               | [] -> []::((M.revmerge leT_UU2082_ ys xs)::stack1)
               | _::_ ->
                 []::([]::(merge_sort_push0
                            (M.revmerge geT_UU2082_
                              (M.revmerge leT_UU2082_ ys xs) zs) stack1)))))
      in merge_sort_push0
    in
    let rec merge_sort_push_R0 xs_UU2081_ xs_UU2082_ xs_R stack_UU2081_ stack_UU2082_ stack_R = match stack_R with
    | List_R_nil_R ->
      List_R_cons_R (xs_UU2081_, xs_UU2082_, xs_R, stack_UU2081_,
        stack_UU2082_, stack_R)
    | List_R_cons_R (ys_UU2081_, ys_UU2082_, ys_R, stack_UU2081_0,
                     stack_UU2082_0, stack_R0) ->
      (match ys_R with
       | List_R_nil_R ->
         List_R_cons_R (xs_UU2081_, xs_UU2082_, xs_R, stack_UU2081_0,
           stack_UU2082_0, stack_R0)
       | List_R_cons_R (_, _, _, _, _, _) ->
         (match stack_R0 with
          | List_R_nil_R ->
            List_R_cons_R ([], [], List_R_nil_R,
              ((M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)::stack_UU2081_0),
              ((M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)::stack_UU2082_0),
              (List_R_cons_R ((M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_),
              (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_),
              (revmerge_R leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_ ys_UU2082_
                ys_R xs_UU2081_ xs_UU2082_ xs_R), stack_UU2081_0,
              stack_UU2082_0, stack_R0)))
          | List_R_cons_R (zs_UU2081_, zs_UU2082_, zs_R, stack_UU2081_1,
                           stack_UU2082_1, stack_R1) ->
            (match zs_R with
             | List_R_nil_R ->
               List_R_cons_R ([], [], List_R_nil_R,
                 ((M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)::stack_UU2081_1),
                 ((M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)::stack_UU2082_1),
                 (List_R_cons_R
                 ((M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_),
                 (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_),
                 (revmerge_R leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_
                   ys_UU2082_ ys_R xs_UU2081_ xs_UU2082_ xs_R),
                 stack_UU2081_1, stack_UU2082_1, stack_R1)))
             | List_R_cons_R (_, _, _, _, _, _) ->
               List_R_cons_R ([], [], List_R_nil_R,
                 ([]::(fix_merge_sort_push_1
                        (M.revmerge geT_UU2081_
                          (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                          zs_UU2081_) stack_UU2081_1)),
                 ([]::(fix_merge_sort_push_2
                        (M.revmerge geT_UU2082_
                          (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                          zs_UU2082_) stack_UU2082_1)), (List_R_cons_R ([],
                 [], List_R_nil_R,
                 (fix_merge_sort_push_1
                   (M.revmerge geT_UU2081_
                     (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                     zs_UU2081_) stack_UU2081_1),
                 (fix_merge_sort_push_2
                   (M.revmerge geT_UU2082_
                     (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                     zs_UU2082_) stack_UU2082_1),
                 (merge_sort_push_R0
                   (M.revmerge geT_UU2081_
                     (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                     zs_UU2081_)
                   (M.revmerge geT_UU2082_
                     (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                     zs_UU2082_)
                   (revmerge_R geT_UU2081_ geT_UU2082_
                     (fun x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R ->
                     leT_R y_UU2081_ y_UU2082_ y_R x_UU2081_ x_UU2082_ x_R)
                     (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                     (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                     (revmerge_R leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_
                       ys_UU2082_ ys_R xs_UU2081_ xs_UU2082_ xs_R) zs_UU2081_
                     zs_UU2082_ zs_R) stack_UU2081_1 stack_UU2082_1 stack_R1)))))))
    in merge_sort_push_R0

  (** val merge_sort_pop_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> bool -> bool -> bool_R
      -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R -> 'a1 list list ->
      'a2 list list -> ('a1 list, 'a2 list, ('a1, 'a2, 'a3) list_R) list_R ->
      ('a1, 'a2, 'a3) list_R **)

  let merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R =
    let geT_UU2081_ = fun x y -> leT_UU2081_ y x in
    let geT_UU2082_ = fun x y -> leT_UU2082_ y x in
    let rec merge_sort_pop_R0 mode_UU2081_ mode_UU2082_ mode_R xs_UU2081_ xs_UU2082_ xs_R _ _ = function
    | List_R_nil_R ->
      (match mode_R with
       | Bool_R_true_R ->
         let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
           match s1_R with
           | List_R_nil_R -> s2_R
           | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s1'_UU2081_,
                            s1'_UU2082_, s1'_R) ->
             catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R (x_UU2081_::s2_UU2081_)
               (x_UU2082_::s2_UU2082_) (List_R_cons_R (x_UU2081_, x_UU2082_,
               x_R, s2_UU2081_, s2_UU2082_, s2_R))
         in catrev_R xs_UU2081_ xs_UU2082_ xs_R [] [] List_R_nil_R
       | Bool_R_false_R -> xs_R)
    | List_R_cons_R (ys_UU2081_, ys_UU2082_, ys_R, stack_UU2081_,
                     stack_UU2082_, stack_R0) ->
      (match ys_R with
       | List_R_nil_R ->
         (match stack_R0 with
          | List_R_nil_R ->
            merge_sort_pop_R0 (not mode_UU2081_) (not mode_UU2082_)
              (match mode_R with
               | Bool_R_true_R -> Bool_R_false_R
               | Bool_R_false_R -> Bool_R_true_R) (List.rev xs_UU2081_)
              (List.rev xs_UU2082_)
              (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                 match s1_R with
                 | List_R_nil_R -> s2_R
                 | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s1'_UU2081_,
                                  s1'_UU2082_, s1'_R) ->
                   catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                     (x_UU2081_::s2_UU2081_) (x_UU2082_::s2_UU2082_)
                     (List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s2_UU2081_,
                     s2_UU2082_, s2_R))
               in catrev_R xs_UU2081_ xs_UU2082_ xs_R [] [] List_R_nil_R)
              stack_UU2081_ stack_UU2082_ stack_R0
          | List_R_cons_R (_, _, l_R, stack_UU2081_0, stack_UU2082_0, stack_R1) ->
            (match l_R with
             | List_R_nil_R ->
               merge_sort_pop_R0 mode_UU2081_ mode_UU2082_ mode_R xs_UU2081_
                 xs_UU2082_ xs_R stack_UU2081_0 stack_UU2082_0 stack_R1
             | List_R_cons_R (_, _, _, _, _, _) ->
               merge_sort_pop_R0 (not mode_UU2081_) (not mode_UU2082_)
                 (match mode_R with
                  | Bool_R_true_R -> Bool_R_false_R
                  | Bool_R_false_R -> Bool_R_true_R) (List.rev xs_UU2081_)
                 (List.rev xs_UU2082_)
                 (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                    match s1_R with
                    | List_R_nil_R -> s2_R
                    | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s1'_UU2081_,
                                     s1'_UU2082_, s1'_R) ->
                      catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                        (x_UU2081_::s2_UU2081_) (x_UU2082_::s2_UU2082_)
                        (List_R_cons_R (x_UU2081_, x_UU2082_, x_R,
                        s2_UU2081_, s2_UU2082_, s2_R))
                  in catrev_R xs_UU2081_ xs_UU2082_ xs_R [] [] List_R_nil_R)
                 stack_UU2081_ stack_UU2082_ stack_R0))
       | List_R_cons_R (_, _, _, _, _, _) ->
         (match mode_R with
          | Bool_R_true_R ->
            merge_sort_pop_R0 false false Bool_R_false_R
              (M.revmerge geT_UU2081_ xs_UU2081_ ys_UU2081_)
              (M.revmerge geT_UU2082_ xs_UU2082_ ys_UU2082_)
              (revmerge_R geT_UU2081_ geT_UU2082_
                (fun x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R ->
                leT_R y_UU2081_ y_UU2082_ y_R x_UU2081_ x_UU2082_ x_R)
                xs_UU2081_ xs_UU2082_ xs_R ys_UU2081_ ys_UU2082_ ys_R)
              stack_UU2081_ stack_UU2082_ stack_R0
          | Bool_R_false_R ->
            merge_sort_pop_R0 true true Bool_R_true_R
              (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
              (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
              (revmerge_R leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_ ys_UU2082_
                ys_R xs_UU2081_ xs_UU2082_ xs_R) stack_UU2081_ stack_UU2082_
              stack_R0))
    in merge_sort_pop_R0

  (** val sort1_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R **)

  let sort1_R leT_UU2081_ leT_UU2082_ leT_R =
    let rec sort1rec_R stack_UU2081_ stack_UU2082_ stack_R _ _ = function
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
        Bool_R_false_R [] [] List_R_nil_R stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s_UU2081_, s_UU2082_, s_R0) ->
      sort1rec_R (merge_sort_push leT_UU2081_ (x_UU2081_::[]) stack_UU2081_)
        (merge_sort_push leT_UU2082_ (x_UU2082_::[]) stack_UU2082_)
        (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R (x_UU2081_::[])
          (x_UU2082_::[]) (List_R_cons_R (x_UU2081_, x_UU2082_, x_R, [], [],
          List_R_nil_R)) stack_UU2081_ stack_UU2082_ stack_R) s_UU2081_
        s_UU2082_ s_R0
    in sort1rec_R [] [] List_R_nil_R

  (** val sort2_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R **)

  let sort2_R leT_UU2081_ leT_UU2082_ leT_R =
    let rec sort2rec_R stack_UU2081_ stack_UU2082_ stack_R s_UU2081_ s_UU2082_ s_R = match s_R with
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
        Bool_R_false_R s_UU2081_ s_UU2082_ s_R stack_UU2081_ stack_UU2082_
        stack_R
    | List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R, _, _, l_R) ->
      (match l_R with
       | List_R_nil_R ->
         merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
           Bool_R_false_R s_UU2081_ s_UU2082_ s_R stack_UU2081_ stack_UU2082_
           stack_R
       | List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R, s'_UU2081_, s'_UU2082_,
                        s'_R) ->
         let s1_UU2081_ =
           if leT_UU2081_ x1_UU2081_ x2_UU2081_
           then x1_UU2081_::(x2_UU2081_::[])
           else x2_UU2081_::(x1_UU2081_::[])
         in
         let s1_UU2082_ =
           if leT_UU2082_ x1_UU2082_ x2_UU2082_
           then x1_UU2082_::(x2_UU2082_::[])
           else x2_UU2082_::(x1_UU2082_::[])
         in
         sort2rec_R (merge_sort_push leT_UU2081_ s1_UU2081_ stack_UU2081_)
           (merge_sort_push leT_UU2082_ s1_UU2082_ stack_UU2082_)
           (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R s1_UU2081_
             s1_UU2082_
             (match leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_ x2_UU2082_
                      x2_R with
              | Bool_R_true_R ->
                List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R,
                  (x2_UU2081_::[]), (x2_UU2082_::[]), (List_R_cons_R
                  (x2_UU2081_, x2_UU2082_, x2_R, [], [], List_R_nil_R)))
              | Bool_R_false_R ->
                List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R,
                  (x1_UU2081_::[]), (x1_UU2082_::[]), (List_R_cons_R
                  (x1_UU2081_, x1_UU2082_, x1_R, [], [], List_R_nil_R))))
             stack_UU2081_ stack_UU2082_ stack_R) s'_UU2081_ s'_UU2082_ s'_R)
    in sort2rec_R [] [] List_R_nil_R

  (** val sort3_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R **)

  let sort3_R leT_UU2081_ leT_UU2082_ leT_R =
    let rec sort3rec_R stack_UU2081_ stack_UU2082_ stack_R s_UU2081_ s_UU2082_ s_R = match s_R with
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
        Bool_R_false_R s_UU2081_ s_UU2082_ s_R stack_UU2081_ stack_UU2082_
        stack_R
    | List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R, _, _, l_R) ->
      (match l_R with
       | List_R_nil_R ->
         merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
           Bool_R_false_R s_UU2081_ s_UU2082_ s_R stack_UU2081_ stack_UU2082_
           stack_R
       | List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R, _, _, l0_R) ->
         (match l0_R with
          | List_R_nil_R ->
            merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
              Bool_R_false_R
              (if leT_UU2081_ x1_UU2081_ x2_UU2081_
               then s_UU2081_
               else x2_UU2081_::(x1_UU2081_::[]))
              (if leT_UU2082_ x1_UU2082_ x2_UU2082_
               then s_UU2082_
               else x2_UU2082_::(x1_UU2082_::[]))
              (match leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_ x2_UU2082_
                       x2_R with
               | Bool_R_true_R -> s_R
               | Bool_R_false_R ->
                 List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R,
                   (x1_UU2081_::[]), (x1_UU2082_::[]), (List_R_cons_R
                   (x1_UU2081_, x1_UU2082_, x1_R, [], [], List_R_nil_R))))
              stack_UU2081_ stack_UU2082_ stack_R
          | List_R_cons_R (x3_UU2081_, x3_UU2082_, x3_R, s'_UU2081_,
                           s'_UU2082_, s'_R) ->
            let s1_UU2081_ =
              if leT_UU2081_ x1_UU2081_ x2_UU2081_
              then if leT_UU2081_ x2_UU2081_ x3_UU2081_
                   then x1_UU2081_::(x2_UU2081_::(x3_UU2081_::[]))
                   else if leT_UU2081_ x1_UU2081_ x3_UU2081_
                        then x1_UU2081_::(x3_UU2081_::(x2_UU2081_::[]))
                        else x3_UU2081_::(x1_UU2081_::(x2_UU2081_::[]))
              else if leT_UU2081_ x1_UU2081_ x3_UU2081_
                   then x2_UU2081_::(x1_UU2081_::(x3_UU2081_::[]))
                   else if leT_UU2081_ x2_UU2081_ x3_UU2081_
                        then x2_UU2081_::(x3_UU2081_::(x1_UU2081_::[]))
                        else x3_UU2081_::(x2_UU2081_::(x1_UU2081_::[]))
            in
            let s1_UU2082_ =
              if leT_UU2082_ x1_UU2082_ x2_UU2082_
              then if leT_UU2082_ x2_UU2082_ x3_UU2082_
                   then x1_UU2082_::(x2_UU2082_::(x3_UU2082_::[]))
                   else if leT_UU2082_ x1_UU2082_ x3_UU2082_
                        then x1_UU2082_::(x3_UU2082_::(x2_UU2082_::[]))
                        else x3_UU2082_::(x1_UU2082_::(x2_UU2082_::[]))
              else if leT_UU2082_ x1_UU2082_ x3_UU2082_
                   then x2_UU2082_::(x1_UU2082_::(x3_UU2082_::[]))
                   else if leT_UU2082_ x2_UU2082_ x3_UU2082_
                        then x2_UU2082_::(x3_UU2082_::(x1_UU2082_::[]))
                        else x3_UU2082_::(x2_UU2082_::(x1_UU2082_::[]))
            in
            sort3rec_R (merge_sort_push leT_UU2081_ s1_UU2081_ stack_UU2081_)
              (merge_sort_push leT_UU2082_ s1_UU2082_ stack_UU2082_)
              (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R s1_UU2081_
                s1_UU2082_
                (match leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_ x2_UU2082_
                         x2_R with
                 | Bool_R_true_R ->
                   (match leT_R x2_UU2081_ x2_UU2082_ x2_R x3_UU2081_
                            x3_UU2082_ x3_R with
                    | Bool_R_true_R ->
                      List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R,
                        (x2_UU2081_::(x3_UU2081_::[])),
                        (x2_UU2082_::(x3_UU2082_::[])), (List_R_cons_R
                        (x2_UU2081_, x2_UU2082_, x2_R, (x3_UU2081_::[]),
                        (x3_UU2082_::[]), (List_R_cons_R (x3_UU2081_,
                        x3_UU2082_, x3_R, [], [], List_R_nil_R)))))
                    | Bool_R_false_R ->
                      (match leT_R x1_UU2081_ x1_UU2082_ x1_R x3_UU2081_
                               x3_UU2082_ x3_R with
                       | Bool_R_true_R ->
                         List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R,
                           (x3_UU2081_::(x2_UU2081_::[])),
                           (x3_UU2082_::(x2_UU2082_::[])), (List_R_cons_R
                           (x3_UU2081_, x3_UU2082_, x3_R, (x2_UU2081_::[]),
                           (x2_UU2082_::[]), (List_R_cons_R (x2_UU2081_,
                           x2_UU2082_, x2_R, [], [], List_R_nil_R)))))
                       | Bool_R_false_R ->
                         List_R_cons_R (x3_UU2081_, x3_UU2082_, x3_R,
                           (x1_UU2081_::(x2_UU2081_::[])),
                           (x1_UU2082_::(x2_UU2082_::[])), (List_R_cons_R
                           (x1_UU2081_, x1_UU2082_, x1_R, (x2_UU2081_::[]),
                           (x2_UU2082_::[]), (List_R_cons_R (x2_UU2081_,
                           x2_UU2082_, x2_R, [], [], List_R_nil_R)))))))
                 | Bool_R_false_R ->
                   (match leT_R x1_UU2081_ x1_UU2082_ x1_R x3_UU2081_
                            x3_UU2082_ x3_R with
                    | Bool_R_true_R ->
                      List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R,
                        (x1_UU2081_::(x3_UU2081_::[])),
                        (x1_UU2082_::(x3_UU2082_::[])), (List_R_cons_R
                        (x1_UU2081_, x1_UU2082_, x1_R, (x3_UU2081_::[]),
                        (x3_UU2082_::[]), (List_R_cons_R (x3_UU2081_,
                        x3_UU2082_, x3_R, [], [], List_R_nil_R)))))
                    | Bool_R_false_R ->
                      (match leT_R x2_UU2081_ x2_UU2082_ x2_R x3_UU2081_
                               x3_UU2082_ x3_R with
                       | Bool_R_true_R ->
                         List_R_cons_R (x2_UU2081_, x2_UU2082_, x2_R,
                           (x3_UU2081_::(x1_UU2081_::[])),
                           (x3_UU2082_::(x1_UU2082_::[])), (List_R_cons_R
                           (x3_UU2081_, x3_UU2082_, x3_R, (x1_UU2081_::[]),
                           (x1_UU2082_::[]), (List_R_cons_R (x1_UU2081_,
                           x1_UU2082_, x1_R, [], [], List_R_nil_R)))))
                       | Bool_R_false_R ->
                         List_R_cons_R (x3_UU2081_, x3_UU2082_, x3_R,
                           (x2_UU2081_::(x1_UU2081_::[])),
                           (x2_UU2082_::(x1_UU2082_::[])), (List_R_cons_R
                           (x2_UU2081_, x2_UU2082_, x2_R, (x1_UU2081_::[]),
                           (x1_UU2082_::[]), (List_R_cons_R (x1_UU2081_,
                           x1_UU2082_, x1_R, [], [], List_R_nil_R))))))))
                stack_UU2081_ stack_UU2082_ stack_R) s'_UU2081_ s'_UU2082_
              s'_R))
    in sort3rec_R [] [] List_R_nil_R

  (** val sortN_R :
      'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
      ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R **)

  let sortN_R leT_UU2081_ leT_UU2082_ leT_R _ _ = function
  | List_R_nil_R -> List_R_nil_R
  | List_R_cons_R (x_UU2081_, x_UU2082_, x_R, s_UU2081_, s_UU2082_, s_R0) ->
    let rec sortNrec_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ = function
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
        Bool_R_false_R (x_UU2081_0::[]) (x_UU2082_0::[]) (List_R_cons_R
        (x_UU2081_0, x_UU2082_0, x_R0, [], [], List_R_nil_R)) stack_UU2081_
        stack_UU2082_ stack_R
    | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
      (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
       | Bool_R_true_R ->
         incr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
           s_UU2081_0 s_UU2082_0 s_R2 (x_UU2081_0::[]) (x_UU2082_0::[])
           (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [], [],
           List_R_nil_R))
       | Bool_R_false_R ->
         decr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
           s_UU2081_0 s_UU2082_0 s_R2 (x_UU2081_0::[]) (x_UU2082_0::[])
           (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [], [],
           List_R_nil_R)))
    and incr_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ s_R1 accu_UU2081_ accu_UU2082_ accu_R =
      match s_R1 with
      | List_R_nil_R ->
        merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
          Bool_R_false_R (List.rev_append accu_UU2081_ (x_UU2081_0::[]))
          (List.rev_append accu_UU2082_ (x_UU2082_0::[]))
          (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
             match s1_R with
             | List_R_nil_R -> s2_R
             | List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s1'_UU2081_,
                              s1'_UU2082_, s1'_R) ->
               catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                 (x_UU2081_1::s2_UU2081_) (x_UU2082_1::s2_UU2082_)
                 (List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s2_UU2081_,
                 s2_UU2082_, s2_R))
           in catrev_R accu_UU2081_ accu_UU2082_ accu_R (x_UU2081_0::[])
                (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0,
                x_R0, [], [], List_R_nil_R))) stack_UU2081_ stack_UU2082_
          stack_R
      | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
        (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
         | Bool_R_true_R ->
           incr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2 (x_UU2081_0::accu_UU2081_)
             (x_UU2082_0::accu_UU2082_) (List_R_cons_R (x_UU2081_0,
             x_UU2082_0, x_R0, accu_UU2081_, accu_UU2082_, accu_R))
         | Bool_R_false_R ->
           sortNrec_R
             (merge_sort_push leT_UU2081_
               (List.rev_append accu_UU2081_ (x_UU2081_0::[])) stack_UU2081_)
             (merge_sort_push leT_UU2082_
               (List.rev_append accu_UU2082_ (x_UU2082_0::[])) stack_UU2082_)
             (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
               (List.rev_append accu_UU2081_ (x_UU2081_0::[]))
               (List.rev_append accu_UU2082_ (x_UU2082_0::[]))
               (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                  match s1_R with
                  | List_R_nil_R -> s2_R
                  | List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s1'_UU2081_,
                                   s1'_UU2082_, s1'_R) ->
                    catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                      (x_UU2081_1::s2_UU2081_) (x_UU2082_1::s2_UU2082_)
                      (List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1,
                      s2_UU2081_, s2_UU2082_, s2_R))
                in catrev_R accu_UU2081_ accu_UU2082_ accu_R (x_UU2081_0::[])
                     (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0,
                     x_R0, [], [], List_R_nil_R))) stack_UU2081_
               stack_UU2082_ stack_R) y_UU2081_ y_UU2082_ y_R s_UU2081_0
             s_UU2082_0 s_R2)
    and decr_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ s_R1 accu_UU2081_ accu_UU2082_ accu_R =
      match s_R1 with
      | List_R_nil_R ->
        merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
          Bool_R_false_R (x_UU2081_0::accu_UU2081_)
          (x_UU2082_0::accu_UU2082_) (List_R_cons_R (x_UU2081_0, x_UU2082_0,
          x_R0, accu_UU2081_, accu_UU2082_, accu_R)) stack_UU2081_
          stack_UU2082_ stack_R
      | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
        (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
         | Bool_R_true_R ->
           sortNrec_R
             (merge_sort_push leT_UU2081_ (x_UU2081_0::accu_UU2081_)
               stack_UU2081_)
             (merge_sort_push leT_UU2082_ (x_UU2082_0::accu_UU2082_)
               stack_UU2082_)
             (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
               (x_UU2081_0::accu_UU2081_) (x_UU2082_0::accu_UU2082_)
               (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, accu_UU2081_,
               accu_UU2082_, accu_R)) stack_UU2081_ stack_UU2082_ stack_R)
             y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2
         | Bool_R_false_R ->
           decr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2 (x_UU2081_0::accu_UU2081_)
             (x_UU2082_0::accu_UU2082_) (List_R_cons_R (x_UU2081_0,
             x_UU2082_0, x_R0, accu_UU2081_, accu_UU2082_, accu_R)))
    in sortNrec_R [] [] List_R_nil_R x_UU2081_ x_UU2082_ x_R s_UU2081_
         s_UU2082_ s_R0

  (** val sort1_stable : StableSort.coq_function **)

  let sort1_stable =
    { StableSort.apply = (fun _ -> sort1); StableSort.coq_function__1 =
      (fun _ _ _ -> sort1_R); StableSort.coq_function__2 = (fun _ -> sort1P) }

  (** val sort2_stable : StableSort.coq_function **)

  let sort2_stable =
    { StableSort.apply = (fun _ -> sort2); StableSort.coq_function__1 =
      (fun _ _ _ -> sort2_R); StableSort.coq_function__2 = (fun _ -> sort2P) }

  (** val sort3_stable : StableSort.coq_function **)

  let sort3_stable =
    { StableSort.apply = (fun _ -> sort3); StableSort.coq_function__1 =
      (fun _ _ _ -> sort3_R); StableSort.coq_function__2 = (fun _ -> sort3P) }

  (** val sortN_stable : StableSort.coq_function **)

  let sortN_stable =
    { StableSort.apply = (fun _ -> sortN); StableSort.coq_function__1 =
      (fun _ _ _ -> sortN_R); StableSort.coq_function__2 = (fun _ -> sortNP) }
 end

module CBV = CBV_(Revmerge)

module CBVAcc = CBV_(RevmergeAcc)
