
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
  type 't tree =
  | Coq_branch_tree of bool * 't tree * 't tree
  | Coq_leaf_tree of Equality.sort * 't list

  (** val empty_tree : 'a1 rel -> 'a1 tree **)

  let empty_tree _ =
    Coq_leaf_tree ((Obj.magic false), [])

  (** val flatten_tree : 'a1 rel -> 'a1 tree -> 'a1 list **)

  let rec flatten_tree leT = function
  | Coq_branch_tree (_, l, r) -> cat (flatten_tree leT l) (flatten_tree leT r)
  | Coq_leaf_tree (_, s) -> s

  (** val sort_tree : 'a1 rel -> 'a1 tree -> 'a1 list **)

  let rec sort_tree leT = function
  | Coq_branch_tree (b, l, r) ->
    if b
    then merge leT (sort_tree leT l) (sort_tree leT r)
    else List.rev
           (merge (fun x y -> leT y x) (List.rev (sort_tree leT r))
             (List.rev (sort_tree leT l)))
  | Coq_leaf_tree (b, s) -> if Obj.magic b then s else List.rev s

  type 't tree_nil_spec =
  | TreeNil
  | TreeNotNil

  (** val tree_nilP : 'a1 rel -> 'a1 tree -> 'a1 tree_nil_spec **)

  let tree_nilP leT t =
    match nilP (sort_tree leT t) with
    | ReflectT ->
      (match nilP (flatten_tree leT t) with
       | ReflectT ->
         ssr_have __ (fun _ _ -> ssr_have __ (fun _ _ -> TreeNil)) __ __
       | ReflectF -> assert false (* absurd case *))
    | ReflectF ->
      (match nilP (flatten_tree leT t) with
       | ReflectT -> assert false (* absurd case *)
       | ReflectF -> TreeNotNil)

  type sort_ty_R =
    __ -> __ -> __ -> __ rel -> __ rel -> (__, __, __) rel_R -> __ list -> __
    list -> (__, __, __) list_R -> (__, __, __) list_R

  type interface = { sort_fun : (__ -> __ rel -> __ list -> __ list);
                     interface__1 : sort_ty_R;
                     interface__2 : (__ -> __ rel -> __ list -> __ tree sig2) }
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
      if leT x y
      then ascending0 stack (x::[]) y s0
      else descending0 stack (x::[]) y s0
    and ascending0 stack acc x = function
    | [] -> merge_sort_pop leT (List.rev_append acc (x::[])) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::acc) y s0
      else sortNrec0
             (merge_sort_push leT (List.rev_append acc (x::[])) stack) y s0
    and descending0 stack acc x = function
    | [] -> merge_sort_pop leT (x::acc) stack
    | y::s0 ->
      if leT x y
      then sortNrec0 (merge_sort_push leT (x::acc) stack) y s0
      else descending0 stack (x::acc) y s0
    in sortNrec0

  (** val ascending :
      'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 list **)

  let ascending leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT (x::[]) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::[]) y s0
      else descending0 stack (x::[]) y s0
    and ascending0 stack acc x = function
    | [] -> merge_sort_pop leT (List.rev_append acc (x::[])) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::acc) y s0
      else sortNrec0
             (merge_sort_push leT (List.rev_append acc (x::[])) stack) y s0
    and descending0 stack acc x = function
    | [] -> merge_sort_pop leT (x::acc) stack
    | y::s0 ->
      if leT x y
      then sortNrec0 (merge_sort_push leT (x::acc) stack) y s0
      else descending0 stack (x::acc) y s0
    in ascending0

  (** val descending :
      'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 list **)

  let descending leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT (x::[]) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::[]) y s0
      else descending0 stack (x::[]) y s0
    and ascending0 stack acc x = function
    | [] -> merge_sort_pop leT (List.rev_append acc (x::[])) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::acc) y s0
      else sortNrec0
             (merge_sort_push leT (List.rev_append acc (x::[])) stack) y s0
    and descending0 stack acc x = function
    | [] -> merge_sort_pop leT (x::acc) stack
    | y::s0 ->
      if leT x y
      then sortNrec0 (merge_sort_push leT (x::acc) stack) y s0
      else descending0 stack (x::acc) y s0
    in descending0

  (** val sortN : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sortN leT = function
  | [] -> []
  | x::s0 -> sortNrec leT [] x s0

  (** val merge_sort_pushP :
      'a1 rel -> 'a1 StableSort.tree -> 'a1 StableSort.tree list -> 'a1
      StableSort.tree list sig2 **)

  let rec merge_sort_pushP leT t = function
  | [] -> t::[]
  | y::l ->
    (match StableSort.tree_nilP leT y with
     | StableSort.TreeNil -> t::l
     | StableSort.TreeNotNil ->
       ssr_have
         (merge_sort_pushP leT (StableSort.Coq_branch_tree (true, y, t)) l)
         (fun __top_assumption_ ->
         (StableSort.empty_tree leT)::__top_assumption_))

  (** val merge_sort_popP :
      'a1 rel -> 'a1 StableSort.tree -> 'a1 StableSort.tree list -> 'a1
      StableSort.tree sig2 **)

  let rec merge_sort_popP leT t = function
  | [] -> t
  | y::l ->
    ssr_have
      (merge_sort_popP leT (StableSort.Coq_branch_tree (true, y, t)) l)
      (fun __top_assumption_ -> __top_assumption_)

  (** val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.tree sig2 **)

  let sort1P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec f l stack =
          match l with
          | [] -> merge_sort_popP leT (StableSort.empty_tree leT) stack
          | y::l0 ->
            f l0
              (merge_sort_pushP leT (StableSort.Coq_leaf_tree
                ((Obj.magic true), (y::[]))) stack)
        in f s []))

  (** val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.tree sig2 **)

  let sort2P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec iHs stack = function
        | [] ->
          merge_sort_popP leT (StableSort.Coq_leaf_tree ((Obj.magic true),
            [])) stack
        | x::x0 ->
          (match x0 with
           | [] ->
             merge_sort_popP leT (StableSort.Coq_leaf_tree ((Obj.magic true),
               (x::[]))) stack
           | x1::x2 ->
             iHs
               (merge_sort_pushP leT (StableSort.Coq_leaf_tree
                 ((Obj.magic leT x x1), (x::(x1::[])))) stack) x2)
        in iHs [] s))

  (** val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.tree sig2 **)

  let sort3P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        ssr_have __ (fun _ ->
          let rec iHs stack = function
          | [] ->
            merge_sort_popP leT (StableSort.Coq_leaf_tree ((Obj.magic true),
              [])) stack
          | x::x0 ->
            (match x0 with
             | [] ->
               merge_sort_popP leT (StableSort.Coq_leaf_tree
                 ((Obj.magic true), (x::[]))) stack
             | x1::x2 ->
               (match x2 with
                | [] ->
                  merge_sort_popP leT (StableSort.Coq_leaf_tree
                    ((Obj.magic leT x x1), (x::(x1::[])))) stack
                | x3::x4 ->
                  ssr_have __ (fun _ _ ->
                    iHs
                      (merge_sort_pushP leT (StableSort.Coq_branch_tree
                        (false, (StableSort.Coq_leaf_tree
                        ((Obj.magic leT x x1), (x::(x1::[])))),
                        (StableSort.Coq_leaf_tree ((Obj.magic true),
                        (x3::[]))))) stack) x4) __))
          in iHs [] s)))

  (** val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.tree sig2 **)

  let sortNP leT = function
  | [] -> StableSort.empty_tree leT
  | x::x0 ->
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec iHs stack x1 = function
        | [] ->
          merge_sort_popP leT (StableSort.Coq_leaf_tree ((Obj.magic true),
            (x1::[]))) stack
        | x2::x3 ->
          ssr_have __
            (ssr_have __ (fun _ _ ->
              let rec f l ord x4 acc =
                match l with
                | [] ->
                  merge_sort_popP leT (StableSort.Coq_leaf_tree
                    ((Obj.magic ord), (List.rev (x4::acc)))) stack
                | y::l0 ->
                  if ord
                  then (match boolP (leT x4 y) with
                        | AltTrue ->
                          ssr_have __ (fun _ -> f l0 true y (x4::acc))
                        | AltFalse ->
                          iHs
                            (merge_sort_pushP leT (StableSort.Coq_leaf_tree
                              ((Obj.magic true), (List.rev (x4::acc)))) stack)
                            y l0)
                  else (match boolP (leT x4 y) with
                        | AltTrue ->
                          iHs
                            (merge_sort_pushP leT (StableSort.Coq_leaf_tree
                              ((Obj.magic false), (List.rev (x4::acc))))
                              stack) y l0
                        | AltFalse ->
                          ssr_have __ (fun _ -> f l0 false y (x4::acc)))
              in f x3 (leT x1 x2) x2 (x1::[])))
        in iHs [] x x0))

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
         ascending_R stack_UU2081_ stack_UU2082_ stack_R (x_UU2081_0::[])
           (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [],
           [], List_R_nil_R)) y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0
           s_R2
       | Bool_R_false_R ->
         descending_R stack_UU2081_ stack_UU2082_ stack_R (x_UU2081_0::[])
           (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [],
           [], List_R_nil_R)) y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0
           s_R2)
    and ascending_R stack_UU2081_ stack_UU2082_ stack_R acc_UU2081_ acc_UU2082_ acc_R x_UU2081_0 x_UU2082_0 x_R0 _ _ = function
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R
        (List.rev_append acc_UU2081_ (x_UU2081_0::[]))
        (List.rev_append acc_UU2082_ (x_UU2082_0::[]))
        (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
           match s1_R with
           | List_R_nil_R -> s2_R
           | List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s1'_UU2081_,
                            s1'_UU2082_, s1'_R) ->
             catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R (x_UU2081_1::s2_UU2081_)
               (x_UU2082_1::s2_UU2082_) (List_R_cons_R (x_UU2081_1,
               x_UU2082_1, x_R1, s2_UU2081_, s2_UU2082_, s2_R))
         in catrev_R acc_UU2081_ acc_UU2082_ acc_R (x_UU2081_0::[])
              (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0,
              [], [], List_R_nil_R))) stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
      (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
       | Bool_R_true_R ->
         ascending_R stack_UU2081_ stack_UU2082_ stack_R
           (x_UU2081_0::acc_UU2081_) (x_UU2082_0::acc_UU2082_) (List_R_cons_R
           (x_UU2081_0, x_UU2082_0, x_R0, acc_UU2081_, acc_UU2082_, acc_R))
           y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2
       | Bool_R_false_R ->
         sortNrec_R
           (merge_sort_push leT_UU2081_
             (List.rev_append acc_UU2081_ (x_UU2081_0::[])) stack_UU2081_)
           (merge_sort_push leT_UU2082_
             (List.rev_append acc_UU2082_ (x_UU2082_0::[])) stack_UU2082_)
           (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
             (List.rev_append acc_UU2081_ (x_UU2081_0::[]))
             (List.rev_append acc_UU2082_ (x_UU2082_0::[]))
             (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                match s1_R with
                | List_R_nil_R -> s2_R
                | List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s1'_UU2081_,
                                 s1'_UU2082_, s1'_R) ->
                  catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                    (x_UU2081_1::s2_UU2081_) (x_UU2082_1::s2_UU2082_)
                    (List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s2_UU2081_,
                    s2_UU2082_, s2_R))
              in catrev_R acc_UU2081_ acc_UU2082_ acc_R (x_UU2081_0::[])
                   (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0,
                   x_R0, [], [], List_R_nil_R))) stack_UU2081_ stack_UU2082_
             stack_R) y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2)
    and descending_R stack_UU2081_ stack_UU2082_ stack_R acc_UU2081_ acc_UU2082_ acc_R x_UU2081_0 x_UU2082_0 x_R0 _ _ = function
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R
        (x_UU2081_0::acc_UU2081_) (x_UU2082_0::acc_UU2082_) (List_R_cons_R
        (x_UU2081_0, x_UU2082_0, x_R0, acc_UU2081_, acc_UU2082_, acc_R))
        stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
      (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
       | Bool_R_true_R ->
         sortNrec_R
           (merge_sort_push leT_UU2081_ (x_UU2081_0::acc_UU2081_)
             stack_UU2081_)
           (merge_sort_push leT_UU2082_ (x_UU2082_0::acc_UU2082_)
             stack_UU2082_)
           (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
             (x_UU2081_0::acc_UU2081_) (x_UU2082_0::acc_UU2082_)
             (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, acc_UU2081_,
             acc_UU2082_, acc_R)) stack_UU2081_ stack_UU2082_ stack_R)
           y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2
       | Bool_R_false_R ->
         descending_R stack_UU2081_ stack_UU2082_ stack_R
           (x_UU2081_0::acc_UU2081_) (x_UU2082_0::acc_UU2082_) (List_R_cons_R
           (x_UU2081_0, x_UU2082_0, x_R0, acc_UU2081_, acc_UU2082_, acc_R))
           y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2)
    in sortNrec_R [] [] List_R_nil_R x_UU2081_ x_UU2082_ x_R s_UU2081_
         s_UU2082_ s_R0

  (** val sort1_stable : StableSort.interface **)

  let sort1_stable =
    { StableSort.sort_fun = (fun _ -> sort1); StableSort.interface__1 =
      (fun _ _ _ -> sort1_R); StableSort.interface__2 = (fun _ -> sort1P) }

  (** val sort2_stable : StableSort.interface **)

  let sort2_stable =
    { StableSort.sort_fun = (fun _ -> sort2); StableSort.interface__1 =
      (fun _ _ _ -> sort2_R); StableSort.interface__2 = (fun _ -> sort2P) }

  (** val sort3_stable : StableSort.interface **)

  let sort3_stable =
    { StableSort.sort_fun = (fun _ -> sort3); StableSort.interface__1 =
      (fun _ _ _ -> sort3_R); StableSort.interface__2 = (fun _ -> sort3P) }

  (** val sortN_stable : StableSort.interface **)

  let sortN_stable =
    { StableSort.sort_fun = (fun _ -> sortN); StableSort.interface__1 =
      (fun _ _ _ -> sortN_R); StableSort.interface__2 = (fun _ -> sortNP) }
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

  let rec sort2rec leT ss s = match s with
  | [] -> merge_sort_pop leT false s ss
  | x1::l ->
    (match l with
     | [] -> merge_sort_pop leT false s ss
     | x2::s' ->
       sort2rec leT
         (merge_sort_push leT
           (if leT x1 x2 then x1::(x2::[]) else x2::(x1::[])) ss) s')

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
      if leT x y
      then ascending0 stack (x::[]) y s0
      else descending0 stack (x::[]) y s0
    and ascending0 stack acc x = function
    | [] -> merge_sort_pop leT false (List.rev_append acc (x::[])) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::acc) y s0
      else sortNrec0
             (merge_sort_push leT (List.rev_append acc (x::[])) stack) y s0
    and descending0 stack acc x = function
    | [] -> merge_sort_pop leT false (x::acc) stack
    | y::s0 ->
      if leT x y
      then sortNrec0 (merge_sort_push leT (x::acc) stack) y s0
      else descending0 stack (x::acc) y s0
    in sortNrec0

  (** val ascending :
      'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 list **)

  let ascending leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT false (x::[]) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::[]) y s0
      else descending0 stack (x::[]) y s0
    and ascending0 stack acc x = function
    | [] -> merge_sort_pop leT false (List.rev_append acc (x::[])) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::acc) y s0
      else sortNrec0
             (merge_sort_push leT (List.rev_append acc (x::[])) stack) y s0
    and descending0 stack acc x = function
    | [] -> merge_sort_pop leT false (x::acc) stack
    | y::s0 ->
      if leT x y
      then sortNrec0 (merge_sort_push leT (x::acc) stack) y s0
      else descending0 stack (x::acc) y s0
    in ascending0

  (** val descending :
      'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 list **)

  let descending leT =
    let rec sortNrec0 stack x = function
    | [] -> merge_sort_pop leT false (x::[]) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::[]) y s0
      else descending0 stack (x::[]) y s0
    and ascending0 stack acc x = function
    | [] -> merge_sort_pop leT false (List.rev_append acc (x::[])) stack
    | y::s0 ->
      if leT x y
      then ascending0 stack (x::acc) y s0
      else sortNrec0
             (merge_sort_push leT (List.rev_append acc (x::[])) stack) y s0
    and descending0 stack acc x = function
    | [] -> merge_sort_pop leT false (x::acc) stack
    | y::s0 ->
      if leT x y
      then sortNrec0 (merge_sort_push leT (x::acc) stack) y s0
      else descending0 stack (x::acc) y s0
    in descending0

  (** val sortN : 'a1 rel -> 'a1 list -> 'a1 list **)

  let sortN leT = function
  | [] -> []
  | x::s0 -> sortNrec leT [] x s0

  (** val merge_sort_pushP :
      'a1 rel -> 'a1 StableSort.tree -> 'a1 StableSort.tree list -> 'a1
      StableSort.tree list sig2 **)

  let rec merge_sort_pushP leT t = function
  | [] -> t::[]
  | x::x0 ->
    (match x0 with
     | [] ->
       ssr_have (fun _ -> nilP) (fun __top_assumption_ ->
         match __top_assumption_ __ (StableSort.flatten_tree leT x) with
         | ReflectT -> t::[]
         | ReflectF ->
           (StableSort.empty_tree leT)::((StableSort.Coq_branch_tree (true,
             x, t))::[]))
     | x1::x2 ->
       ssr_have (fun _ -> nilP) (fun __top_assumption_ ->
         match __top_assumption_ __ (StableSort.flatten_tree leT x) with
         | ReflectT -> t::(x1::x2)
         | ReflectF ->
           ssr_have (fun _ -> nilP) (fun __top_assumption_0 ->
             match __top_assumption_0 __ (StableSort.flatten_tree leT x1) with
             | ReflectT ->
               (StableSort.empty_tree leT)::((StableSort.Coq_branch_tree
                 (true, x, t))::x2)
             | ReflectF ->
               ssr_have
                 (merge_sort_pushP leT (StableSort.Coq_branch_tree (false,
                   x1, (StableSort.Coq_branch_tree (true, x, t)))) x2)
                 (fun __top_assumption_1 ->
                 (StableSort.empty_tree leT)::((StableSort.empty_tree leT)::__top_assumption_1)))))

  (** val merge_sort_popP :
      'a1 rel -> bool -> 'a1 StableSort.tree -> 'a1 StableSort.tree list ->
      'a1 StableSort.tree sig2 **)

  let rec merge_sort_popP leT mode t = function
  | [] -> t
  | x::x0 ->
    (match StableSort.tree_nilP leT x with
     | StableSort.TreeNil ->
       (match x0 with
        | [] -> t
        | x1::x2 ->
          (match StableSort.tree_nilP leT x1 with
           | StableSort.TreeNil -> merge_sort_popP leT mode t x2
           | StableSort.TreeNotNil ->
             merge_sort_popP leT mode (StableSort.Coq_branch_tree (mode, x1,
               t)) x2))
     | StableSort.TreeNotNil ->
       merge_sort_popP leT (not mode) (StableSort.Coq_branch_tree
         ((not mode), x, t)) x0)

  (** val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.tree sig2 **)

  let sort1P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec f l stack =
          match l with
          | [] -> merge_sort_popP leT false (StableSort.empty_tree leT) stack
          | y::l0 ->
            f l0
              (merge_sort_pushP leT (StableSort.Coq_leaf_tree
                ((Obj.magic true), (y::[]))) stack)
        in f s []))

  (** val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.tree sig2 **)

  let sort2P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec iHs stack = function
        | [] ->
          merge_sort_popP leT false (StableSort.Coq_leaf_tree
            ((Obj.magic true), [])) stack
        | x::x0 ->
          (match x0 with
           | [] ->
             merge_sort_popP leT false (StableSort.Coq_leaf_tree
               ((Obj.magic true), (x::[]))) stack
           | x1::x2 ->
             iHs
               (merge_sort_pushP leT (StableSort.Coq_leaf_tree
                 ((Obj.magic leT x x1), (x::(x1::[])))) stack) x2)
        in iHs [] s))

  (** val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.tree sig2 **)

  let sort3P leT s =
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        ssr_have __ (fun _ ->
          let rec iHs stack = function
          | [] ->
            merge_sort_popP leT false (StableSort.Coq_leaf_tree
              ((Obj.magic true), [])) stack
          | x::x0 ->
            (match x0 with
             | [] ->
               merge_sort_popP leT false (StableSort.Coq_leaf_tree
                 ((Obj.magic true), (x::[]))) stack
             | x1::x2 ->
               (match x2 with
                | [] ->
                  merge_sort_popP leT false (StableSort.Coq_leaf_tree
                    ((Obj.magic leT x x1), (x::(x1::[])))) stack
                | x3::x4 ->
                  ssr_have __ (fun _ _ ->
                    iHs
                      (merge_sort_pushP leT (StableSort.Coq_branch_tree
                        (false, (StableSort.Coq_leaf_tree
                        ((Obj.magic leT x x1), (x::(x1::[])))),
                        (StableSort.Coq_leaf_tree ((Obj.magic true),
                        (x3::[]))))) stack) x4) __))
          in iHs [] s)))

  (** val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.tree sig2 **)

  let sortNP leT = function
  | [] -> StableSort.empty_tree leT
  | x::x0 ->
    ssr_have __ (fun _ ->
      ssr_have __ (fun _ ->
        let rec iHs stack x1 = function
        | [] ->
          merge_sort_popP leT false (StableSort.Coq_leaf_tree
            ((Obj.magic true), (x1::[]))) stack
        | x2::x3 ->
          ssr_have __
            (ssr_have __ (fun _ _ ->
              let rec f l ord x4 acc =
                match l with
                | [] ->
                  merge_sort_popP leT false (StableSort.Coq_leaf_tree
                    ((Obj.magic ord), (List.rev (x4::acc)))) stack
                | y::l0 ->
                  if ord
                  then (match boolP (leT x4 y) with
                        | AltTrue ->
                          ssr_have __ (fun _ -> f l0 true y (x4::acc))
                        | AltFalse ->
                          iHs
                            (merge_sort_pushP leT (StableSort.Coq_leaf_tree
                              ((Obj.magic true), (List.rev (x4::acc)))) stack)
                            y l0)
                  else (match boolP (leT x4 y) with
                        | AltTrue ->
                          iHs
                            (merge_sort_pushP leT (StableSort.Coq_leaf_tree
                              ((Obj.magic false), (List.rev (x4::acc))))
                              stack) y l0
                        | AltFalse ->
                          ssr_have __ (fun _ -> f l0 false y (x4::acc)))
              in f x3 (leT x1 x2) x2 (x1::[])))
        in iHs [] x x0))

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
                            (M.revmerge (fun x y -> leT_UU2081_ y x)
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
                            (M.revmerge (fun x y -> leT_UU2082_ y x)
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
                        (M.revmerge (fun x y -> leT_UU2081_ y x)
                          (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                          zs_UU2081_) stack_UU2081_1)),
                 ([]::(fix_merge_sort_push_2
                        (M.revmerge (fun x y -> leT_UU2082_ y x)
                          (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                          zs_UU2082_) stack_UU2082_1)), (List_R_cons_R ([],
                 [], List_R_nil_R,
                 (fix_merge_sort_push_1
                   (M.revmerge (fun x y -> leT_UU2081_ y x)
                     (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                     zs_UU2081_) stack_UU2081_1),
                 (fix_merge_sort_push_2
                   (M.revmerge (fun x y -> leT_UU2082_ y x)
                     (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                     zs_UU2082_) stack_UU2082_1),
                 (merge_sort_push_R0
                   (M.revmerge (fun x y -> leT_UU2081_ y x)
                     (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                     zs_UU2081_)
                   (M.revmerge (fun x y -> leT_UU2082_ y x)
                     (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                     zs_UU2082_)
                   (revmerge_R (fun x y -> leT_UU2081_ y x) (fun x y ->
                     leT_UU2082_ y x)
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

  let rec merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R mode_UU2081_ mode_UU2082_ mode_R xs_UU2081_ xs_UU2082_ xs_R _ _ = function
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
          merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R (not mode_UU2081_)
            (not mode_UU2082_)
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
             merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R mode_UU2081_
               mode_UU2082_ mode_R xs_UU2081_ xs_UU2082_ xs_R stack_UU2081_0
               stack_UU2082_0 stack_R1
           | List_R_cons_R (_, _, _, _, _, _) ->
             merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R
               (not mode_UU2081_) (not mode_UU2082_)
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
               stack_UU2081_ stack_UU2082_ stack_R0))
     | List_R_cons_R (_, _, _, _, _, _) ->
       (match mode_R with
        | Bool_R_true_R ->
          merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
            Bool_R_false_R
            (M.revmerge (fun x y -> leT_UU2081_ y x) xs_UU2081_ ys_UU2081_)
            (M.revmerge (fun x y -> leT_UU2082_ y x) xs_UU2082_ ys_UU2082_)
            (revmerge_R (fun x y -> leT_UU2081_ y x) (fun x y ->
              leT_UU2082_ y x)
              (fun x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R ->
              leT_R y_UU2081_ y_UU2082_ y_R x_UU2081_ x_UU2082_ x_R)
              xs_UU2081_ xs_UU2082_ xs_R ys_UU2081_ ys_UU2082_ ys_R)
            stack_UU2081_ stack_UU2082_ stack_R0
        | Bool_R_false_R ->
          merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R true true
            Bool_R_true_R (M.revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
            (M.revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
            (revmerge_R leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_ ys_UU2082_
              ys_R xs_UU2081_ xs_UU2082_ xs_R) stack_UU2081_ stack_UU2082_
            stack_R0))

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
    let rec sort2rec_R ss_UU2081_ ss_UU2082_ ss_R s_UU2081_ s_UU2082_ s_R = match s_R with
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
        Bool_R_false_R s_UU2081_ s_UU2082_ s_R ss_UU2081_ ss_UU2082_ ss_R
    | List_R_cons_R (x1_UU2081_, x1_UU2082_, x1_R, _, _, l_R) ->
      (match l_R with
       | List_R_nil_R ->
         merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
           Bool_R_false_R s_UU2081_ s_UU2082_ s_R ss_UU2081_ ss_UU2082_ ss_R
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
         sort2rec_R (merge_sort_push leT_UU2081_ s1_UU2081_ ss_UU2081_)
           (merge_sort_push leT_UU2082_ s1_UU2082_ ss_UU2082_)
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
             ss_UU2081_ ss_UU2082_ ss_R) s'_UU2081_ s'_UU2082_ s'_R)
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
         ascending_R stack_UU2081_ stack_UU2082_ stack_R (x_UU2081_0::[])
           (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [],
           [], List_R_nil_R)) y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0
           s_R2
       | Bool_R_false_R ->
         descending_R stack_UU2081_ stack_UU2082_ stack_R (x_UU2081_0::[])
           (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, [],
           [], List_R_nil_R)) y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0
           s_R2)
    and ascending_R stack_UU2081_ stack_UU2082_ stack_R acc_UU2081_ acc_UU2082_ acc_R x_UU2081_0 x_UU2082_0 x_R0 _ _ = function
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
        Bool_R_false_R (List.rev_append acc_UU2081_ (x_UU2081_0::[]))
        (List.rev_append acc_UU2082_ (x_UU2082_0::[]))
        (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
           match s1_R with
           | List_R_nil_R -> s2_R
           | List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s1'_UU2081_,
                            s1'_UU2082_, s1'_R) ->
             catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R (x_UU2081_1::s2_UU2081_)
               (x_UU2082_1::s2_UU2082_) (List_R_cons_R (x_UU2081_1,
               x_UU2082_1, x_R1, s2_UU2081_, s2_UU2082_, s2_R))
         in catrev_R acc_UU2081_ acc_UU2082_ acc_R (x_UU2081_0::[])
              (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0,
              [], [], List_R_nil_R))) stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
      (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
       | Bool_R_true_R ->
         ascending_R stack_UU2081_ stack_UU2082_ stack_R
           (x_UU2081_0::acc_UU2081_) (x_UU2082_0::acc_UU2082_) (List_R_cons_R
           (x_UU2081_0, x_UU2082_0, x_R0, acc_UU2081_, acc_UU2082_, acc_R))
           y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2
       | Bool_R_false_R ->
         sortNrec_R
           (merge_sort_push leT_UU2081_
             (List.rev_append acc_UU2081_ (x_UU2081_0::[])) stack_UU2081_)
           (merge_sort_push leT_UU2082_
             (List.rev_append acc_UU2082_ (x_UU2082_0::[])) stack_UU2082_)
           (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
             (List.rev_append acc_UU2081_ (x_UU2081_0::[]))
             (List.rev_append acc_UU2082_ (x_UU2082_0::[]))
             (let rec catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                match s1_R with
                | List_R_nil_R -> s2_R
                | List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s1'_UU2081_,
                                 s1'_UU2082_, s1'_R) ->
                  catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R
                    (x_UU2081_1::s2_UU2081_) (x_UU2082_1::s2_UU2082_)
                    (List_R_cons_R (x_UU2081_1, x_UU2082_1, x_R1, s2_UU2081_,
                    s2_UU2082_, s2_R))
              in catrev_R acc_UU2081_ acc_UU2082_ acc_R (x_UU2081_0::[])
                   (x_UU2082_0::[]) (List_R_cons_R (x_UU2081_0, x_UU2082_0,
                   x_R0, [], [], List_R_nil_R))) stack_UU2081_ stack_UU2082_
             stack_R) y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2)
    and descending_R stack_UU2081_ stack_UU2082_ stack_R acc_UU2081_ acc_UU2082_ acc_R x_UU2081_0 x_UU2082_0 x_R0 _ _ = function
    | List_R_nil_R ->
      merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R false false
        Bool_R_false_R (x_UU2081_0::acc_UU2081_) (x_UU2082_0::acc_UU2082_)
        (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, acc_UU2081_,
        acc_UU2082_, acc_R)) stack_UU2081_ stack_UU2082_ stack_R
    | List_R_cons_R (y_UU2081_, y_UU2082_, y_R, s_UU2081_0, s_UU2082_0, s_R2) ->
      (match leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R with
       | Bool_R_true_R ->
         sortNrec_R
           (merge_sort_push leT_UU2081_ (x_UU2081_0::acc_UU2081_)
             stack_UU2081_)
           (merge_sort_push leT_UU2082_ (x_UU2082_0::acc_UU2082_)
             stack_UU2082_)
           (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
             (x_UU2081_0::acc_UU2081_) (x_UU2082_0::acc_UU2082_)
             (List_R_cons_R (x_UU2081_0, x_UU2082_0, x_R0, acc_UU2081_,
             acc_UU2082_, acc_R)) stack_UU2081_ stack_UU2082_ stack_R)
           y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2
       | Bool_R_false_R ->
         descending_R stack_UU2081_ stack_UU2082_ stack_R
           (x_UU2081_0::acc_UU2081_) (x_UU2082_0::acc_UU2082_) (List_R_cons_R
           (x_UU2081_0, x_UU2082_0, x_R0, acc_UU2081_, acc_UU2082_, acc_R))
           y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2)
    in sortNrec_R [] [] List_R_nil_R x_UU2081_ x_UU2082_ x_R s_UU2081_
         s_UU2082_ s_R0

  (** val sort1_stable : StableSort.interface **)

  let sort1_stable =
    { StableSort.sort_fun = (fun _ -> sort1); StableSort.interface__1 =
      (fun _ _ _ -> sort1_R); StableSort.interface__2 = (fun _ -> sort1P) }

  (** val sort2_stable : StableSort.interface **)

  let sort2_stable =
    { StableSort.sort_fun = (fun _ -> sort2); StableSort.interface__1 =
      (fun _ _ _ -> sort2_R); StableSort.interface__2 = (fun _ -> sort2P) }

  (** val sort3_stable : StableSort.interface **)

  let sort3_stable =
    { StableSort.sort_fun = (fun _ -> sort3); StableSort.interface__1 =
      (fun _ _ _ -> sort3_R); StableSort.interface__2 = (fun _ -> sort3P) }

  (** val sortN_stable : StableSort.interface **)

  let sortN_stable =
    { StableSort.sort_fun = (fun _ -> sortN); StableSort.interface__1 =
      (fun _ _ _ -> sortN_R); StableSort.interface__2 = (fun _ -> sortNP) }
 end

module CBV = CBV_(Revmerge)

module CBVAcc = CBV_(RevmergeAcc)
