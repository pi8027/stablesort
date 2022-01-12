module MergesortCoqCbn where

import qualified Prelude

type Pred t = t -> Prelude.Bool

type Rel t = t -> Pred t

catrev :: (([]) a1) -> (([]) a1) -> ([]) a1
catrev s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) x s1' -> catrev s1' ((:) x s2)}

merge :: (Rel a1) -> (([]) a1) -> (([]) a1) -> ([]) a1
merge leT xs ys =
  case xs of {
   ([]) -> ys;
   (:) x xs' ->
    let {
     merge' ys0 =
       case ys0 of {
        ([]) -> xs;
        (:) y ys' ->
         case leT x y of {
          Prelude.True -> (:) x (merge leT xs' ys0);
          Prelude.False -> (:) y (merge' ys')}}}
    in merge' ys}

merge_sort_push :: (Rel a1) -> (([]) a1) -> (([]) (([]) a1)) -> ([])
                   (([]) a1)
merge_sort_push leT s stack =
  case stack of {
   ([]) -> (:) s stack;
   (:) s' stack' ->
    case s' of {
     ([]) -> (:) s stack';
     (:) _ _ -> (:) ([]) (merge_sort_push leT (merge leT s' s) stack')}}

merge_sort_pop :: (Rel a1) -> (([]) a1) -> (([]) (([]) a1)) -> ([]) a1
merge_sort_pop leT s1 stack =
  case stack of {
   ([]) -> s1;
   (:) s2 stack' -> merge_sort_pop leT (merge leT s2 s1) stack'}

sort1rec :: (Rel a1) -> (([]) (([]) a1)) -> (([]) a1) -> ([]) a1
sort1rec leT stack s =
  case s of {
   ([]) -> merge_sort_pop leT ([]) stack;
   (:) x s0 -> sort1rec leT (merge_sort_push leT ((:) x ([])) stack) s0}

sort1 :: (Rel a1) -> (([]) a1) -> ([]) a1
sort1 leT =
  sort1rec leT ([])

sort2rec :: (Rel a1) -> (([]) (([]) a1)) -> (([]) a1) -> ([]) a1
sort2rec leT stack s =
  case s of {
   ([]) -> merge_sort_pop leT s stack;
   (:) x1 l ->
    case l of {
     ([]) -> merge_sort_pop leT s stack;
     (:) x2 s' ->
      sort2rec leT
        (merge_sort_push leT
          (case leT x1 x2 of {
            Prelude.True -> (:) x1 ((:) x2 ([]));
            Prelude.False -> (:) x2 ((:) x1 ([]))}) stack) s'}}

sort2 :: (Rel a1) -> (([]) a1) -> ([]) a1
sort2 leT =
  sort2rec leT ([])

sort3rec :: (Rel a1) -> (([]) (([]) a1)) -> (([]) a1) -> ([]) a1
sort3rec leT stack s =
  case s of {
   ([]) -> merge_sort_pop leT s stack;
   (:) x1 l ->
    case l of {
     ([]) -> merge_sort_pop leT s stack;
     (:) x2 l0 ->
      case l0 of {
       ([]) ->
        merge_sort_pop leT
          (case leT x1 x2 of {
            Prelude.True -> s;
            Prelude.False -> (:) x2 ((:) x1 ([]))}) stack;
       (:) x3 s' ->
        sort3rec leT
          (merge_sort_push leT
            (case leT x1 x2 of {
              Prelude.True ->
               case leT x2 x3 of {
                Prelude.True -> (:) x1 ((:) x2 ((:) x3 ([])));
                Prelude.False ->
                 case leT x1 x3 of {
                  Prelude.True -> (:) x1 ((:) x3 ((:) x2 ([])));
                  Prelude.False -> (:) x3 ((:) x1 ((:) x2 ([])))}};
              Prelude.False ->
               case leT x1 x3 of {
                Prelude.True -> (:) x2 ((:) x1 ((:) x3 ([])));
                Prelude.False ->
                 case leT x2 x3 of {
                  Prelude.True -> (:) x2 ((:) x3 ((:) x1 ([])));
                  Prelude.False -> (:) x3 ((:) x2 ((:) x1 ([])))}}}) stack)
          s'}}}

sort3 :: (Rel a1) -> (([]) a1) -> ([]) a1
sort3 leT =
  sort3rec leT ([])

sortNrec :: (Rel a1) -> (([]) (([]) a1)) -> a1 -> (([]) a1) -> ([]) a1
sortNrec leT =
  let {
   sortNrec0 stack x s =
     case s of {
      ([]) -> merge_sort_pop leT ((:) x ([])) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr stack y s0 ((:) x ([]));
        Prelude.False -> decr stack y s0 ((:) x ([]))}};
   incr stack x s accu =
     case s of {
      ([]) -> merge_sort_pop leT (catrev accu ((:) x ([]))) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr stack y s0 ((:) x accu);
        Prelude.False ->
         sortNrec0 (merge_sort_push leT (catrev accu ((:) x ([]))) stack) y
           s0}};
   decr stack x s accu =
     case s of {
      ([]) -> merge_sort_pop leT ((:) x accu) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True ->
         sortNrec0 (merge_sort_push leT ((:) x accu) stack) y s0;
        Prelude.False -> decr stack y s0 ((:) x accu)}}}
  in sortNrec0

sortN :: (Rel a1) -> (([]) a1) -> ([]) a1
sortN leT s =
  case s of {
   ([]) -> ([]);
   (:) x s0 -> sortNrec leT ([]) x s0}

