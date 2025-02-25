module NaiveTopDown : sig
  val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module NaiveBottomUp : sig
  val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module TopDown : sig
  val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module BottomUp : sig
  val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module NTRStack : sig
  val sort3 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sortN : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sort3N : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module NTRStack_ : sig
  val sort3 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sortN : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sort3N : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module TRMCStack : sig
  val sort3 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sortN : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sort3N : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module TRMCStack_ : sig
  val sort3 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sortN : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sort3N : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module TRStack : sig
  val sort3 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sortN : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sort3N : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module TRStack_ : sig
  val sort3 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sortN : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
  val sort3N : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end

module StdlibSort : sig
  val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list
end
