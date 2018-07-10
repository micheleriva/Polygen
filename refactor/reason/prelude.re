module Prelude = {

  exception Unexpected(string);
  
  type either('a, 'b) =
    | Former('a)
    | Latter('b);
  let is_former = (e) =>
    switch e {
    | Former(_) => true
    | _ => false
    };
  let is_latter = (e) => ! is_former(e);
  let surely_former = (e) =>
    switch e {
    | Former(x) => x
    | _ => raise(Unexpected("prelude.ml: surely_former"))
    };
  let surely_latter = (e) =>
    switch e {
    | Latter(x) => x
    | _ => raise(Unexpected("prelude.ml: surely_latter"))
    };
  
  type symbol = string;
  
  let before = (a, b) => {
    b;
    a;
  };
  
  let ($) = (f, g, x) => f(g(x));
  
  let occurs = (l, x) => List.exists((==)(x), l);
  
  let disjoint = ((==), l1, l2) => List.for_all((x) => ! List.exists((==)(x), l1), l2);
  
  let rec flatten_strings = (spc, l) =>
    switch l {
    | [] => ""
    | [s] => s
    | [s, ...l'] => s ++ spc ++ flatten_strings(spc, l')
    };
  let mappen_strings = (f, spc, l) => flatten_strings(spc, List.map(f, l));
  
  let surely_assoc = (x, l) =>
    try (List.assoc(x, l)) {
    | Not_found => raise(Unexpected("prelude.ml: surely_assoc"))
    };
  
  module type CacheKey = {type t; let (==): (t, t) => bool;};
  module Cache:
    (Key: CacheKey) =>
    {type t('v); let init: unit => t('v); let load: (t('v), Key.t, Lazy.t('v)) => 'v;} =
    (Key: CacheKey) => {
      module HashKey: Hashtbl.HashedType with type t = Key.t = {
        type t = Key.t;
        let equal = Key.(==);
        let hash = Hashtbl.hash;
      };
      module Tbl = Hashtbl.Make(HashKey);
      type t('v) = Tbl.t(option('v));
      let init = () => Tbl.create(100);
      let load = (tbl, x, suspension) =>
        try (
          switch (Tbl.find(tbl, x)) {
          | None => Lazy.force(suspension)
          | Some(y) => y
          }
        ) {
        | Not_found =>
          let _ = Tbl.add(tbl, x, None);
          let y = Lazy.force(suspension);
          let _ = Tbl.replace(tbl, x, Some(y));
          y;
        };
    };
  
  module Label: Set.OrderedType with type t = symbol = {
    type t = symbol;
    let compare = (lb1, lb2) => compare(lb1, lb2);
  };
  module LabelSet = {
    include Set.Make(Label);
    let of_labels = (labels) => List.fold_left((lbs, lb) => add(lb, lbs), empty, labels);
    let occurs = mem;
    let pretty = (lbs) => "{" ++ flatten_strings(", ", elements(lbs)) ++ "}";
  };
  
  let mapfst = (f, (a, b)) => (f(a), b);
  let mapsnd = (f, (a, b)) => (a, f(b));
  
  let surely_some = (o) =>
    switch o {
    | Some(x) => x
    | None => raise(Unexpected("prelude.ml: surely_some"))
    };
  
  let tail_segment = (p, l) => {
    let rec recur = (r) =>
      fun
      | [] => []
      | [x, ...xs] => {
          let r' = [x, ...r];
          if (p(x)) {
            r';
          } else {
            recur(r', xs);
          };
        };
    recur([], l);
  };
  
  let rec tab = (f, n) =>
    if (n == 0) {
      [];
    } else {
      let n = n - 1;
      [f(n), ...tab(f, n)];
    };
};
