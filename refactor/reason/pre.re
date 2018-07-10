open Absyn;
open List;
open Prelude;
open Prelude;
open Env;
open Lazy;

module Pre = {
  module A = Absyn0;
  module B = Absyn1;

  let rec comb = (ll) =>
    switch ll {
    | [] => []
    | [xs] => map((x) => [x], xs)
    | [xs, ...lls] =>
      let ll' = comb(lls);
      flatten(map((x) => map((l) => [x, ...l], ll'), xs));
    };

  let rec permute = (l) =>
    switch l {
    | [] => []
    | [x] => [[x]]
    | _ =>
      let perm = (h, x, t) => map((l) => [x, ...l], permute(h @ t));
      let rec expl = (l, h) =>
        switch l {
        | [] => []
        | [x, ...xs] => expl(xs, [x, ...h]) @ perm(h, x, xs)
        };
      expl(l, []);
    };
  let arrange = (mseq) => {
    let rec proj = (mseq, mseq') =>
      switch mseq {
      | [] => []
      | [Former(_), ...l] => [surely_former(hd(mseq')), ...proj(l, tl(mseq'))]
      | [Latter(a), ...l] => [a, ...proj(l, mseq')]
      };
    switch (permute(filter(is_former, mseq))) {
    | [] => [proj(mseq, [])]
    | mseqs' => map(proj(mseq), mseqs')
    };
  };

  let pre = (decls) => {
    let rec declare = (env, decls) => {
      let f = ((decl, _)) =>
        switch decl {
        | [@implicit_arity] A.Bind(_, sym, p) => (sym, p)
        | A.Import(_) => raise(Unexpected("import not supported"))
        };

      Env.bind(env, map(f, decls));
    }
    and pre_atom = (env, (a, _)) =>
      switch a {
      | A.Terminal(A.Epsilon) => [Latter(B.Terminal(B.Epsilon))]
      | A.Terminal(A.Concat) => [Latter(B.Terminal(B.Concat))]
      | A.Terminal(A.Capitalize) => [Latter(B.Terminal(B.Capitalize))]
      | A.Terminal(A.Term(sym)) => [Latter(B.Terminal(B.Term(sym)))]
      | [@implicit_arity] A.Sel(a', lbo) =>
        let f = (ma) =>
          switch ma {
          | Former(a) => Former([@implicit_arity] B.Sel(a, lbo))
          | Latter(a) => Latter([@implicit_arity] B.Sel(a, lbo))
          };
        map(f, pre_atom(env, a'));
      | A.Lock(u)
      | A.Fold(u) =>
        switch u {
        | A.NonTerm(path) => [Latter(B.NonTerm(path))]
        | [@implicit_arity] A.Sub(m, decls, p) =>
          let env' = declare(env, decls);
          let sub' = [@implicit_arity] B.Sub(pre_decls(env', decls), pre_prod(env', p));
          switch m {
          | A.Mob => [Former(sub')]
          | A.Std => [Latter(sub')]
          };
        }
      | A.Unfold(u) =>
        switch u {
        | A.NonTerm(path) =>
          let B.Prod(seqs) = pre_prod(env, Env.lookup(env, path));
          map((seq) => Latter([@implicit_arity] B.Sub([], B.Prod([seq]))), seqs);
        | [@implicit_arity] A.Sub(m, decls, p) =>
          let env' = declare(env, decls);
          let sub' = (seq) => [@implicit_arity] B.Sub(pre_decls(env', decls), B.Prod([seq]));
          let B.Prod(seqs) = pre_prod(env', p);
          switch m {
          | A.Mob => map((seq) => Former(sub'(seq)), seqs)
          | A.Std => map((seq) => Latter(sub'(seq)), seqs)
          };
        }
      }
    and pre_seq = (env, ([@implicit_arity] A.Seq(lbo, atoms), _)) => {
      let mseqs = comb(map(pre_atom(env), atoms));
      let new_seqs = (lbo, seqs) => map((seq) => [@implicit_arity] B.Seq(lbo, seq, ref(0)), seqs);
      let seqs =
        map((mseq) => [[@implicit_arity] B.Sub([], B.Prod(new_seqs(None, arrange(mseq))))], mseqs);
      new_seqs(lbo, seqs);
    }
    and pre_prod = (env, (A.Prod(seqs), _)) => B.Prod(flatten(map(pre_seq(env), seqs)))
    and pre_decls = (env, decls) => {
      let f = ((decl, _)) =>
        switch decl {
        | [@implicit_arity] A.Bind(A.Def, sym, p) =>
          [@implicit_arity] B.Bind(B.Def, sym, pre_prod(env, p))
        | [@implicit_arity] A.Bind(A.Assign, sym, p) =>
          [@implicit_arity] B.Bind(B.Assign, sym, pre_prod(env, p))
        | A.Import(_) => raise(Unexpected("pre.ml: pre_decl"))
        };
      map(f, decls);
    };
    pre_decls(declare(Env.empty, decls), decls);
  };
};
