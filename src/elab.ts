import { Map, List } from "immutable";
import { MCtx, Rule, Tactic, Term, Ty, type TacticState } from "./kernel.ts";
import { type Parser, type ParserDescr, type Syntax } from "./parser.ts";
import type { CoreState } from "./core.ts";

export type NotationDescr =
  | { kind: "atom", val: string }
  | { kind: "term", ty: Ty, prec: number }

export type Notation = {
  name: string,
  descr: NotationDescr[],
};

export function elabTy(stx: Syntax): Ty {
  if (stx.kind !== "node") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
  if (stx.type !== "ty") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
  const arg0 = stx.args[0];
  const arg1 = stx.args[1];
  const arg2 = stx.args[2];

  if (arg0 && arg0.kind === "ident") {
    return { kind: "base", name: arg0.val };
  }

  if (
    arg0 && arg1 && arg2 &&
    arg0.kind === "node" && arg0.type === "ty" &&
    arg1.kind === "atom" && arg1.val === "->" &&
    arg2.kind === "node" && arg2.type === "ty"
  ) {
    return { kind: "arrow", left: elabTy(arg0), right: elabTy(arg2) };
  }

  if (
    arg0 && arg1 && arg2 &&
    arg0.kind === "atom" && arg0.val === "(" &&
    arg1.kind === "node" && arg1.type === "ty" &&
    arg2.kind === "atom" && arg2.val === ")"
  ) {
    return elabTy(arg1);
  }

  throw new Error("unexpected syntax");
}

export function elabTerm(
  stx: Syntax,
  bdepth: number, fdepth: number,
  bvMap: Map<string, number>, fvMap: Map<string, number>,
  notations: Notation[]
): Term {
  if (stx.kind !== "node") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
  if (stx.type !== "term") throw new Error(`unreachable: ${JSON.stringify(stx)}`);

  const [arg0, arg1, arg2, arg3, arg4, arg5, ..._args] = stx.args;
  
  if (arg0 && arg0.kind === "ident") {
    const i = bvMap.get(arg0.val, null);
    if (i !== null) return { kind: "bvar", idx: bdepth - (i+1) };
    const j = fvMap.get(arg0.val, null);
    if (j !== null) return { kind: "fvar", idx: fdepth - (j+1) };
    return { kind: "const", name: arg0.val };
  }

  if (
    arg0 && arg1 &&
    arg0.kind === "node" && arg0.type === "term" &&
    arg1.kind === "node" && arg1.type === "term"
  ) {
    const ta = elabTerm(arg0, bdepth, fdepth, bvMap, fvMap, notations);
    const tb = elabTerm(arg1, bdepth, fdepth, bvMap, fvMap, notations);
    return { kind: "app", fn: ta, arg: tb };
  }

  if (
    arg0 && arg1 && arg2 && arg3 && arg4 && arg5 &&
    arg0.kind === "atom" && arg0.val === "\\" &&
    arg1.kind === "ident" &&
    arg2.kind === "atom" && arg2.val === ":" &&
    arg3.kind === "node" && arg3.type === "ty" &&
    arg4.kind === "atom" && arg4.val === "," &&
    arg5.kind === "node" && arg5.type === "term"
  ) {
    const t = elabTerm(arg5, bdepth+1, fdepth, bvMap.set(arg1.val, bdepth), fvMap, notations);
    return { kind: "lam", name: arg1.val, ty: elabTy(arg3), body: t };
  }

  if (
    arg0 && arg1 && arg2 &&
    arg0.kind === "atom" && arg0.val === "(" &&
    arg1.kind === "node" && arg1.type === "term" &&
    arg2.kind === "atom" && arg2.val === ")"
  ) {
    return elabTerm(arg1, bdepth, fdepth, bvMap, fvMap, notations);
  }

  for (const { name, descr } of notations) {
    if (descr.length !== stx.args.length) continue;
    let matched = true;
    let res: Term = { kind: "const", name };
    for (let i = 0; i < descr.length; ++i) {
      const arg = stx.args[i]!;
      const d = descr[i]!;

      if (d.kind === "atom") {
        if (arg.kind !== "atom") {
          matched = false;
          break;
        }
      } else {
        if (arg.kind !== "node" || arg.type !== "term") {
          matched = false;
          break;
        }
        res = { kind: "app", fn: res, arg: elabTerm(arg, bdepth, fdepth, bvMap, fvMap, notations) };
      }
    }
    
    if (matched) return res;
  }

  throw new Error("not implemented");
}

export function elabRule(stx: Syntax, fdepth: number, fvMap: Map<string, number>, notations: Notation[]): Rule {
  if (stx.kind !== "node") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
  if (stx.type !== "rule") throw new Error(`unreachable: ${JSON.stringify(stx)}`);

  const [arg0, arg1, arg2, arg3, arg4, arg5, ..._args] = stx.args;

  if (arg0 && arg0.kind === "node" && arg0.type === "term") {
    return { kind: "proves", p: elabTerm(arg0, 0, fdepth, Map(), fvMap, notations) };
  }

  if (
    arg0 && arg1 && arg2 && arg3 && arg4 && arg5 &&
    arg0.kind === "atom" && arg0.val === "!!" &&
    arg1.kind === "node" && arg1.type === "many" &&
    arg2.kind === "atom" && arg2.val === ":" &&
    arg3.kind === "node" && arg3.type === "ty" &&
    arg4.kind === "atom" && arg4.val === "," &&
    arg5.kind === "node" && arg5.type === "rule"
  ) {
    const xs = arg1.args.map(v => {
      if (v.kind !== "ident") throw new Error("unexpected syntax");
      return v.val;
    });
    const nextMap = xs.reduce((l, r, i) => {
      return l.set(r, fdepth+i);
    }, fvMap);
    const s = elabTy(arg3);
    const r = elabRule(arg5, fdepth+arg1.args.length, nextMap, notations);
    return xs.reduceRight((l, r) => {
      return { kind: "all", name: r, s, P: l };
    }, r);
  }

  if (
    arg0 && arg1 && arg2 &&
    arg0.kind === "node" && arg0.type === "rule" &&
    arg1.kind === "atom" && arg1.val === "=>" &&
    arg2.kind === "node" && arg2.type === "rule"
  ) {
    const r1 = elabRule(arg0, fdepth, fvMap, notations);
    const r2 = elabRule(arg2, fdepth, fvMap, notations);
    return { kind: "implies", P: r1, Q: r2 };
  }

  if (
    arg0 && arg1 && arg2 &&
    arg0.kind === "atom" && arg0.val === "(" &&
    arg1.kind === "node" && arg1.type === "rule" &&
    arg2.kind === "atom" && arg2.val === ")"
  ) {
    return elabRule(arg1, fdepth, fvMap, notations);
  }

  throw new Error("unexpected syntax");
}

export function elabNotation(stxs: Syntax[], name: string, prec: number, base: Ty): [Notation, Parser, string[], Ty] {
  let nd: NotationDescr[] = [];
  let pd: ParserDescr[] = [];
  let kw: string[] = [];
  let ty: Ty = base;
  for (const stx of stxs) {
    if (stx.kind !== "node") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
    if (stx.type !== "notation") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
    
    const [arg0, arg1, arg2, ..._args] = stx.args;

    if (arg0 && arg0.kind === "str") {
      nd.push({ kind: "atom", val: arg0.val });
      pd.push({ kind: "symbol", val: arg0.val });
      kw.push(arg0.val);
      continue;
    }

    if (
      arg0 && arg1 && arg2 &&
      arg0.kind === "node" && arg0.type === "ty" &&
      arg1.kind === "atom" && arg1.val === ":" &&
      arg2.kind === "num"
    ) {
      const t = elabTy(arg0);
      nd.push({ kind: "term", ty: t, prec: arg2.val });
      pd.push({ kind: "recurse", type: "term", prec: arg2.val });
      ty = { kind: "arrow", left: t, right: ty };
      continue;
    }

    throw new Error(`unexpected syntax: ${JSON.stringify(stx)}`);
  }

  return [{ name, descr: nd }, { prec, descr: pd }, kw, ty];
} 

export function elabTactic(ts: TacticState, stx: Syntax, notations: Notation[]): TacticState {
  if (stx.kind !== "node") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
  if (stx.type !== "tactic") throw new Error(`unreachable: ${JSON.stringify(stx)}`);

  const [arg0, arg1, arg2, arg3, ..._args] = stx.args;

  if (arg0 && arg0.kind === "atom" && arg0.val === "assum") {
    return Tactic.assumption(ts);
  }

  if (
    arg0 && arg1 &&
    arg0.kind === "atom" && arg0.val === "intro" &&
    arg1.kind === "node" && arg1.type === "many"
  ) {
    let ts1 = ts;
    for (const s of arg1.args) {
      if (s.kind !== "ident") throw new Error(`unexpected syntax: ${JSON.stringify(s)}`);
      ts1 = Tactic.intro(ts1, s.val);
    }
    return ts1;
  }

  if (
    arg0 && arg1 && arg2 &&
    arg0.kind === "atom" && arg0.val === "apply" &&
    arg1.kind === "ident" &&
    arg2.kind === "node" && arg2.type === "many"
  ) {
    const g = Tactic.getGoal(ts);
    const fvMap = Map(g.fctx.toReversed().map(([n], i) => [n, i]));
    const xs = arg2.args.map(v => {
      if (v.kind === "ident") {
        return v.val;
      } else if (v.kind === "node" && v.type === "term") {
        return elabTerm(v, 0, g.fctx.length, Map(), fvMap, notations)
      } else {
        throw new Error(`unexpected syntax: ${JSON.stringify(v)}`);
      }
    });
    return Tactic.apply(ts, arg1.val, xs);
  }

  if (
    arg0 && arg1 && arg2 && arg3 &&
    arg0.kind === "atom" && arg0.val === "have" &&
    arg1.kind === "ident" &&
    arg2.kind === "atom" && arg2.val === ":" &&
    arg3.kind === "node" && arg3.type === "rule"
  ) {
    const g = Tactic.getGoal(ts);
    const fvMap = Map(g.fctx.toReversed().map(([n], i) => [n, i]));
    return Tactic.have(ts, arg1.val, elabRule(arg3, g.fctx.length, fvMap, notations));
  }

  throw new Error(`unexpected syntax: ${JSON.stringify(stx)}`);
}

export function elabCommand(cs: CoreState, stx: Syntax): CoreState {
  if (stx.kind !== "node") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
  if (stx.type !== "command") throw new Error(`unreachable: ${JSON.stringify(stx)}`);
  
  const [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, ..._args] = stx.args;

  if (
    arg0 && arg1 && arg2 && arg3 && arg4 && arg5 && arg6 && arg7 &&
    arg0.kind === "atom" && arg0.val === "notation" &&
    arg1.kind === "atom" && arg1.val === ":" &&
    arg2.kind === "num" &&
    arg3.kind === "node" && arg3.type === "many" &&
    arg4.kind === "atom" && arg4.val === ":" &&
    arg5.kind === "node" && arg5.type === "ty" &&
    arg6.kind === "atom" && arg6.val === ":=" &&
    arg7.kind === "ident"
  ) {
    if (cs.constants.has(arg7.val))
      throw new Error(`constant '${arg7.val}' is already declared`);

    const [notation, parser, keywords, ty] = elabNotation(arg3.args, arg7.val, arg2.val, elabTy(arg5));
    const ps = cs.parsers.get("term") ?? List<Parser>();
    return {
      ...cs,
      notations: [...cs.notations, notation],
      parsers: cs.parsers.set("term", ps.push(parser).sortBy(({ prec }) => -prec)),
      trie: keywords.reduce((l, r) => {
        return l.insert(r);
      }, cs.trie),
      constants: cs.constants.set(arg7.val, ty)
    };
  }

  if (
    arg0 && arg1 && arg2 && arg3 &&
    arg0.kind === "atom" && arg0.val === "axiom" &&
    arg1.kind === "ident" &&
    arg2.kind === "atom" && arg2.val === ":" &&
    arg3.kind === "node" && arg3.type === "rule"
  ) {
    if (cs.axioms.has(arg1.val))
      throw new Error(`'${arg1.val}' is already declared`);
    const r = elabRule(arg3, 0, Map(), cs.notations);
    if (!Rule.isWF(MCtx.default(), cs.constants, [], r))
      throw new Error(`rule '${arg1.val}' is not well-formed`);

    return {
      ...cs,
      axioms: cs.axioms.set(arg1.val, r)
    };
  }

  if (
    arg0 && arg1 && arg2 && arg3 && arg4 && arg5 &&
    arg0.kind === "atom" && arg0.val === "prove" &&
    arg1.kind === "ident" &&
    arg2.kind === "atom" && arg2.val === ":" &&
    arg3.kind === "node" && arg3.type === "rule" &&
    arg4.kind === "atom" && arg4.val === "by" &&
    arg5.kind === "node" && arg5.type === "many"
  ) {
    if (cs.axioms.has(arg1.val))
      throw new Error(`'${arg1.val}' is already declared`);
    const r = elabRule(arg3, 0, Map(), cs.notations);
    if (!Rule.isWF(MCtx.default(), cs.constants, [], r))
      throw new Error(`rule '${arg1.val}' is not well-formed`);

    const ts1: TacticState = {
      goals: [],
      axioms: cs.axioms,
      proofs: Map(),
      cctx: cs.constants,
      mctx: MCtx.default()
    };

    const [ts2, hole, goal] = Tactic.mkHole(ts1, r, [], []);

    let ts : TacticState = {
      ...ts2,
      goals: [goal]
    };
    
    for (const tac of arg5.args) {
      ts = elabTactic(ts, tac, cs.notations);
    }
    
    if (ts.goals.length !== 0) {
      let s = "unsolved goals\n";
      for (const g of ts.goals) {
        s += `case ${g.holeId}\n`;
        s += `\nVariables:\n`;
        s += g.fctx.reduceRight((l, r) => {
          return l + `\t${r[0]} : ${Ty.toString(r[1])}\n`;
        }, "");
        s += `\nHypothesis:\n`;
        s += g.ctx.reduce((l, r) => {
          return l + `\t${r[0]} : ${Rule.toString(r[1], g.fctx, 0)}\n`;
        }, "");
        s += `\nGoal: ${Rule.toString(g.target, g.fctx, 0)}`;
      }
      throw new Error(s);
    }

    return {
      ...cs,
      axioms: cs.axioms.set(arg1.val, r)
    };
  }

  throw new Error(`unexpected syntax: ${JSON.stringify(stx)}`);
}

