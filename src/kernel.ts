import { Map } from "immutable";

export type Ty =
  | { kind: "base", name: string }
  | { kind: "arrow", left: Ty, right: Ty };

export type Term =
  | { kind: "bvar", idx: number }
  | { kind: "fvar", idx: number }
  | { kind: "mvar", name: string }
  | { kind: "app", fn: Term, arg: Term }
  | { kind: "lam", name: string, ty: Ty, body: Term }
  | { kind: "const", name: string }
  
export type MCtx = Readonly<{
  assignment: Map<string, Term>,
  types: Map<string, Ty>,
  counter: number
}>;

export type Rule =
  | { kind: 'proves', p: Term }
  | { kind: 'implies', P: Rule, Q: Rule }
  | { kind: 'all', name: string, s: Ty, P: Rule };

export type Proof =
  | { kind: "hole", name: string }
  | { kind: 'ax', name: string }
  | { kind: 'hyp', idx: number }
  | { kind: 'impI', P: Rule, hq: Proof }
  | { kind: 'impE', hpq: Proof, hp: Proof }
  | { kind: 'allI', name: string, s: Ty, h: Proof }
  | { kind: 'allE', h: Proof, t: Term };

export type Goal = {
  holeId: string;
  target: Rule;
  ctx: [string, Rule, Proof | null][];
  fctx: [string, Ty][];
}

export type TacticState = {
  goals: Goal[],
  proofs: Map<string, Proof>,
  axioms: Map<string, Rule>,
  cctx: Map<string, Ty>,
  mctx: MCtx
}

export abstract class TacticError {
  abstract message(): string;
}

class NoGoalsError extends TacticError {
  message(): string {
    return "no goals to solve";
  }
}

class AssumptionError extends TacticError {
  message(): string {
    return "assumption failed";
  }
}

class IntroError extends TacticError {
  message(): string {
    return "intro failed";
  }
}

class UnknownIdError extends TacticError {
  constructor(public readonly id: string) { super(); }
  message(): string {
    return `unknown identifier: ${this.id}`;
  }
}

class NotDefEqError extends TacticError {
  constructor(public readonly P: string, public readonly Q: string) { super(); }
  message(): string {
    return `${this.P} is not definitionally equal to ${this.Q}`;
  }
}

class TypeMismatchError extends TacticError {
  constructor(public readonly t: string, public readonly ty1: string, public readonly ty2: string) { super(); }
  message(): string {
    return `type mismatch: ${this.t} has type ${this.ty1} but expected to have type ${this.ty2}`;
  }
}

class ApplyExcessArgumentError extends TacticError {
  message(): string {
    return "apply failed: excess arguments";
  }
}

class NotApplicableError extends TacticError {
  message(): string {
    return "apply failed: not applicable";
  }
}

export const Ty = {

  toString: (ty: Ty, left: boolean = false): string => {
    switch (ty.kind) {
    case "base": return ty.name;
    case "arrow":
      const s = `${Ty.toString(ty.left, true)} -> ${Ty.toString(ty.right, false)}`;
      return left ? `(${s})` : s;
    }
  },

  eq: (a: Ty, b: Ty): boolean => {
    if (a.kind === "base" && b.kind === "base") return a.name === b.name;
    if (a.kind === "arrow" && b.kind === "arrow") return Ty.eq(a.left, b.left) && Ty.eq(a.right, b.right);
    return false;
  }
};

export const Term = {

  toString(t: Term, fctx: [string, Ty][], bctx: [string, Ty][], prec: number = 0): string {
    switch (t.kind) {
    case "bvar":
      return bctx[t.idx] ? bctx[t.idx]![0] : `#${t.idx}`;
    case "fvar":
      return fctx[t.idx] ? fctx[t.idx]![0] : `?${t.idx}`;
    case "mvar": return `$${t.name}`;
    case "app":
      const sApp = `${Term.toString(t.fn, fctx, bctx, 1)} ${Term.toString(t.arg, fctx, bctx, 2)}`;
      return prec > 1 ? `(${sApp})` : sApp;
    case "lam":
      const sLam = `\\${t.name} : ${Ty.toString(t.ty)}, ${Term.toString(t.body, fctx, [[t.name, t.ty], ...bctx], 0)}`;
      return prec > 0 ? `(${sLam})` : sLam;
    case "const": return t.name;
    }
  },

  instM(mctx: MCtx, t: Term): Term {
    switch (t.kind) {
    case "mvar":
      const v = MCtx.getAssignment(mctx, t.name);
      return v ? Term.instM(mctx, v) : t;
    case "app":
      return { kind: "app", fn: Term.instM(mctx, t.fn), arg: Term.instM(mctx, t.arg) };
    case "lam":
      return { kind: "lam", name: t.name, ty: t.ty, body: Term.instM(mctx, t.body) };
    default:
      return t;
    }
  },
  
  occursM(mctx: MCtx, t: Term, m: string): boolean {
    switch (t.kind) {
    case 'mvar':
      if (t.name === m) return true;
      const v = MCtx.getAssignment(mctx, t.name);
      if (v) return Term.occursM(mctx, v, m);
      return false;
    case 'app':
      return Term.occursM(mctx, t.fn, m) || Term.occursM(mctx, t.arg, m);
    case 'lam':
      return Term.occursM(mctx, t.body, m);
    default:
      return false;
    }
  },

  liftB(t: Term, n: number, k: number = 0): Term {
    switch (t.kind) {
    case 'bvar': return t.idx < k ? t : { kind: 'bvar', idx: t.idx + n };
    case 'app': return { kind: 'app', fn: Term.liftB(t.fn, n, k), arg: Term.liftB(t.arg, n, k) };
    case 'lam': return { kind: 'lam', name: t.name, ty: t.ty, body: Term.liftB(t.body, n, k + 1) };
    default: return t;
    }
  },

  substB(t: Term, u: Term, k: number): Term {
    switch (t.kind) {
    case 'bvar':
      if (t.idx === k) return Term.liftB(u, k);
      if (t.idx > k) return { kind: 'bvar', idx: t.idx - 1 };
      return t;
    case 'app': return { kind: 'app', fn: Term.substB(t.fn, u, k), arg: Term.substB(t.arg, u, k) };
    case 'lam': return { kind: 'lam', name: t.name, ty: t.ty, body: Term.substB(t.body, u, k + 1) };
    default: return t;
    }
  },

  liftF(t: Term, n: number, k: number = 0): Term {
    switch (t.kind) {
    case 'fvar': return t.idx < k ? t : { kind: 'fvar', idx: t.idx + n };
    case 'app': return { kind: 'app', fn: Term.liftF(t.fn, n, k), arg: Term.liftF(t.arg, n, k) };
    case 'lam': return { kind: 'lam', name: t.name, ty: t.ty, body: Term.liftF(t.body, n, k + 1) };
    default: return t;
    }
  },

  substF(t: Term, u: Term, k: number): Term {
    switch (t.kind) {
    case 'fvar':
      if (t.idx === k) return Term.liftF(u, k);
      if (t.idx > k) return { kind: 'fvar', idx: t.idx - 1 };
      return t;
    case 'app': return { kind: 'app', fn: Term.substF(t.fn, u, k), arg: Term.substF(t.arg, u, k) };
    case 'lam': return { kind: 'lam', name: t.name, ty: t.ty, body: Term.substF(t.body, u, k) };
    default: return t;
    }
  },

  inferType(mctx: MCtx, cctx: Map<string, Ty>, fctx: [string, Ty][], bctx: [string, Ty][], t: Term): Ty {
    switch (t.kind) {
    case 'bvar':
      if (t.idx < bctx.length) return bctx[t.idx]![1];
      throw new Error(`invalid bvar: #${t.idx}`);
    case 'fvar':
      if (t.idx < fctx.length) return fctx[t.idx]![1];
      throw new Error(`invalid fvar: ?${t.idx}`);
    case 'mvar':
      const mty = mctx.types.get(t.name);
      if (mty) return mty;
      throw new Error(`invalid mvar: $${t.name}`);
    case 'app':
      const fnTy = Term.inferType(mctx, cctx, fctx, bctx, t.fn);
      if (fnTy.kind !== 'arrow') throw new Error("function type expected");
      const argTy = Term.inferType(mctx, cctx, fctx, bctx, t.arg);
      if (!Ty.eq(fnTy.left, argTy)) throw new Error("type mismatch in application");
      return fnTy.right;
    case 'lam':
      const bodyTy = Term.inferType(mctx, cctx, fctx, [[t.name, t.ty], ...bctx], t.body);
      return { kind: "arrow", left: t.ty, right: bodyTy };
    case 'const':
      const cty = cctx.get(t.name);
      if (cty) return cty;
      throw new Error(`unknown const: \`${t.name}\``);
    }
  },

  whnf(mctx: MCtx, t: Term): Term {
    switch (t.kind) {
    case "app":
      const fn = Term.whnf(mctx, t.fn);
      if (fn.kind === "lam")
        return Term.whnf(mctx, Term.substB(fn.body, t.arg, 0));
      else
        return { kind: "app", fn, arg: t.arg };
    case "mvar":
      const v = MCtx.getAssignment(mctx, t.name);
      return v ? Term.whnf(mctx, v) : t;
    default:
      return t;
    }
  },

  isDefEq(mctx: MCtx, t1: Term, t2: Term): [MCtx, boolean] {
    const n1 = Term.whnf(mctx, t1);
    const n2 = Term.whnf(mctx, t2);

    if (n1.kind === "bvar" && n2.kind === "bvar") {
      if (n1.idx === n2.idx) return [mctx, true];
    }
    else if (n1.kind === "fvar" && n2.kind === "fvar") {
      if (n1.idx === n2.idx) return [mctx, true];
    }
    else if (n1.kind === "const" && n2.kind === "const") {
      if (n1.name === n2.name) return [mctx, true];
    }
    else if (n1.kind === "mvar" && n2.kind === "mvar") {
      if (n1.name === n2.name) return [mctx, true];
      return [MCtx.assign(mctx, n1.name, n2), true];
    }
    else if (n1.kind === "mvar") {
      if (Term.occursM(mctx, n2, n1.name)) return [mctx, false];
      return [MCtx.assign(mctx, n1.name, n2), true];
    }
    else if (n2.kind === "mvar") {
      if (Term.occursM(mctx, n1, n2.name)) return [mctx, false];
      return [MCtx.assign(mctx, n2.name, n1), true];
    }
    else if (n1.kind === "lam" && n2.kind === "lam") {
      if (!Ty.eq(n1.ty, n2.ty)) return [mctx, false];
      return Term.isDefEq(mctx, n1.body, n2.body);
    }
    else if (n1.kind === "app" && n2.kind === "app") {
      const [mctx1, de1] = Term.isDefEq(mctx, n1.fn, n2.fn);
      if (!de1) return [mctx, false];
      const [mctx2, de2] = Term.isDefEq(mctx1, n1.arg, n2.arg);
      if (!de2) return [mctx, false];
      return [mctx2, true];
    }
    return [mctx, false];
  }
};

export const MCtx = {
  default(): MCtx { return { assignment: Map(), types: Map(), counter: 0 } },

  getAssignment(mctx: MCtx, m: string): Term | null {
    return mctx.assignment.get(m, null);
  },

  assign(mctx: MCtx, m: string, t: Term): MCtx {
    return { ...mctx, assignment: mctx.assignment.set(m, t) };
  },

  mkFreshMVar(mctx: MCtx, ty: Ty): [MCtx, Term] {
    const name = `_m${mctx.counter}`;
    return [{
      ...mctx,
      types: mctx.types.set(name, ty),
      counter: mctx.counter + 1
    }, { kind: "mvar", name }];
  }
}

export const Rule = {

  toString(r: Rule, fctx: [string, Ty][], prec: number = 0): string {
    switch (r.kind) {
    case "proves":
      return Term.toString(r.p, fctx, [], 0);
    case "implies":
      const sImp = `${Rule.toString(r.P, fctx, 2)} => ${Rule.toString(r.Q, fctx, 1)}`;
      return prec > 1 ? `(${sImp})` : sImp;
    case "all":
      const sAll = `!! ${r.name} : ${Ty.toString(r.s)}, ${Rule.toString(r.P, [[r.name, r.s], ...fctx], 0)}`;
      return prec > 0 ? `(${sAll})` : sAll;
    }
  },

  substF(r: Rule, u: Term, k: number): Rule {
    switch (r.kind) {
    case "proves":
      return { kind: "proves", p: Term.substF(r.p, Term.liftF(u, k), k) };
    case "implies":
      return { kind: "implies", P: Rule.substF(r.P, u, k), Q: Rule.substF(r.Q, u, k) };
    case "all":
      return { kind: "all", name: r.name, s: r.s, P: Rule.substF(r.P, u, k+1) };
    }
  },

  instM(mctx: MCtx, r: Rule): Rule {
    switch (r.kind) {
    case "proves":
      return { kind: "proves", p: Term.instM(mctx, r.p)};
    case "implies":
      return { kind: "implies", P: Rule.instM(mctx, r.P), Q: Rule.instM(mctx, r.Q) };
    case "all":
      return { kind: "all", name: r.name, s: r.s, P: Rule.instM(mctx, r.P) };
    }
  },

  isDefEq(mctx: MCtx, r1: Rule, r2: Rule): [MCtx, boolean] {
    if (r1.kind === "proves" && r2.kind === "proves") {
      const [mctxn, de] = Term.isDefEq(mctx, r1.p, r2.p);
      return de ? [mctxn, true] : [mctx, false];
    }
    if (r1.kind === "implies" && r2.kind === "implies") {
      const [mctx1, de1] = Rule.isDefEq(mctx, r1.P, r2.P);
      if (!de1) return [mctx, false];
      const [mctx2, de2] = Rule.isDefEq(mctx1, r1.Q, r2.Q);
      if (!de2) return [mctx, false];
      return [mctx2, true];
    }
    if (r1.kind === "all" && r2.kind === "all") {
      if (!Ty.eq(r1.s, r2.s)) return [mctx, false];
      return Rule.isDefEq(mctx, r1.P, r2.P);
    }
    return [mctx, false];
  },

  isWF(mctx: MCtx, cctx: Map<string, Ty>, fctx: [string, Ty][], r: Rule): boolean {
    switch (r.kind) {
    case "proves":
      const ty = Term.inferType(mctx, cctx, fctx, [], r.p);
      return ty.kind === "base";
    case "implies":
      return Rule.isWF(mctx, cctx, fctx, r.P) && Rule.isWF(mctx, cctx, fctx, r.Q);
    case "all":
      return Rule.isWF(mctx, cctx, [[r.name, r.s], ...fctx], r.P);
    }
  }
}

export const Proof = {
  check(mctx: MCtx, cctx: Map<string, Ty>, ax: Map<string, Rule>, ctx: Rule[], fctx: [string, Ty][], p: Proof): Rule {
    switch (p.kind) {
    case "hole":
      throw new Error("proof has a hole");
    case "ax":
      const r = ax.get(p.name);
      if (r) return r;
      throw new Error(`invalid axiom: ${p.name}`);
    case "hyp":
      if (p.idx < ctx.length) return ctx[p.idx]!;
      throw new Error(`invalid hypothesis: #${p.idx}`);
    case "impI":
      const Q = Proof.check(mctx, cctx, ax, [...ctx, p.P], fctx, p.hq);
      return { kind: "implies", P: p.P, Q };
    case "impE":
      const imp = Proof.check(mctx, cctx, ax, ctx, fctx, p.hpq);
      if (imp.kind !== "implies") throw new Error("implies expected at impE");
      const PImp = Proof.check(mctx, cctx, ax, ctx, fctx, p.hp);
      const [, de] = Rule.isDefEq(mctx, imp.P, PImp);
      if (!de) throw new Error(`${Rule.toString(imp.P, fctx)} != ${Rule.toString(PImp, fctx)}`);
      return imp.Q;
    case "allI":
      const PAll = Proof.check(mctx, cctx, ax, ctx, [[p.name, p.s], ...fctx], p.h);
      return { kind: "all", name: p.name, s: p.s, P: PAll };
    case "allE":
      const all = Proof.check(mctx, cctx, ax, ctx, fctx, p.h);
      if (all.kind !== "all") throw new Error("all expected at allE");
      const ty = Term.inferType(mctx, cctx, fctx, [], p.t);
      if (!Ty.eq(all.s, ty)) throw new Error("type mismatch at allE");
      return Rule.substF(all.P, p.t, 0);
    }
  },

  instHole(p: Proof, proofs: Map<string, Proof>): Proof {
    switch (p.kind) {
    case "hole":
      const resv = proofs.get(p.name);
      if (resv) return Proof.instHole(resv, proofs);
      return p;
    case "impI":
      return { kind: "impI", P: p.P, hq: Proof.instHole(p.hq, proofs) };
    case "impE":
      return { kind: "impE", hpq: Proof.instHole(p.hpq, proofs), hp: Proof.instHole(p.hp, proofs) };
    case "allI":
      return { kind: "allI", name: p.name, s: p.s, h: Proof.instHole(p.h, proofs) };
    case "allE":
      return { kind: "allE", h: Proof.instHole(p.h, proofs), t: p.t };
    default: return p;
    }
  }
}

export const Tactic = {
  getGoal(ts: TacticState): Goal {
    if (ts.goals.length === 0) throw new NoGoalsError();
    return ts.goals[0]!;
  },

  replaceGoal(ts: TacticState, newGoals: Goal[]): TacticState {
    if (ts.goals.length === 0) throw new NoGoalsError();
    const [, ...tail] = ts.goals;
    const goals = [...newGoals, ...tail];
    
    return {
      ...ts,
      goals: goals.map(g => ({
        ...g,
        target: Rule.instM(ts.mctx, g.target),
        ctx: g.ctx.map(([n, r, p]) => [n, Rule.instM(ts.mctx, r), p])
      }))
    };
  },

  assignProof(ts: TacticState, holeId: string, p: Proof): TacticState {
    return {
      ...ts,
      proofs: ts.proofs.set(holeId, p)
    };
  },

  mkHole(ts: TacticState, target: Rule, ctx: [string, Rule, Proof | null][], fctx: [string, Ty][]): [TacticState, Proof, Goal] {
    const name = `_hole_${ts.mctx.counter}`;
    const newGoal: Goal = { holeId: name, target, ctx, fctx };
    return [
      { ...ts, mctx: { ...ts.mctx, counter: ts.mctx.counter+1 }},
      { kind: "hole", name },
      newGoal
    ];
  },

  assumption(ts: TacticState): TacticState {
    const g = Tactic.getGoal(ts);
    for (let i = 0; i < g.ctx.length; ++i) {
      const [, rule, p] = g.ctx[i]!;
      const [mctx, de] = Rule.isDefEq(ts.mctx, rule, g.target);
      if (!de) continue;
      const ts1 = { ...ts, mctx };
      const ts2 = Tactic.assignProof(ts1, g.holeId, p ?? { kind: "hyp", idx: i });
      return this.replaceGoal(ts2, []);
    }
    throw new AssumptionError();
  },

  intro(ts: TacticState, name: string): TacticState {
    const g = Tactic.getGoal(ts);
    switch (g.target.kind) {
    case "implies":
      const [ts1, qHole, g1] = Tactic.mkHole(ts, g.target.Q, [...g.ctx, [name, g.target.P, null]], g.fctx);
      const ts2 = Tactic.assignProof(ts1, g.holeId, { kind: "impI", P: g.target.P, hq: qHole });
      return Tactic.replaceGoal(ts2, [g1]);
    case "all":
      const [ts3, pHole, g2] = Tactic.mkHole(ts, g.target.P, g.ctx, [[name, g.target.s], ...g.fctx]);
      const ts4 = Tactic.assignProof(ts3, g.holeId, { kind: "allI", name, s: g.target.s, h: pHole });
      return Tactic.replaceGoal(ts4, [g2]);
    default: throw new IntroError();
    }
  },

  apply(ts: TacticState, name: string, args: (string|Term)[]): TacticState {
    const g = Tactic.getGoal(ts);
    const idx = g.ctx.findIndex(([n,,]) => n === name);
    if (idx !== -1) {
      return Tactic.applyArgs(ts, { kind: "hyp", idx }, g.ctx[idx]![1], args);
    }
    const rule = ts.axioms.get(name);
    if (rule) {
      return Tactic.applyArgs(ts, { kind: "ax", name }, rule, args);
    }
    throw new UnknownIdError(name);
  },

  applyArgs(ts: TacticState, p: Proof, r: Rule, args: (string|Term)[]): TacticState {
    const g = Tactic.getGoal(ts);

    const [t, ...nextArgs] = args;

    if (typeof t === "string") {
      switch (r.kind) {
      case "implies":
        const idx = g.ctx.findIndex(([n,,]) => n === t);
        if (idx === -1) throw new UnknownIdError(t);
        const [mctx1, de] = Rule.isDefEq(ts.mctx, r.P, g.ctx[idx]![1]);
        if (!de) throw new NotDefEqError(Rule.toString(r.P, g.fctx), Rule.toString(g.ctx[idx]![1], g.fctx));
        return Tactic.applyArgs({ ...ts, mctx: mctx1 }, { kind: "impE", hpq: p, hp: { kind: "hyp", idx }}, r.Q, nextArgs);
      case "all":
        const idx2 = g.fctx.findIndex(([n,]) => n === t);
        if (idx2 !== -1) {
          const P = Rule.substF(r.P, { kind: "fvar", idx: idx2 }, 0);
          return Tactic.applyArgs(ts, { kind: "allE", h: p, t: { kind: "fvar", idx: idx2 } }, P, nextArgs);
        }
        const c = ts.cctx.get(t);
        if (c) {
          if (!Ty.eq(c, r.s))
            throw new TypeMismatchError(t, Ty.toString(c), Ty.toString(r.s));
          const P = Rule.substF(r.P, { kind: "const", name: t }, 0);
          return Tactic.applyArgs(ts, { kind: "allE", h: p, t: { kind: "const", name: t } }, P, nextArgs);
        }
        throw new UnknownIdError(t);
      default:
        throw new ApplyExcessArgumentError();
      }
    } else if (t) {
      if (r.kind !== "all") throw new NotApplicableError();
      const ty = Term.inferType(ts.mctx, ts.cctx, g.fctx, [], t);
      if (!Ty.eq(ty, r.s))
        throw new TypeMismatchError(Term.toString(t, g.fctx, []), Ty.toString(ty), Ty.toString(r.s));
      const P = Rule.substF(r.P, t, 0);
      return Tactic.applyArgs(ts, { kind: "allE", h: p, t }, P, nextArgs);
    } else {
      return Tactic.applyCore(ts, p, r, []);
    }
  },

  applyCore(ts: TacticState, p: Proof, r: Rule, goals: Goal[]): TacticState {
    const g = Tactic.getGoal(ts);

    const [mctx1, de] = Rule.isDefEq(ts.mctx, r, g.target);
    if (de) {
      const ts1 = Tactic.assignProof({ ...ts, mctx: mctx1 }, g.holeId, p);
      return Tactic.replaceGoal(ts1, goals);
    }

    switch (r.kind) {
    case "implies":
      const [ts1, pHole, newGoal] = Tactic.mkHole(ts, r.P, g.ctx, g.fctx);
      return Tactic.applyCore(ts1, { kind: "impE", hpq: p, hp: pHole }, r.Q, [...goals, newGoal]);
    case "all":
      const [mctx2, mv] = MCtx.mkFreshMVar(ts.mctx, r.s);
      const P = Rule.substF(r.P, mv, 0);
      return Tactic.applyCore({ ...ts, mctx: mctx2 }, { kind: "allE", h: p, t: mv}, P, goals);
    default:
      throw new NotDefEqError(Rule.toString(r, g.fctx), Rule.toString(g.target, g.fctx));
    }
  },

  have(ts: TacticState, name: string, r: Rule): TacticState {
    const g = Tactic.getGoal(ts);
    const [ts1, hole, lemmaGoal] = Tactic.mkHole(ts, r, g.ctx, g.fctx);
    const newGoal: Goal = {
      ...g,
      ctx: [...g.ctx, [name, r, hole]]
    };

    return Tactic.replaceGoal(ts1, [lemmaGoal, newGoal]);
  }
}
