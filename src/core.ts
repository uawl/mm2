import type { Notation } from "./elab"
import type { Rule, Ty } from "./kernel";
import { SeparatorTrie, type Parser, type Parsers } from "./parser";
import { Map, List } from "immutable";

const defaultParsers: Parsers = Map<string, List<Parser>>({
  command: List<Parser>([
    { prec: 1024, descr: [
      { kind: "symbol", val: "notation" },
      { kind: "symbol", val: ":" },
      { kind: "num" },
      { kind: "many1", rule: { kind: "recurse", type: "notation", prec: 0 } },
      { kind: "symbol", val: ":" },
      { kind: "recurse", type: "ty", prec: 0 },
      { kind: "symbol", val: ":=" },
      { kind: "ident" }
    ]},
    { prec: 1024, descr: [
      { kind: "symbol", val: "axiom" },
      { kind: "ident" },
      { kind: "symbol", val: ":" },
      { kind: "recurse", type: "rule", prec: 0 }
    ]},
    { prec: 1024, descr: [
      { kind: "symbol", val: "prove" },
      { kind: "ident" },
      { kind: "symbol", val: ":" },
      { kind: "recurse", type: "rule", prec: 0 },
      { kind: "symbol", val: "by" },
      { kind: "many", rule: { kind: "recurse", type: "tactic", prec: 0 } }
    ]}
  ]),
  notation: List<Parser>([
    { prec: 1024, descr: [
      { kind: "str" },
    ]},
    { prec: 1024, descr: [
      { kind: "recurse", type: "ty", prec: 0 },
      { kind: "symbol", val: ":" },
      { kind: "num" }
    ]}
  ]),
  applyArg: List<Parser>([
    { prec: 1024, descr: [
      { kind: "ident" },
    ]},
    { prec: 1024, descr: [
      { kind: "recurse", type: "term", prec: 61 },
    ]}
  ]),
  tactic: List<Parser>([
    { prec: 1024, descr: [
      { kind: "symbol", val: "assum" }
    ]},
    { prec: 1024, descr: [
      { kind: "symbol", val: "intro" },
      { kind: "many1", rule: { kind: "ident" } }
    ]},
    { prec: 1024, descr: [
      { kind: "symbol", val: "apply" },
      { kind: "ident" },
      { kind: "many", rule: { kind: "recurse", type: "applyArg", prec: 0 }}
    ]},
    { prec: 1024, descr: [
      { kind: "symbol", val: "have" },
      { kind: "ident" },
      { kind: "symbol", val: ":" },
      { kind: "recurse", type: "rule", prec: 0 }
    ]}
  ]),
  rule: List<Parser>([
    { prec: 1024, descr: [
      { kind: "symbol", val: "(" },
      { kind: "recurse", type: "rule", prec: 0 },
      { kind: "symbol", val: ")" }
    ]},
    { prec: 1024, descr: [
      { kind: "recurse", type: "term", prec: 0 }
    ]},
    { prec: 1024, descr: [
      { kind: "symbol", val: "!!" },
      { kind: "many1", rule: { kind: "ident" } },
      { kind: "symbol", val: ":" },
      { kind: "recurse", type: "ty", prec: 0 },
      { kind: "symbol", val: "," },
      { kind: "recurse", type: "rule", prec: 0 }
    ]},
    { prec: 30, descr: [
      { kind: "recurse", type: "rule", prec: 31 },
      { kind: "symbol", val: "=>" },
      { kind: "recurse", type: "rule", prec: 30 }
    ]}
  ]),
  term: List<Parser>([
    { prec: 1024, descr: [
      { kind: "symbol", val: "(" },
      { kind: "recurse", type: "term", prec: 0 },
      { kind: "symbol", val: ")" }
    ]},
    { prec: 1024, descr: [{ kind: "ident" }]},
    { prec: 1024, descr: [
      { kind: "symbol", val: "\\" },
      { kind: "ident" },
      { kind: "symbol", val: ":" },
      { kind: "recurse", type: "ty", prec: 0 },
      { kind: "symbol", val: "," },
      { kind: "recurse", type: "term", prec: 0 } 
    ]},
    { prec: 0, descr: [
      { kind: "recurse", type: "term", prec: 0 },
      { kind: "recurse", type: "term", prec: 1 },
    ]}
  ]),
  ty: List<Parser>([
    { prec: 1024, descr: [
      { kind: "symbol", val: "(" },
      { kind: "recurse", type: "ty", prec: 0 },
      { kind: "symbol", val: ")" }
    ]},
    { prec: 1024, descr: [{ kind: "ident" }] },
    { prec: 30, descr: [
      { kind: "recurse", type: "ty", prec: 31 },
      { kind: "symbol", val: "->" },
      { kind: "recurse", type: "ty", prec: 30 }
    ]}
  ])
});

const defaultTrie = new SeparatorTrie()
  .insert("(")
  .insert(")")
  .insert("->")
  .insert("\\")
  .insert(":")
  .insert(",")
  .insert("!!")
  .insert("=>")
  .insert(":=")
  .insert("assum")
  .insert("intro")
  .insert("apply")
  .insert("have")
  .insert("notation")
  .insert("axiom")
  .insert("prove")
  .insert("by");


export type CoreState = {
  parsers: Parsers,
  trie: SeparatorTrie,
  notations: Notation[],

  constants: Map<string, Ty>,
  axioms: Map<string, Rule>,
};

export const defaultCoreState: CoreState = {
  parsers: defaultParsers,
  trie: defaultTrie,
  notations: [],

  constants: Map(),
  axioms: Map()
};
