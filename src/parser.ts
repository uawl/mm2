import { Map, List } from "immutable";

export type Syntax =
  | { kind: "ident", val: string }
  | { kind: "atom", val: string }
  | { kind: "str", val: string }
  | { kind: "num", val: number }
  | { kind: "node", type: string, args: Syntax[] }

export type ParserDescr =
  | { kind: "recurse", type: string, prec: number }
  | { kind: "ident" }
  | { kind: "str" }
  | { kind: "num" }
  | { kind: "symbol", val: string }
  | { kind: "many", rule: ParserDescr }
  | { kind: "many1", rule: ParserDescr };

export type Parser = {
  prec: number,
  descr: ParserDescr[]
};

export type Parsers = Map<string, List<Parser>>;


const END_KEY = Symbol("END");

export type TrieNode = Map<string | typeof END_KEY, TrieNode>;

export class SeparatorTrie {
  constructor(private root: TrieNode = Map()) {}

  public insert(word: string): SeparatorTrie {
    if (word.length === 0) return this;

    const path = [...word.split(""), END_KEY];
    
    const newRoot = this.root.setIn(path, true);
    
    return new SeparatorTrie(newRoot);
  }

  public matchLongest(text: string, start: number): number {
    let node = this.root;
    let maxMatchLength = 0;
    let currentLength = 0;

    for (let i = start; i < text.length; i++) {
      const char = text[i]!;
      
      const nextNode = node.get(char);

      if (!nextNode) {
        break;
      }

      node = nextNode;
      currentLength++;

      if (node.has(END_KEY)) {
        maxMatchLength = currentLength;
      }
    }

    return maxMatchLength;
  }

  public has(word: string): boolean {
    const path = [...word.split(""), END_KEY];
    return this.root.hasIn(path);
  }
}

export class TokenStream {
  constructor(private text: string, public readonly index: number = 0) {}



  public peek(trie: SeparatorTrie): string | undefined {
    const { token } = this.readToken(trie);
    return token;
  }

  public next(trie: SeparatorTrie): TokenStream {
    const { nextIndex } = this.readToken(trie);
    return new TokenStream(this.text, nextIndex);
  }

  private readToken(trie: SeparatorTrie): { token: string | undefined; nextIndex: number } {
    let start = this.index;

    while (start < this.text.length && /\s/.test(this.text[start]!)) {
      start++;
    }

    if (start >= this.text.length) {
      return { token: undefined, nextIndex: start };
    }
    
    if (this.text[start] === '"') {
      let end = start + 1;
      while (end < this.text.length) {
        const char = this.text[end];
        
        if (char === '"') {
          end++;
          return {
            token: this.text.slice(start, end),
            nextIndex: end
          };
        }
        
        if (char === '\\') {
          end++;
        }
        
        end++;
      }
      return { token: this.text.slice(start, end), nextIndex: end };
    }

    if (/\d/.test(this.text[start]!)) {
      let end = start + 1;
      while (end < this.text.length && /\d/.test(this.text[end]!)) {
        end++;
      }
      return { token: this.text.slice(start, end), nextIndex: end };
    }

    const sepLen = trie.matchLongest(this.text, start);
    if (sepLen > 0) {
      return {
        token: this.text.slice(start, start + sepLen),
        nextIndex: start + sepLen,
      };
    }

    let end = start;
    while (end < this.text.length) {
      if (/\s/.test(this.text[end]!)) break;
      if (trie.matchLongest(this.text, end) > 0) {
        break;
      }
      end++;
    }

    return { token: this.text.slice(start, end), nextIndex: end };
  }
}

export function createTokenStream(text: string): TokenStream {
  return new TokenStream(text, 0);
}

type ParseResult = 
  | { success: true, val: Syntax, rest: TokenStream } 
  | { success: false, reason: string, fatal: boolean };

export function parse(
  stream: TokenStream,
  targetType: string,
  parsers: Parsers,
  trie: SeparatorTrie,
  minPrec: number = 0
): ParseResult {
  const allRules = parsers.get(targetType, List<Parser>());
  if (allRules.isEmpty()) {
    return { success: false, reason: `no rules for type '${targetType}'`, fatal: false };
  }

  const prefixRules = allRules.filter(rule => {
    const first = rule.descr[0];
    return !first || !(first.kind === "recurse" && first.type === targetType);
  });

  let left: Syntax | null = null;
  let currentStream = stream;
  let prefixMatched = false;
  let lastError: ParseResult = { success: false, reason: "unexpected syntax", fatal: false };

  for (const rule of prefixRules) {
    const res = parseRule(currentStream, rule.descr, parsers, trie, null);
    if (res.success) {
      left = { kind: "node", type: targetType, args: res.args };
      currentStream = res.rest;
      prefixMatched = true;
      break;
    } else {
      lastError = res;

      if (res.fatal)
        return res;
    }
  }

  if (!prefixMatched || !left) {
    return lastError;
  }

  while (true) {
    if (!currentStream.peek(trie)) break;

    const infixRules = allRules.filter(rule => {
      const first = rule.descr[0];
      return first && (first.kind === "recurse" && first.type === targetType);
    });
    
    let infixMatchedRule: Parser | null = null;
    
    for (const rule of infixRules) {
      if (rule.prec < minPrec) continue;

      const nextDesc = rule.descr[1];
      
      if (!nextDesc) {
        continue;
      }

      if (nextDesc.kind === "symbol") {
        const token = currentStream.peek(trie);
        if (token === nextDesc.val) {
          infixMatchedRule = rule;
          break;
        }
      } else if (nextDesc.kind === "ident" || nextDesc.kind === "recurse") {
        infixMatchedRule = rule;
        break; 
      }
    }

    if (!infixMatchedRule) {
      break;
    }

    const res = parseRule(currentStream, infixMatchedRule.descr, parsers, trie, left);
    
    if (res.success) {
      left = { kind: "node", type: targetType, args: res.args };
      currentStream = res.rest;
    } else {
      if (res.fatal)
        return res;
      break; 
    }
  }

  return { success: true, val: left, rest: currentStream };
}

function parseRule(
  stream: TokenStream,
  descr: ParserDescr[],
  parsers: Parsers,
  trie: SeparatorTrie,
  leftInfix: Syntax | null
): { success: true; args: Syntax[]; rest: TokenStream } | { success: false; reason: string, fatal: boolean } {
  
  let currentStream = stream;
  const args: Syntax[] = [];
  
  const savedIndex = stream.index;
  let startIndex = 0;

  if (leftInfix) {
    args.push(leftInfix);
    startIndex = 1; 
  }

  for (let i = startIndex; i < descr.length; i++) {
    const desc = descr[i]!;
    
    const isCommitted = currentStream.index !== savedIndex;

    const res = parseArg(currentStream, desc, parsers, trie);
    
    if (res.success) {
      args.push(res.val);
      currentStream = res.rest;
    } else {
      return { 
        success: false, 
        reason: res.reason, 
        fatal: res.fatal || isCommitted 
      };
    }
  }

  return { success: true, args, rest: currentStream };
}

function parseArg(
  stream: TokenStream,
  desc: ParserDescr,
  parsers: Parsers,
  trie: SeparatorTrie
): { success: true, val: Syntax, rest: TokenStream } | { success: false, reason: string, fatal: boolean } {
  
  if (desc.kind === "symbol") {
    const token = stream.peek(trie);
    if (!token) return { success: false, reason: `unexpected EOF, expected '${desc.val}'`, fatal: false };
    
    if (token === desc.val) {
      return { success: true, val: { kind: "atom", val: token }, rest: stream.next(trie) };
    } else {
      return { success: false, reason: `expected '${desc.val}', got '${token}'`, fatal: false };
    }
  } 
  
  else if (desc.kind === "ident") {
    const token = stream.peek(trie);
    if (!token) return { success: false, reason: "unexpected EOF, expected identifier", fatal: false };
    if (trie.has(token)) {
      return { success: false, reason: `expected identifier, got symbol '${token}'`, fatal: false };
    }
    return { success: true, val: { kind: "ident", val: token }, rest: stream.next(trie) };
  } 
  
  else if (desc.kind === "str") {
    const token = stream.peek(trie);
    if (!token) return { success: false, reason: "unexpected EOF, expected string", fatal: false };
    if (!token.startsWith('"')) {
      return { success: false, reason: `expected string literal, got '${token}'`, fatal: false };
    }
    try {
      const val = JSON.parse(token);
      return { success: true, val: { kind: "str", val }, rest: stream.next(trie) };
    } catch {
      return { success: false, reason: `invalid string literal: ${token}`, fatal: true };
    }
  } 

  else if (desc.kind === "num") {
    const token = stream.peek(trie);
    if (!token) return { success: false, reason: "unexpected EOF, expected string", fatal: false };
    if (!/\d/.test(token[0]!)) {
      return { success: false, reason: `expected natural literal, got '${token}'`, fatal: false };
    }
    try {
      const val = parseInt(token);
      return { success: true, val: { kind: "num", val }, rest: stream.next(trie) };
    } catch {
      return { success: false, reason: `invalid natural literal: ${token}`, fatal: true };
    }
  }
  
  else if (desc.kind === "recurse") {
    const res = parse(stream, desc.type, parsers, trie, desc.prec);
    if (res.success) {
      return { success: true, val: res.val, rest: res.rest };
    } else {
      return res;
    }
  }
  
  else if (desc.kind === "many") {
    let curr = stream;
    const items: Syntax[] = [];
    while (true) {
      const res = parseArg(curr, desc.rule, parsers, trie);
      if (res.success) {
        items.push(res.val);
        curr = res.rest;
      } else {
        if (res.fatal) return res;
        break;
      }
    }
    return { success: true, val: { kind: "node", type: "many", args: items }, rest: curr };
  }

  else if (desc.kind === "many1") {
    const firstRes = parseArg(stream, desc.rule, parsers, trie);
    if (!firstRes.success) {
      return firstRes;
    }

    let curr = firstRes.rest;
    const items: Syntax[] = [firstRes.val];

    while (true) {
      const res = parseArg(curr, desc.rule, parsers, trie);
      if (res.success) {
        items.push(res.val);
        curr = res.rest;
      } else {
        if (res.fatal) return res;
        break;
      }
    }
    return { success: true, val: { kind: "node", type: "many", args: items }, rest: curr };
  }

  return { success: false, reason: "unknown parser descriptor", fatal: true };
}