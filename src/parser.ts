import { Map, List, Set } from "immutable";

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

// Prec-sorted list of Parser, indexed by node type
export type Parsers = Map<string, List<Parser>>;


const END_KEY = Symbol("END");

export type TrieNode = Map<string | typeof END_KEY, TrieNode>;

export class SeparatorTrie {
  // 내부 구조: Map<string, Map | boolean>
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
      
      // 다음 글자로 이동
      const nextNode = node.get(char);

      if (!nextNode) {
        break; // 매칭 실패
      }

      node = nextNode;
      currentLength++;

      // 현재 노드가 단어의 끝(END_KEY)을 가지고 있는지 확인
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

    // 1. 공백 스킵
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
          // 닫는 따옴표 발견 -> 종료
          end++; // 닫는 따옴표 포함
          return {
            token: this.text.slice(start, end), // "abc" 형태 그대로 반환
            nextIndex: end
          };
        }
        
        if (char === '\\') {
          // 이스케이프 문자 처리: 다음 한 글자를 무조건 건너뜀
          end++;
        }
        
        end++;
      }
      // 닫는 따옴표를 못 찾고 끝난 경우 (에러 상황이지만 여기선 끝까지 읽음)
      return { token: this.text.slice(start, end), nextIndex: end };
    }

    if (/\d/.test(this.text[start]!)) {
      let end = start + 1;
      while (end < this.text.length && /\d/.test(this.text[end]!)) {
        end++;
      }
      return { token: this.text.slice(start, end), nextIndex: end };
    }

    // 2. Trie Longest Match (구분자 확인)
    const sepLen = trie.matchLongest(this.text, start);
    if (sepLen > 0) {
      return {
        token: this.text.slice(start, start + sepLen),
        nextIndex: start + sepLen,
      };
    }

    // 3. 일반 식별자/리터럴 읽기
    let end = start;
    while (end < this.text.length) {
      if (/\s/.test(this.text[end]!)) break;

      // 읽는 도중 Trie에 매칭되는 구분자가 나오면 거기서 끊음
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

  // 1. Prefix 파싱 (NUD)
  // 첫 번째 요소가 자기 자신(targetType)에 대한 recurse가 *아닌* 규칙들을 찾습니다.
  // (좌재귀가 아닌 규칙들)
  const prefixRules = allRules.filter(rule => {
    const first = rule.descr[0];
    return !first || !(first.kind === "recurse" && first.type === targetType);
  });

  let left: Syntax | null = null;
  let currentStream = stream;
  let prefixMatched = false;
  let lastError: ParseResult = { success: false, reason: "unexpected syntax", fatal: false };

  // Prefix 규칙 중 매칭되는 것 시도
  for (const rule of prefixRules) {
    const res = parseRule(currentStream, rule.descr, parsers, trie, null);
    if (res.success) {
      left = { kind: "node", type: targetType, args: res.args };
      currentStream = res.rest;
      prefixMatched = true;
      break;
    } else {
      // 가장 그럴듯한 에러를 남기기 위해 (단순 구현으로는 마지막 에러 저장)
      lastError = res;

      if (res.fatal)
        return res;
    }
  }

  if (!prefixMatched || !left) {
    return lastError;
  }

  // 2. Infix 파싱 (LED) - 반복
  while (true) {
    if (!currentStream.peek(trie)) break;

    // 다음 토큰으로 시작할 수 있는 Infix 규칙들을 찾습니다.
    // Infix 규칙: 첫 번째 요소가 자기 자신(targetType)에 대한 recurse인 규칙
    const infixRules = allRules.filter(rule => {
      const first = rule.descr[0];
      return first && (first.kind === "recurse" && first.type === targetType);
    });

    // Infix 규칙 중, 현재 minPrec보다 결합력이 높은 규칙만 고려
    // 그리고 다음 토큰과 매칭되는지 확인 (Lookahead)
    // Pratt 파서에서 Infix 규칙 선택은 "다음 토큰"을 보고 결정하는 것이 일반적입니다.
    // 여기서는 rule.descr[1] (왼쪽 항 다음의 요소)이 매칭되는지 봅니다.
    
    let infixMatchedRule: Parser | null = null;
    
    for (const rule of infixRules) {
      if (rule.prec < minPrec) continue;
      
      // Infix 규칙 형태: [ { recurse: myself }, { symbol: "+" }, ... ] 
      // 또는 [ { recurse: myself }, { recurse: other } ... ] (함수 적용)
      
      const nextDesc = rule.descr[1]; // 좌측 항(0번) 다음 요소
      
      if (!nextDesc) {
        // [recurse] 만 있는 규칙? -> Postfix? 
        // 여기서는 뒤에 뭔가 오는 경우만 처리한다고 가정
        continue;
      }

      if (nextDesc.kind === "symbol") {
        const token = currentStream.peek(trie);
        if (token === nextDesc.val) {
          infixMatchedRule = rule;
          break; // 우선순위 정렬되어 있다고 가정하면 첫 매칭 선택
        }
      } else if (nextDesc.kind === "ident" || nextDesc.kind === "recurse") {
        // 함수 적용(Application) 같은 경우: 심볼 없이 바로 이어짐
        // 이 경우 모호함이 있을 수 있으나, 일단 매칭된다고 보고 시도
        // (보통 함수 적용은 가장 높은 우선순위로, 또는 특정 심볼이 없을 때의 기본값으로 처리)
        
        // 예: term term -> 두 번째 term의 시작이 무엇이냐에 따라 결정됨.
        // 이는 예측하기 어려우므로, "심볼로 시작하지 않는 Infix 규칙"은
        // 항상 시도해보거나, 별도의 로직이 필요합니다.
        // 여기서는 간단히 "심볼이 없는 Infix"는 항상 매칭 후보로 둡니다.
        infixMatchedRule = rule;
        break; 
      }
    }

    if (!infixMatchedRule) {
      break; // 더 이상 확장할 Infix 규칙이 없음 -> 종료
    }

    // Infix 규칙 적용
    // parseRule에게 이미 파싱된 `left`를 전달합니다.
    const res = parseRule(currentStream, infixMatchedRule.descr, parsers, trie, left);
    
    if (res.success) {
      left = { kind: "node", type: targetType, args: res.args };
      currentStream = res.rest;
    } else {
      if (res.fatal)
        return res;
      // Infix 매칭 실패 시, 더 이상 진행 불가 (백트래킹 하지 않고 여기서 멈춤)
      // 또는 다른 Infix 규칙을 시도해야 할 수도 있지만, Pratt에서는 보통 결정적입니다.
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
  
  const savedIndex = stream.index; // 롤백 여부 판단용 (fatal check)
  let startIndex = 0;

  // Infix 규칙인 경우 왼쪽 항 주입
  if (leftInfix) {
    args.push(leftInfix);
    startIndex = 1; 
  }

  for (let i = startIndex; i < descr.length; i++) {
    const desc = descr[i]!;
    
    // 이 시점에서 스트림이 이동했으면, 실패 시 fatal로 간주할 수 있음 (커밋됨)
    const isCommitted = currentStream.index !== savedIndex;

    const res = parseArg(currentStream, desc, parsers, trie);
    
    if (res.success) {
      args.push(res.val);
      currentStream = res.rest;
    } else {
      // 이미 진행된 상태에서 실패하면 fatal 오류
      return { 
        success: false, 
        reason: res.reason, 
        fatal: res.fatal || isCommitted 
      };
    }
  }

  return { success: true, args, rest: currentStream };
}

/**
 * 단일 ParserDescr 요소를 파싱 (재귀적으로 many/optional 처리)
 */
function parseArg(
  stream: TokenStream,
  desc: ParserDescr,
  parsers: Parsers,
  trie: SeparatorTrie
): { success: true, val: Syntax, rest: TokenStream } | { success: false, reason: string, fatal: boolean } {
  
  // 1. Symbol
  if (desc.kind === "symbol") {
    const token = stream.peek(trie);
    if (!token) return { success: false, reason: `unexpected EOF, expected '${desc.val}'`, fatal: false };
    
    if (token === desc.val) {
      return { success: true, val: { kind: "atom", val: token }, rest: stream.next(trie) };
    } else {
      return { success: false, reason: `expected '${desc.val}', got '${token}'`, fatal: false };
    }
  } 
  
  // 2. Ident
  else if (desc.kind === "ident") {
    const token = stream.peek(trie);
    if (!token) return { success: false, reason: "unexpected EOF, expected identifier", fatal: false };
    if (trie.has(token)) {
      return { success: false, reason: `expected identifier, got symbol '${token}'`, fatal: false };
    }
    return { success: true, val: { kind: "ident", val: token }, rest: stream.next(trie) };
  } 
  
  // 3. String Literal
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
  
  // 4. Recurse (서브 표현식)
  else if (desc.kind === "recurse") {
    const res = parse(stream, desc.type, parsers, trie, desc.prec);
    if (res.success) {
      return { success: true, val: res.val, rest: res.rest };
    } else {
      return res; // 실패 전파
    }
  }
  
  // 6. Many (0 or more)
  else if (desc.kind === "many") {
    let curr = stream;
    const items: Syntax[] = [];
    while (true) {
      // 다음 토큰 확인하여 끝났는지 먼저 체크할 수도 있으나,
      // 여기서는 파싱 시도 후 실패 시 루프 탈출하는 방식 사용
      const res = parseArg(curr, desc.rule, parsers, trie);
      if (res.success) {
        items.push(res.val);
        curr = res.rest;
      } else {
        if (res.fatal) return res; // 내부에서 치명적 오류 발생 시 전체 중단
        break; // 단순 불일치면 반복 종료
      }
    }
    return { success: true, val: { kind: "node", type: "many", args: items }, rest: curr };
  }

  // 7. Many1 (1 or more)
  else if (desc.kind === "many1") {
    // 최소 1회 실행
    const firstRes = parseArg(stream, desc.rule, parsers, trie);
    if (!firstRes.success) {
      // 1회도 매칭 안되면 실패
      return firstRes;
    }

    let curr = firstRes.rest;
    const items: Syntax[] = [firstRes.val];

    // 이후 many와 동일
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