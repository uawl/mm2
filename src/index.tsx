import { useComputed, useSignal } from "@preact/signals";
import { render } from "preact";
import { createTokenStream, parse } from "./parser";
import { elabCommand } from "./elab";
import { defaultCoreState } from "./core";
import { TacticError } from "./kernel";


function App() {
  const s = useSignal("");
  const t = useComputed(() => {
    let st = createTokenStream(s.value);
    let state = defaultCoreState;
    while (true) {
      const p = parse(st, "command", state.parsers, state.trie);
      if (!p.success) {
        if (p.fatal || st.peek(state.trie))
          return p.reason;
        break;
      }
      st = p.rest;
      try {
        state = elabCommand(state, p.val);
      } catch (e) {
        if (e instanceof Error) return e.message;
        if (e instanceof TacticError) return e.message();
        throw `Unknown error: ${JSON.stringify(e)}`;
      }
    }
    return `all good`;
  });
  
  return <div style={{
    display: "flex",
    flexDirection: "column"
  }}>
    <textarea style={{
      width: "100%",
      height: "50dvh",
      resize: "none"
    }} value={s} onInput={(t) => { s.value = (t.target as HTMLTextAreaElement).value; }}></textarea>
    <pre style={{
      width: "100%"
    }}>{t}</pre>
  </div>;
}

render(<App />, document.body);

