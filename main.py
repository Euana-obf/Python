from flask import Flask, request, render_template_string, send_file, jsonify
import random, string, base64, io, re, os, struct, time

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 64 * 1024 * 1024

# ============================================================
#  18byt0 v1.2 — FAST
#  Adaptive layers by size, bigger chunks, light mutation
# ============================================================

_ALPHA = string.ascii_letters
_ALNUM = string.ascii_letters + string.digits

def M(n=None):
    n = n or random.randint(8, 12)
    return random.choice(_ALPHA) + "".join(random.choices(_ALNUM, k=n - 1))

def R(a=1 << 16, b=(1 << 28) - 1):
    return random.randint(a, b)

def rxor(data: bytes, key: int) -> bytes:
    buf = bytearray(len(data))
    k = key & 0xFFFFFFFF
    for i, b in enumerate(data):
        k = (k * 1664525 + 1013904223) & 0xFFFFFFFF
        buf[i] = b ^ ((k >> 16) & 0xFF) ^ (i & 0xFF)
    return bytes(buf)

def b64e(b: bytes) -> str:
    return base64.b64encode(b).decode()

def pack_instr(words):
    return b"".join(struct.pack(">I", n & 0xFFFFFFFF) for n in words)

# -------------------- Macros (unchanged, fast enough) --------------------
def preprocess_macros(src: str, max_passes: int = 4) -> str:
    lines = src.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    defines, func_macros, out, i, stack = {}, {}, [], 0, []

    def active():
        return all(stack) if stack else True

    def expand_defined(expr):
        def repl(m):
            name = m.group(2)
            present = name in defines or name in func_macros
            if m.group(1):
                present = not present
            return "1" if present else "0"
        return re.sub(r"(!?)defined\s*\(\s*([A-Za-z_]\w*)\s*\)", repl, expr)

    def eval_simple(expr):
        expr = expand_defined(expr.strip())
        for n, v in list(defines.items()):
            expr = re.sub(rf"\b{re.escape(n)}\b", f"({v})", expr)
        expr = expr.replace("&&", " and ").replace("||", " or ")
        expr = re.sub(r"!(?!=)", " not ", expr)
        if re.search(r"[^0-9\s\(\)notandor<>!=+\-*/%]", expr):
            try:
                return bool(int(expr)) if expr.strip().isdigit() else bool(expr.strip())
            except Exception:
                return bool(expr.strip())
        try:
            return bool(eval(expr, {"__builtins__": {}}, {}))
        except Exception:
            return False

    while i < len(lines):
        raw, s = lines[i], lines[i].strip()
        if s.startswith("#macro "):
            name = s[7:].split()[0]
            body = []
            i += 1
            while i < len(lines) and not lines[i].strip().startswith("#endmacro"):
                body.append(lines[i]); i += 1
            if active():
                func_macros[name] = "\n".join(body)
            i += 1
            continue
        if s.startswith("#define "):
            if active():
                rest = s[8:].strip()
                m = re.match(r"([A-Za-z_]\w*)\(([^)]*)\)\s+(.*)$", rest)
                if m:
                    func_macros[m.group(1)] = (
                        [a.strip() for a in m.group(2).split(",") if a.strip()],
                        m.group(3),
                    )
                else:
                    p = rest.split(None, 1)
                    defines[p[0]] = p[1] if len(p) > 1 else "1"
            i += 1
            continue
        if s.startswith("#undef "):
            if active():
                n = s[7:].strip()
                defines.pop(n, None)
                func_macros.pop(n, None)
            i += 1
            continue
        if s.startswith("#ifdef "):
            n = s[7:].strip()
            stack.append(active() and (n in defines or n in func_macros))
            i += 1
            continue
        if s.startswith("#ifndef "):
            n = s[8:].strip()
            stack.append(active() and not (n in defines or n in func_macros))
            i += 1
            continue
        if s.startswith("#if "):
            stack.append(active() and eval_simple(s[4:]))
            i += 1
            continue
        if s.startswith("#elif "):
            if stack:
                prev = stack.pop()
                parent = all(stack) if stack else True
                stack.append(parent and (not prev) and eval_simple(s[6:]))
            i += 1
            continue
        if s == "#else":
            if stack:
                prev = stack.pop()
                parent = all(stack) if stack else True
                stack.append(parent and (not prev))
            i += 1
            continue
        if s == "#endif":
            if stack:
                stack.pop()
            i += 1
            continue
        if s.startswith("#error") and active():
            raise ValueError("macro #error: " + s[6:].strip())
        if s.startswith("#include") or s.startswith("#pragma"):
            i += 1
            continue
        if s.startswith("@OBF_STRIP"):
            i += 1
            while i < len(lines) and not lines[i].strip().startswith("@END"):
                i += 1
            i += 1
            continue
        if active():
            out.append(raw)
        i += 1

    text = "\n".join(out)

    def expand_once(t):
        for n, v in list(defines.items()):
            t = re.sub(rf"\b{re.escape(n)}\b", v, t)
        t = re.sub(
            r"#(?:str|stringify)\s*\(\s*([^)]+?)\s*\)",
            lambda m: '"' + m.group(1).strip().replace("\\", "\\\\").replace('"', '\\"') + '"',
            t,
        )
        for n, spec in list(func_macros.items()):
            if isinstance(spec, tuple):
                args, body = spec
                def repl(m, args=args, body=body):
                    av = [a.strip() for a in m.group(1).split(",")] if m.group(1).strip() else []
                    r = body
                    for a, val in zip(args, av + [""] * len(args)):
                        r = re.sub(rf"\b{re.escape(a)}\s*##\s*", val, r)
                        r = re.sub(rf"##\s*\b{re.escape(a)}\b", val, r)
                        r = re.sub(rf"\b{re.escape(a)}\b", val, r)
                    return r
                t = re.sub(rf"\b{re.escape(n)}\s*\(([^)]*)\)", repl, t)
            else:
                t = re.sub(rf"\b{re.escape(n)}\b", spec, t)
        return t

    for _ in range(max_passes):
        nxt = expand_once(text)
        if nxt == text:
            break
        text = nxt
    return text

def normalize(src: str) -> str:
    src = re.sub(r"--\[\[.*?\]\]", "", src, flags=re.DOTALL)
    src = re.sub(r"--[^\n]*", "", src)
    src = re.sub(r"^\s*#.*$", "", src, flags=re.MULTILINE)
    return src.strip()

def gen_opcode_map():
    pool = list(range(0x20, 0xC0))
    random.shuffle(pool)
    keys = ["LOAD", "MOVE", "CAT", "CLR", "RET", "HALT", "PROBE", "JUNK", "JMP", "NOP"]
    return {k: pool[i] for i, k in enumerate(keys)}

def light_mutate(words, OP):
    """Fast mutation: occasional junk only, no heavy CFG scramble."""
    ins = [words[i:i + 4] for i in range(0, len(words), 4)]
    out = []
    for inst in ins:
        if random.random() < 0.12:
            out.append([OP["JUNK"], random.randint(0, 5), random.randint(0, 7), 0])
        out.append(inst)
    flat = []
    for x in out:
        flat.extend(x)
    return flat

def compile_layer(payload: str, step: int = 96):
    step = max(32, step)
    pieces = [payload[i:i + step] for i in range(0, len(payload), step)] or [payload]
    consts = []
    for p in pieces:
        ck = random.randint(0x21, 0xDE)
        consts.append((b64e(rxor(p.encode("utf-8"), ck)), ck))

    OP = gen_opcode_map()
    master = R()

    code = [OP["PROBE"], 0, 0, 0]
    code += [OP["LOAD"], 1, 0, 0, OP["MOVE"], 0, 1, 0]
    for i in range(1, len(pieces)):
        code += [OP["LOAD"], 1, i, 0, OP["CAT"], 0, 0, 1]
        if i % 8 == 0:
            code += [OP["CLR"], 2, 6, 0]
    code += [OP["RET"], 0, 2, 0, OP["HALT"], 0, 0, 0]

    mutated = light_mutate(code, OP)
    packed = pack_instr(mutated)
    enc = rxor(packed, master)
    return consts, b64e(enc), master, OP

def emit_layer(consts, enc_b64, master, OP):
    N = {k: M() for k in (
        "fail", "hk", "id", "lcg", "probe", "roll", "b64", "dec", "run", "fetch", "K", "code", "junk"
    )}
    s1, s2 = R(), R()
    px = master ^ s1 ^ s2
    kt = "{" + ",".join(f"{{{d!r},{k}}}" for d, k in consts) + "}"

    a = []
    A = a.append
    A("(function(...)")
    A("local bit32=bit32 or bit")
    A("local tc=table.concat")
    A("local sc=string.char")
    A("local sb=string.byte")
    A("local typeof=typeof or type")
    A("local ls=loadstring or load")
    A(f"local function {N['fail']}() while true do end end")
    A(f"local function {N['hk']}()")
    A("local L={bit32.band,bit32.bxor,bit32.lshift,string.byte,string.char,pcall,rawget,rawequal,typeof,ls}")
    A("for i=1,#L do local f=L[i] if type(f)~=\"function\" then return false end end")
    A("return true end")
    A(f"local function {N['id']}()")
    A("local t={bit32.band,rawget,pcall}")
    A("for i=1,#t do if not rawequal(t[i],t[i]) then return false end end")
    A("return true end")
    A(f"local function {N['lcg']}(v,w)")
    A("v=(772109*v+99839573)%268435456")
    A("v=(943141*v+53826001)%268435456")
    A("w=(w+27317064)%268435456")
    A("return v,w end")
    A(f"local function {N['probe']}()")
    A(f"if not {N['hk']}() then {N['fail']}() end")
    A(f"if not {N['id']}() then {N['fail']}() end")
    A(f"local a,b={N['lcg']}({s1},{s2})")
    A(f"if a==0 then {N['fail']}() end")
    A(f"return bit32.bxor(a,b,{px}) end")
    A(f"local function {N['roll']}(data,key)")
    A("local nr={} local k=key%4294967296")
    A("for i=1,#data do k=(k*1664525+1013904223)%4294967296")
    A("nr[i]=sc(bit32.bxor(sb(data,i),bit32.rshift(k,16)%256,i%256)) end")
    A("return tc(nr) end")
    A(f"local function {N['b64']}(d)")
    A("local b='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'")
    A("d=string.gsub(d,'[^'..b..'=]','')")
    A("return (d:gsub('.',function(x) if x=='=' then return '' end")
    A("local r,f='',(b:find(x)-1)")
    A("for i=6,1,-1 do r=r..(f%2^i-f%2^(i-1)>0 and '1' or '0') end return r end)")
    A(":gsub('%d%d%d?%d?%d?%d?%d?%d?',function(x) if #x~=8 then return '' end local c=0")
    A("for i=1,8 do c=c*2+(x:sub(i,i)=='1' and 1 or 0) end return sc(c) end)) end")
    A(f"local {N['K']}={kt}")
    A(f"local function {N['dec']}(idx,extra)")
    A(f"local e={N['K']}[idx+1] if not e then return nil end")
    A(f"local raw={N['b64']}(e[1])")
    A(f"return {N['roll']}(raw,bit32.bxor(e[2],(extra or 0)%256)) end")
    A(f"local function {N['junk']}(a,b) return bit32.bxor((a or 0)+(b or 0),{R()}) end")
    A(f"local function {N['run']}()")
    A(f"local derived={N['probe']}()")
    A(f"local master=bit32.bxor({master},derived)")
    A(f"local enc={N['b64']}({enc_b64!r})")
    A(f"local plain={N['roll']}(enc,master)")
    A(f"local {N['code']}={{}}")
    A("for i=1,#plain,4 do if i+3>#plain then break end")
    A("local v=sb(plain,i)*16777216+sb(plain,i+1)*65536+sb(plain,i+2)*256+sb(plain,i+3)")
    A(f"{N['code']}[#{N['code']}+1]=v end")
    A("local R={} for i=0,31 do R[i]=nil end local PC=1")
    A(f"local function {N['fetch']}()")
    A(f"local b=PC if b>#{N['code']} then return {OP['HALT']},0,0,0 end")
    A(f"local op={N['code']}[b] local a={N['code']}[b+1] or 0")
    A(f"local bx={N['code']}[b+2] or 0 local c={N['code']}[b+3] or 0")
    A("PC=b+4 return op,a,bx,c end")
    A("while true do")
    A(f"local op,a,bx,c={N['fetch']}()")
    A(f"if op=={OP['PROBE']} then {N['probe']}()")
    A(f"elseif op=={OP['LOAD']} then R[a]={N['dec']}(bx,derived)")
    A(f"elseif op=={OP['MOVE']} then R[a]=R[bx]")
    A(f"elseif op=={OP['CAT']} then R[a]=tostring(R[bx] or \"\")..tostring(R[c] or \"\")")
    A(f"elseif op=={OP['CLR']} then for i=a,bx do R[i]=nil end")
    A(f"elseif op=={OP['JUNK']} or op=={OP['NOP']} then {N['junk']}(a,bx)")
    A(f"elseif op=={OP['JMP']} then local rel=bx if c==1 and rel>=0x8000 then rel=rel-0x10000 end PC=PC+rel*4")
    A(f"elseif op=={OP['RET']} then local src=R[a]")
    A(f"if type(src)~=\"string\" then {N['fail']}() end")
    A(f"for i=0,31 do if i~=a then R[i]=nil end end {N['K']}=nil {N['code']}=nil")
    A("local fn=ls(src) if not fn then error(\"18byt0\",0) end return fn")
    A(f"elseif op=={OP['HALT']} then break else {N['fail']}() end end end")
    A(f"local fn={N['run']}()")
    A("if type(fn)==\"function\" then return fn(...) end")
    A("return fn end)")
    return "\n".join(a)

def minify(s: str) -> str:
    return "\n".join(x.strip() for x in s.splitlines() if x.strip())

def choose_profile(n: int):
    """
    Adaptive speed profile by source size.
    returns (layers, chunk_step)
    """
    if n < 3000:
        return 2, 64
    if n < 20000:
        return 2, 128
    if n < 80000:
        return 1, 192
    return 1, 256

def build(src: str) -> str:
    layers, step = choose_profile(len(src))
    # always at least 1 layer
    c, e, m, op = compile_layer(src, step)
    code = "return " + emit_layer(c, e, m, op)
    for _ in range(layers - 1):
        # subsequent layers wrap previous with larger chunks
        c, e, m, op = compile_layer(code, max(step, 160))
        code = "return " + emit_layer(c, e, m, op)
    return minify(code)

def decompile_probe_fast(original: str, protected: str) -> dict:
    # very cheap probe
    score = 0
    issues = []
    cleaned = re.sub(r"\s+", "", original[:2000])
    if len(cleaned) > 20:
        w = cleaned[10:20]
        if w and w in protected:
            score += 20
            issues.append("leak")
    if len(original) > 200 and len(protected) < len(original) * 1.2:
        score += 15
        issues.append("thin")
    return {"score": score, "issues": issues, "verdict": "weak" if score >= 30 else "ok"}

def obfuscate(src: str) -> dict:
    t0 = time.time()
    src = preprocess_macros(src)
    src = normalize(src)
    if not src:
        raise ValueError("empty")
    layers, step = choose_profile(len(src))
    protected = build(src)
    probe = decompile_probe_fast(src, protected)
    # NO auto re-run (was the main slowdown). Only one pass.
    ms = int((time.time() - t0) * 1000)
    return {
        "result": protected,
        "level": layers,
        "probe": probe,
        "version": "v1.2-fast",
        "ms": ms,
        "chunk": step,
        "src_len": len(src),
        "out_len": len(protected),
    }

# -------------------- UI --------------------
HTML = r'''<!DOCTYPE html>
<html lang="ko"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>18byt0 v1.2 fast</title>
<style>
:root{--bg:#09090b;--p:#111113;--b:#27272a;--a:#a78bfa;--a2:#7c3aed;--t:#fafafa;--m:#a1a1aa;--ok:#22c55e}
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:Inter,system-ui,sans-serif;background:var(--bg);color:var(--t);min-height:100vh;display:flex;flex-direction:column}
header{padding:1rem 1.5rem;background:var(--p);border-bottom:1px solid var(--b);display:flex;align-items:center;gap:1rem;flex-wrap:wrap}
h1{font-size:1.3rem;font-weight:700;color:var(--a)}
.tag{font-size:.65rem;background:#2e1065;color:#ddd6fe;padding:.15rem .5rem;border-radius:999px}
main{flex:1;display:grid;grid-template-columns:1fr 1fr;gap:1rem;padding:1rem;max-width:1500px;margin:0 auto;width:100%}
.panel{background:var(--p);border:1px solid var(--b);border-radius:12px;display:flex;flex-direction:column;overflow:hidden}
.ph{padding:.7rem 1rem;background:#18181b;border-bottom:1px solid var(--b);font-size:.85rem;font-weight:600;display:flex;justify-content:space-between}
textarea{flex:1;background:#0c0c0e;color:#e4e4e7;border:none;padding:1rem;font-family:ui-monospace,monospace;font-size:.78rem;line-height:1.5;resize:none;outline:none}
.act{padding:.8rem;background:#18181b;border-top:1px solid var(--b);display:flex;gap:.5rem;flex-wrap:wrap}
button,.fl{background:var(--a2);color:#fff;border:none;padding:.5rem 1rem;border-radius:8px;font-weight:600;font-size:.82rem;cursor:pointer}
button:hover,.fl:hover{background:#6d28d9}button.s,.fl{background:#27272a}button.s:hover{background:#3f3f46}
input[type=file]{display:none}footer{text-align:center;padding:.7rem;font-size:.7rem;color:var(--m)}
.meta{font-size:.75rem;color:var(--m);padding:.5rem 1rem;border-bottom:1px solid var(--b)}
.ok{color:var(--ok)}
@media(max-width:900px){main{grid-template-columns:1fr}}
</style></head>
<body>
<header>
  <h1>18byt0</h1>
  <span class="tag">v1.2 fast · adaptive layers</span>
</header>
<main>
  <div class="panel">
    <div class="ph"><span>Input</span><span style="color:var(--m);font-size:.75rem">Lua / Luau</span></div>
    <textarea id="in" placeholder="코드 입력"></textarea>
    <div class="act">
      <label class="fl" for="f">업로드</label>
      <input type="file" id="f" accept=".lua,.luau,.txt">
      <button onclick="go()">난독화</button>
      <button class="s" onclick="clr()">초기화</button>
    </div>
  </div>
  <div class="panel">
    <div class="ph"><span>Output</span><span style="color:var(--m);font-size:.75rem">protected</span></div>
    <div class="meta" id="meta">ready · small=2layer · large=1layer</div>
    <textarea id="out" readonly></textarea>
    <div class="act">
      <button onclick="dl()">다운로드</button>
      <button class="s" onclick="cp()">복사</button>
    </div>
  </div>
</main>
<footer>18byt0 v1.2 · speed profile by size · no re-escalate · light mutation</footer>
<script>
const I=document.getElementById('in'),O=document.getElementById('out'),F=document.getElementById('f'),M=document.getElementById('meta');
F.onchange=e=>{const f=e.target.files[0];if(!f)return;const r=new FileReader();r.onload=ev=>I.value=ev.target.result;r.readAsText(f)};
async function go(){
  const c=I.value;if(!c.trim())return alert('코드 필요');O.value='...';M.textContent='working';
  try{
    const r=await fetch('/obfuscate',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({code:c})});
    const d=await r.json();
    if(d.error){O.value='Error: '+d.error;M.textContent='fail';return}
    O.value=d.result;
    M.innerHTML=`v1.2 · <span class="ok">${d.ms}ms</span> · layers ${d.level} · chunk ${d.chunk} · in ${d.src_len} → out ${d.out_len}`;
  }catch(e){O.value=''+e}
}
function clr(){I.value='';O.value='';F.value='';M.textContent='ready'}
function cp(){O.select();document.execCommand('copy');alert('ok')}
function dl(){const c=O.value;if(!c||c==='...'||c.startsWith('Error'))return;const b=new Blob([c],{type:'text/plain'});const a=document.createElement('a');a.href=URL.createObjectURL(b);a.download='protected_18byt0_v1.lua';a.click()}
</script>
</body></html>'''

@app.route("/")
def index():
    return render_template_string(HTML)

@app.route("/obfuscate", methods=["POST"])
def do_obfuscate():
    try:
        data = request.get_json(force=True)
        code = data.get("code", "")
        if not code.strip():
            return jsonify({"error": "empty"}), 400
        return jsonify(obfuscate(code))
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/upload", methods=["POST"])
def upload():
    if "file" not in request.files:
        return jsonify({"error": "no file"}), 400
    f = request.files["file"]
    try:
        content = f.read().decode("utf-8", errors="ignore")
        out = obfuscate(content)
        buf = io.BytesIO(out["result"].encode("utf-8"))
        buf.seek(0)
        return send_file(buf, mimetype="text/plain", as_attachment=True,
                         download_name="protected_18byt0_v1.lua")
    except Exception as e:
        return jsonify({"error": str(e)}), 500

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 10000)), debug=False)
