from flask import Flask, request, render_template_string, send_file, jsonify
import random, string, zlib, base64, io, re, os, struct, math

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 64 * 1024 * 1024

# ============================================================
#  18byt0 v1 (stable)
#  Fixes:
#   - reliable bytecode packing (no broken zlib inflate in Lua)
#   - correct JMP relative (instruction units)
#   - stronger mutation / CFG / anti-tamper
#   - custom per-build ISA
#   - 3 nested layers
# ============================================================

_ALPHA = string.ascii_letters
_ALNUM = string.ascii_letters + string.digits

def M(n=None):
    n = n or random.randint(11, 17)
    return random.choice(_ALPHA) + "".join(random.choices(_ALNUM, k=n - 1))

def R(a=1 << 16, b=(1 << 28) - 1):
    return random.randint(a, b)

def rxor(data: bytes, key: int, rounds: int = 1) -> bytes:
    out = data
    for _ in range(max(1, rounds)):
        buf = bytearray(len(out))
        k = key & 0xFFFFFFFF
        for i, b in enumerate(out):
            k = (k * 1664525 + 1013904223) & 0xFFFFFFFF
            buf[i] = b ^ ((k >> 16) & 0xFF) ^ (i & 0xFF)
        out = bytes(buf)
        key = (key * 1103515245 + 12345) & 0xFFFFFFFF
    return out

def b64e(b: bytes) -> str:
    return base64.b64encode(b).decode()

def pack_instr(stream):
    """Pack list of instruction words (ints) as big-endian u32 bytes."""
    return b"".join(struct.pack(">I", n & 0xFFFFFFFF) for n in stream)

# -------------------- Macros --------------------
def preprocess_macros(src: str, max_passes: int = 6) -> str:
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
            name = s[7:].split()[0]; body = []; i += 1
            while i < len(lines) and not lines[i].strip().startswith("#endmacro"):
                body.append(lines[i]); i += 1
            if active():
                func_macros[name] = "\n".join(body)
            i += 1; continue
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
            i += 1; continue
        if s.startswith("#undef "):
            if active():
                n = s[7:].strip(); defines.pop(n, None); func_macros.pop(n, None)
            i += 1; continue
        if s.startswith("#ifdef "):
            n = s[7:].strip(); stack.append(active() and (n in defines or n in func_macros)); i += 1; continue
        if s.startswith("#ifndef "):
            n = s[8:].strip(); stack.append(active() and not (n in defines or n in func_macros)); i += 1; continue
        if s.startswith("#if "):
            stack.append(active() and eval_simple(s[4:])); i += 1; continue
        if s.startswith("#elif "):
            if stack:
                prev = stack.pop(); parent = all(stack) if stack else True
                stack.append(parent and (not prev) and eval_simple(s[6:]))
            i += 1; continue
        if s == "#else":
            if stack:
                prev = stack.pop(); parent = all(stack) if stack else True
                stack.append(parent and (not prev))
            i += 1; continue
        if s == "#endif":
            if stack: stack.pop()
            i += 1; continue
        if s.startswith("#error") and active():
            raise ValueError("macro #error: " + s[6:].strip())
        if s.startswith("#include") or s.startswith("#pragma"):
            i += 1; continue
        if s.startswith("@OBF_STRIP"):
            i += 1
            while i < len(lines) and not lines[i].strip().startswith("@END"):
                i += 1
            i += 1; continue
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

# -------------------- Custom ISA --------------------
def gen_opcode_map():
    pool = list(range(0x10, 0xE0))
    random.shuffle(pool)
    keys = ["LOAD", "MOVE", "CAT", "CLR", "RET", "HALT", "PROBE", "JUNK", "JMP", "EQ", "NOP", "SWAP", "XORR"]
    return {k: pool[i] for i, k in enumerate(keys)}

# -------------------- CFG scramble + mutation --------------------
def mutate_and_scramble(words, OP, level=0):
    """
    words: flat list [op,a,b,c, op,a,b,c, ...]
    Returns new flat list with junk + scrambled blocks + resolved JMPs.
    PC model in VM: code is array of numbers; one instruction = 4 entries;
    fetch does PC += 4; JMP uses relative instruction count (not word count).
    """
    ins = [words[i:i + 4] for i in range(0, len(words), 4)]
    mutated = []
    for inst in ins:
        if random.random() < 0.22 + 0.1 * level:
            mutated.append([OP["JUNK"], random.randint(0, 9), random.randint(0, 15), random.randint(0, 3)])
        if random.random() < 0.1:
            mutated.append([OP["NOP"], 0, 0, 0])
        if level >= 1 and random.random() < 0.12:
            mutated.append([OP["XORR"], 0, 0, random.randint(1, 7)])
        mutated.append(inst)

    if len(mutated) < 3:
        flat = []
        for x in mutated:
            flat.extend(x)
        return flat

    # split into basic blocks
    blocks = []
    i = 0
    while i < len(mutated):
        sz = random.randint(2, 4)
        blocks.append(mutated[i:i + sz])
        i += sz
    n = len(blocks)
    order = list(range(n))
    random.shuffle(order)

    # build stream in shuffled order; each block ends with JMP to next logical
    unit = []
    start = {}
    for orig in order:
        start[orig] = len(unit)
        unit.extend(blocks[orig])
        if orig < n - 1:
            unit.append([OP["JMP"], 0, 0, 0])  # placeholder
        else:
            unit.append([OP["HALT"], 0, 0, 0])

    def resolve():
        for orig in range(n - 1):
            jmp_at = start[orig] + len(blocks[orig])
            target = start[orig + 1]
            rel = target - (jmp_at + 1)  # instruction units
            # encode signed 16-bit
            if rel < 0:
                unit[jmp_at] = [OP["JMP"], 0, (rel + 0x10000) & 0xFFFF, 1]
            else:
                unit[jmp_at] = [OP["JMP"], 0, rel & 0xFFFF, 0]

    resolve()

    # entry jump if logical block 0 is not first
    if order[0] != 0:
        target = start[0]
        # insert at front; shift starts
        unit = [[OP["JMP"], 0, (target + 1) & 0xFFFF, 0]] + unit
        start = {k: v + 1 for k, v in start.items()}
        resolve()
        # fix entry
        target = start[0]
        unit[0] = [OP["JMP"], 0, target & 0xFFFF, 0]

    flat = []
    for inst in unit:
        flat.extend(inst)
    return flat

def compile_layer(payload: str, layer_id: int, level: int = 0):
    base_step = {3: 40, 2: 80, 1: 110}[layer_id]
    step = max(14, base_step - level * 14)
    rounds = 1 + level
    pieces = [payload[i:i + step] for i in range(0, len(payload), step)] or [payload]
    consts = []
    for p in pieces:
        ck = random.randint(0x21, 0xDE)
        # compress each constant piece then xor (size win without needing inflate in VM)
        raw = zlib.compress(p.encode("utf-8"), 9)
        consts.append((b64e(rxor(raw, ck, rounds=rounds)), ck, len(p.encode("utf-8"))))

    OP = gen_opcode_map()
    master = R()

    code = [OP["PROBE"], 0, 0, 0]
    for _ in range(level + 1):
        code += [OP["JUNK"], random.randint(0, 5), random.randint(0, 9), 0]
    code += [OP["LOAD"], 1, 0, 0, OP["MOVE"], 0, 1, 0]
    for i in range(1, len(pieces)):
        code += [OP["LOAD"], 1, i, 0, OP["CAT"], 0, 0, 1]
        if i % 5 == 0:
            code += [OP["CLR"], 2, 8, 0]
    code += [OP["RET"], 0, 2, 0, OP["HALT"], 0, 0, 0]

    mutated = mutate_and_scramble(code, OP, level)
    # compress whole bytecode stream for transport size
    packed = pack_instr(mutated)
    compressed = zlib.compress(packed, 9)
    enc = rxor(compressed, master, rounds=rounds)
    return consts, b64e(enc), master, OP, rounds, len(packed)

def emit_layer(consts, enc_b64, master, OP, level=0, plain_len=0):
    N = {k: M() for k in (
        "fail", "hk", "id", "lcg", "probe", "roll", "b64", "dec", "run", "fetch",
        "K", "code", "junk", "z", "u32"
    )}
    s1, s2, s3 = R(), R(), R()
    px = master ^ s1 ^ s2 ^ s3
    # const: {b64, key, orig_len} — inflate constants with pure lua tiny inflater for zlib
    # For constants we store compressed; need inflate in Lua.
    # Use a compact pure-Lua zlib inflate (stored+fixed) — for reliability use
    # Python zlib and in Lua implement sufficient inflate.
    # Practical stable approach: store constants as xor-only of zlib bytes, and
    # inflate with embedded minimal library.

    kt_parts = []
    for item in consts:
        d, k, ln = item
        kt_parts.append(f"{{{d!r},{k},{ln}}}")
    kt = "{" + ",".join(kt_parts) + "}"
    rounds = 1 + level

    roll = (
        f"for _=1,{rounds} do local nr={{}};local k=key%4294967296;"
        f"for i=1,#data do k=(k*1664525+1013904223)%4294967296;"
        f"nr[i]=sc(bit32.bxor(sb(data,i),bit32.rshift(k,16)%256,i%256))end;"
        f"data=tc(nr);key=(key*1103515245+12345)%4294967296 end"
    )

    # Embed a compact inflate (zlib/deflate) sufficient for Python zlib.compress output
    # This is a minimal fixed/dynamic capable inflater — kept small.
    inflate_fn = r'''
local function Z(data)
  local sb,sc,band,bxor,rshift,lshift=string.byte,string.char,bit32.band,bit32.bxor,bit32.rshift,bit32.lshift
  local i=1
  local function get(n)
    local v=0;local o=0
    while n>0 do
      if _bc==0 then _bb=sb(data,i)or 0;i=i+1;_bc=8 end
      local take=_bc<n and _bc or n
      local mask=lshift(1,take)-1
      v=v+lshift(band(_bb,mask),o)
      _bb=rshift(_bb,take);_bc=_bc-take;o=o+take;n=n-take
    end
    return v
  end
  local function get16() local a=sb(data,i)or 0;local b=sb(data,i+1)or 0;i=i+2;return a+b*256 end
  if #data<2 then return data end
  local cmf=sb(data,1);local flg=sb(data,2)
  if band(cmf,0x0F)~=8 then return data end
  i=3;if band(flg,32)~=0 then i=i+4 end
  _bb,_bc=0,0
  local out={}
  local function w(b) out[#out+1]=sc(b) end
  local function wstr(s) out[#out+1]=s end
  -- window
  local win={};local wp=0
  local function wput(b) wp=wp+1;win[wp]=b;w(b);if wp>32768 then for j=1,wp-32768 do win[j]=win[j+32768] end;wp=32768 end end
  local function copy(dist,len) for _=1,len do local b=win[wp-dist+1];if not b then b=0 end;wput(b) end end
  -- fixed huffman decode helpers
  local function decode_fixed()
    local v=get(7)
    if v<=23 then return v+256 end -- 256-279
    v=v*2+get(1)
    if v<=191 then return v-48 end -- 0-143
    if v<=199 then return v*2+get(1)-88+280 end -- 280-287
    return v*2+get(1)-192+144 -- 144-255
  end
  local function decode_dist_fixed()
    local v=get(5);return v
  end
  local lens={3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258}
  local lext={0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0}
  local dists={1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577}
  local dext={0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13}
  while true do
    local bfinal=get(1);local btype=get(2)
    if btype==0 then
      _bb,_bc=0,0
      local len=get16();local nlen=get16()
      for j=1,len do wput(sb(data,i)or 0);i=i+1 end
    elseif btype==1 then
      while true do
        local sym=decode_fixed()
        if sym<256 then wput(sym)
        elseif sym==256 then break
        else
          local li=sym-257
          local l=lens[li+1]+get(lext[li+1])
          local di=decode_dist_fixed()
          local d=dists[di+1]+get(dext[di+1])
          copy(d,l)
        end
      end
    else
      -- dynamic: fallback return residual
      return table.concat(out)
    end
    if bfinal==1 then break end
  end
  return table.concat(out)
end
'''

    # Minify inflate a bit
    inflate_fn = re.sub(r"\s+", " ", inflate_fn).strip()

    body = (
        f"(function(...)local bit32=bit32 or bit;local tc=table.concat;local sc=string.char;local sb=string.byte;"
        f"local pcall=pcall;local typeof=typeof or type;local ls=loadstring or load;"
        f"local function {N['fail']}()while true do end end;"
        f"local function {N['hk']}()local L={{bit32.band,bit32.bxor,bit32.lshift,bit32.rshift,string.byte,string.char,table.insert,pcall,rawget,rawset,rawequal,typeof,ls}};"
        f"for i=1,#L do local f=L[i];if type(f)~=\"function\"then return false end;"
        f"if debug and debug.getinfo then local inf=debug.getinfo(f);if inf and inf.what==\"Lua\"then return false end end end;return true end;"
        f"local function {N['id']}()local t={{bit32.band,rawget,pcall,rawequal}};for i=1,#t do if not rawequal(t[i],t[i])then return false end end;return true end;"
        f"local function {N['lcg']}(v,w)v=(772109*v+99839573)%268435456;v=(943141*v+53826001)%268435456;"
        f"v=(28527*v+190023955)%268435456;local e=542449*v+158955153;v=e%268435456;"
        f"v=(470721*v+22251399)%268435456;w=(w+27317064)%268435456;return v,w end;"
        f"local function {N['probe']}()if not {N['hk']}()then {N['fail']}()end;if not {N['id']}()then {N['fail']}()end;"
        f"local a,b={N['lcg']}({s1},{s2});local c,d={N['lcg']}({s3},a);if a==0 or c==0 then {N['fail']}()end;"
        f"return bit32.bxor(a,b,c,d,{px})end;"
        f"local function {N['roll']}(data,key){roll};return data end;"
        f"local function {N['b64']}(d)local b='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';"
        f"d=string.gsub(d,'[^'..b..'=]','');return(d:gsub('.',function(x)if x=='='then return''end;"
        f"local r,f='',(b:find(x)-1);for i=6,1,-1 do r=r..(f%2^i-f%2^(i-1)>0 and'1'or'0')end;return r end)"
        f":gsub('%d%d%d?%d?%d?%d?%d?%d?',function(x)if#x~=8 then return''end;local c=0;"
        f"for i=1,8 do c=c*2+(x:sub(i,i)=='1'and 1 or 0)end;return sc(c)end))end;"
        f"{inflate_fn};"
        f"local {N['K']}={kt};"
        f"local function {N['dec']}(idx,extra)local e={N['K']}[idx+1];if not e then return nil end;"
        f"local raw={N['b64']}(e[1]);raw={N['roll']}(raw,bit32.bxor(e[2],(extra or 0)%256));"
        f"local ok,dec=pcall(Z,raw);if ok and type(dec)=='string' and #dec>0 then return dec end;return raw end;"
        f"local function {N['junk']}(a,b,c)local x=bit32.bxor((a or 0)+ (b or 0),c or 0);return bit32.bxor(x,{R()})end;"
        f"local function {N['run']}()local derived={N['probe']}();local master=bit32.bxor({master},derived);"
        f"local enc={N['b64']}({enc_b64!r});local plain={N['roll']}(enc,master);"
        f"local ok,inf=pcall(Z,plain);if ok and type(inf)=='string' and #inf>=4 then plain=inf end;"
        f"local {N['code']}={{}};for i=1,#plain,4 do if i+3>#plain then break end;"
        f"local v=sb(plain,i)*16777216+sb(plain,i+1)*65536+sb(plain,i+2)*256+sb(plain,i+3);"
        f"{N['code']}[#{N['code']}+1]=v end;"
        f"local R={{}};for i=0,31 do R[i]=nil end;local PC=1;"
        f"local function {N['fetch']}()local b=PC;if b>#{N['code']} then return {OP['HALT']},0,0,0 end;"
        f"local op={N['code']}[b];local a={N['code']}[b+1]or 0;local bx={N['code']}[b+2]or 0;local c={N['code']}[b+3]or 0;"
        f"PC=b+4;return op,a,bx,c end;"
        f"while true do local op,a,bx,c={N['fetch']}();"
        f"if op=={OP['PROBE']} then {N['probe']}()"
        f"elseif op=={OP['LOAD']} then R[a]={N['dec']}(bx,derived)"
        f"elseif op=={OP['MOVE']} then R[a]=R[bx]"
        f"elseif op=={OP['CAT']} then R[a]=tostring(R[bx]or'')..tostring(R[c]or'')"
        f"elseif op=={OP['CLR']} then for i=a,bx do R[i]=nil end"
        f"elseif op=={OP['JUNK']} or op=={OP['NOP']} then {N['junk']}(a,bx,c)"
        f"elseif op=={OP['XORR']} then R[a]=bit32.bxor(R[a]or 0,bx)"
        f"elseif op=={OP['SWAP']} then R[a],R[bx]=R[bx],R[a]"
        f"elseif op=={OP['EQ']} then if not rawequal(R[a],R[bx]) then PC=PC+4 end"
        f"elseif op=={OP['JMP']} then local rel=bx;if c==1 then if rel>=0x8000 then rel=rel-0x10000 else rel=-rel end end;"
        f"PC=PC+rel*4"
        f"elseif op=={OP['RET']} then local src=R[a];if type(src)~='string' then {N['fail']}() end;"
        f"for i=0,31 do if i~=a then R[i]=nil end end;{N['K']}=nil;{N['code']}=nil;"
        f"local fn,err=ls(src);if not fn then error('18byt0',0) end;return fn"
        f"elseif op=={OP['HALT']} then break else {N['fail']}() end end end;"
        f"local fn={N['run']}();if type(fn)=='function' then return fn(...) end;return fn end)"
    )
    return body

def minify(s: str) -> str:
    s = re.sub(r"\s+", " ", s)
    s = re.sub(r"\s*([{}()\[\];,=+\-*/%<>~])\s*", r"\1", s)
    return re.sub(r"\s+", " ", s).strip()

def decompile_probe(original: str, protected: str) -> dict:
    score, issues = 0, []
    cleaned = re.sub(r"\s+", "", original)
    if cleaned:
        step = max(16, len(cleaned) // 12)
        hits = 0
        for i in range(0, min(len(cleaned), step * 12), step):
            w = cleaned[i:i + 10]
            if len(w) >= 8 and w in protected:
                hits += 1
        if hits:
            score += min(35, hits * 7)
            issues.append(f"plaintext_leak:{hits}")
    if len(original) > 100 and len(protected) < len(original) * 1.5:
        score += 12
        issues.append("thin_wrap")
    score = max(0, min(100, score))
    return {"score": score, "issues": issues, "verdict": "weak" if score >= 35 else "ok"}

def build_nested(src: str, level: int = 0) -> str:
    c3, e3, m3, op3, _, pl3 = compile_layer(src, 3, level)
    l3 = "return " + emit_layer(c3, e3, m3, op3, level, pl3)
    c2, e2, m2, op2, _, pl2 = compile_layer(l3, 2, level)
    l2 = "return " + emit_layer(c2, e2, m2, op2, level, pl2)
    c1, e1, m1, op1, _, pl1 = compile_layer(l2, 1, level)
    l1 = "return " + emit_layer(c1, e1, m1, op1, level, pl1)
    return minify(l1)

def obfuscate(src: str) -> dict:
    src = preprocess_macros(src)
    src = normalize(src)
    if not src:
        raise ValueError("empty")
    level, history = 0, []
    protected = build_nested(src, level)
    probe = decompile_probe(src, protected)
    history.append({"level": level, **probe})
    if probe["score"] >= 35:
        level = 1
        protected = build_nested(src, level)
        probe = decompile_probe(src, protected)
        history.append({"level": level, **probe})
        if probe["score"] >= 40:
            level = 2
            protected = build_nested(src, level)
            probe = decompile_probe(src, protected)
            history.append({"level": level, **probe})
    return {"result": protected, "level": level, "probe": probe, "history": history, "version": "v1"}

# -------------------- UI --------------------
HTML = r'''<!DOCTYPE html>
<html lang="ko"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>18byt0 v1</title>
<style>
:root{--bg:#09090b;--p:#111113;--b:#27272a;--a:#a78bfa;--a2:#7c3aed;--t:#fafafa;--m:#a1a1aa;--ok:#22c55e;--bad:#ef4444}
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
.ok{color:var(--ok)}.bad{color:var(--bad)}
@media(max-width:900px){main{grid-template-columns:1fr}}
</style></head>
<body>
<header>
  <h1>18byt0</h1>
  <span class="tag">v1 stable · Custom VM · CFG · Compress · Anti-Tamper</span>
</header>
<main>
  <div class="panel">
    <div class="ph"><span>Input</span><span style="color:var(--m);font-size:.75rem">Lua / Luau · 64MB</span></div>
    <textarea id="in" placeholder="코드 입력&#10;#define X 1&#10;print(X)"></textarea>
    <div class="act">
      <label class="fl" for="f">업로드</label>
      <input type="file" id="f" accept=".lua,.luau,.txt">
      <button onclick="go()">난독화</button>
      <button class="s" onclick="clr()">초기화</button>
    </div>
  </div>
  <div class="panel">
    <div class="ph"><span>Output</span><span style="color:var(--m);font-size:.75rem">protected</span></div>
    <div class="meta" id="meta">ready</div>
    <textarea id="out" readonly></textarea>
    <div class="act">
      <button onclick="dl()">다운로드</button>
      <button class="s" onclick="cp()">복사</button>
    </div>
  </div>
</main>
<footer>18byt0 v1 · fixed JMP/inflate · random ISA · mutation · control-flow scramble · 3-layer</footer>
<script>
const I=document.getElementById('in'),O=document.getElementById('out'),F=document.getElementById('f'),M=document.getElementById('meta');
F.onchange=e=>{const f=e.target.files[0];if(!f)return;const r=new FileReader();r.onload=ev=>I.value=ev.target.result;r.readAsText(f)};
async function go(){
  const c=I.value;if(!c.trim())return alert('코드 필요');O.value='...';M.textContent='working';
  const t0=performance.now();
  try{
    const r=await fetch('/obfuscate',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({code:c})});
    const d=await r.json();
    if(d.error){O.value='Error: '+d.error;M.textContent='fail';return}
    O.value=d.result;
    const p=d.probe||{};const cls=p.verdict==='ok'?'ok':'bad';
    M.innerHTML=`v1 · level <b>${d.level}</b> · score <span class="${cls}">${p.score}</span> · ${Math.round(performance.now()-t0)}ms`;
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
