/* =========================================================================
 * 별난 계산기 (Crazy Calculator) — script.js
 *
 *   [1] MathCore : 토크나이저 / 파서 / 평가기 + 특수 수학 함수
 *   [2] Grapher  : HTML5 Canvas 좌표평면 & 곡선 렌더링
 *   [3] WeirdUI  : 이상한 유저 인터페이스 제어 (트롤링 강도 조절 가능)
 *   [4] Wiring   : 이벤트 연결
 *
 * 외부 라이브러리 없음. 순수 Vanilla JS.
 * ========================================================================= */
(function () {
'use strict';

/* =========================================================================
 * [1] MathCore
 * ========================================================================= */
const MathCore = (function () {

  /* ---------- 1-1. 특수 함수들 ---------- */

  // 람다 근사 감마 함수 (Lanczos, g=7, n=9)
  const LANCZOS = [
    0.99999999999980993, 676.5203681218851, -1259.1392167224028,
    771.32342877765313, -176.61502916214059, 12.507343278686905,
    -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7
  ];
  function gamma(z) {
    if (z < 0.5) {
      // 반사 공식: Γ(z)Γ(1-z) = π / sin(πz)
      return Math.PI / (Math.sin(Math.PI * z) * gamma(1 - z));
    }
    z -= 1;
    let x = LANCZOS[0];
    for (let i = 1; i < 9; i++) x += LANCZOS[i] / (z + i);
    const t = z + 7.5;
    return Math.sqrt(2 * Math.PI) * Math.pow(t, z + 0.5) * Math.exp(-t) * x;
  }

  function factorial(n) {
    if (Number.isInteger(n) && n >= 0) {
      if (n > 170) return Infinity;           // double 표현 한계
      let r = 1;
      for (let i = 2; i <= n; i++) r *= i;
      return r;
    }
    if (Number.isInteger(n) && n < 0) throw new CalcError('음의 정수의 계승은 없습니다 (∞으로 도망갔어요)');
    return gamma(n + 1);                      // 실수 계승은 감마로
  }

  // --- 소수 관련 ---
  const SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

  function powMod(base, exp, mod) {
    let r = 1n; base %= mod;
    while (exp > 0n) {
      if (exp & 1n) r = (r * base) % mod;
      base = (base * base) % mod;
      exp >>= 1n;
    }
    return r;
  }

  // 결정적 밀러-라빈 (n < 3.3e24 범위에서 위 12개 밑수면 확정)
  function isPrime(n) {
    if (!Number.isFinite(n) || !Number.isInteger(n)) {
      throw new CalcError('소수 판별은 정수만 됩니다');
    }
    if (n > Number.MAX_SAFE_INTEGER) throw new CalcError('숫자가 너무 큽니다 (2^53 이하로)');
    if (n < 2) return false;
    for (const p of SMALL_PRIMES) {
      if (n === p) return true;
      if (n % p === 0) return false;
    }
    const N = BigInt(n);
    let d = N - 1n, r = 0n;
    while ((d & 1n) === 0n) { d >>= 1n; r++; }
    outer:
    for (const a of SMALL_PRIMES) {
      let x = powMod(BigInt(a), d, N);
      if (x === 1n || x === N - 1n) continue;
      for (let i = 1n; i < r; i++) {
        x = (x * x) % N;
        if (x === N - 1n) continue outer;
      }
      return false;
    }
    return true;
  }

  // 에라토스테네스 체 (캐시해서 재사용)
  const SIEVE_MAX = 5_000_000;
  let sieveLimit = 0;
  let sieveFlags = null;   // Uint8Array: 1 = 합성수
  let sieveCount = null;   // Int32Array: π(i)

  function buildSieve(limit) {
    limit = Math.max(1000, Math.min(SIEVE_MAX, limit));
    if (limit <= sieveLimit) return;
    limit = Math.min(SIEVE_MAX, Math.max(limit, sieveLimit * 2));
    const flags = new Uint8Array(limit + 1);
    for (let i = 2; i * i <= limit; i++) {
      if (!flags[i]) for (let j = i * i; j <= limit; j += i) flags[j] = 1;
    }
    const count = new Int32Array(limit + 1);
    let c = 0;
    for (let i = 2; i <= limit; i++) { if (!flags[i]) c++; count[i] = c; }
    sieveFlags = flags; sieveCount = count; sieveLimit = limit;
  }

  // 소수 계량 함수 π(x) : x 이하의 소수 개수
  function primePi(x) {
    if (!Number.isFinite(x)) throw new CalcError('π(x)에 이상한 값이 들어왔습니다');
    const n = Math.floor(x);
    if (n < 2) return 0;
    if (n > SIEVE_MAX) throw new CalcError('π(x)는 ' + SIEVE_MAX.toLocaleString() + ' 이하까지만 셉니다 (컴퓨터가 웁니다)');
    buildSieve(n);
    return sieveCount[n];
  }

  function nextPrime(n) {
    let k = Math.floor(n) + 1;
    if (k < 2) return 2;
    while (!isPrime(k)) k++;
    return k;
  }

  function nthPrime(k) {
    if (!Number.isInteger(k) || k < 1) throw new CalcError('prime(k)의 k는 1 이상 정수');
    if (k > 200000) throw new CalcError('k가 너무 큽니다 (200000 이하)');
    let n = 1, found = 0;
    while (found < k) { n++; if (isPrime(n)) found++; }
    return n;
  }

  function primeFactors(n) {
    if (!Number.isInteger(n)) throw new CalcError('인수분해는 정수만 됩니다');
    let m = Math.abs(n);
    if (m < 2) return [];
    const out = [];
    for (let p = 2; p * p <= m; p += (p === 2 ? 1 : 2)) {
      while (m % p === 0) { out.push(p); m /= p; }
    }
    if (m > 1) out.push(m);
    return out;
  }

  function gcd(a, b) {
    a = Math.abs(Math.trunc(a)); b = Math.abs(Math.trunc(b));
    while (b) { const t = a % b; a = b; b = t; }
    return a;
  }

  // --- 리만 제타 함수 ζ(s) (실수 s) ---
  // Euler–Maclaurin 공식 + s < 1/2 구간은 함수방정식으로 반사
  const B2K = [1/6, -1/30, 1/42, -1/30, 5/66, -691/2730, 7/6];
  function zeta(s) {
    if (!Number.isFinite(s)) return NaN;
    if (Math.abs(s - 1) < 1e-12) return Infinity;              // 조화급수, 발산
    if (s === 0) return -0.5;
    // 자명한 영점: ζ(-2) = ζ(-4) = ... = 0
    if (s < 0 && Number.isInteger(s) && s % 2 === 0) return 0;

    if (s < 0.5) {
      // ζ(s) = 2^s π^(s-1) sin(πs/2) Γ(1-s) ζ(1-s)
      const r = Math.pow(2, s) * Math.pow(Math.PI, s - 1)
              * Math.sin(Math.PI * s / 2) * gamma(1 - s) * zeta(1 - s);
      return Number.isFinite(r) ? r : NaN;
    }

    const N = 24, M = 7;
    let sum = 0;
    for (let n = 1; n < N; n++) sum += Math.pow(n, -s);
    sum += Math.pow(N, 1 - s) / (s - 1);
    sum += 0.5 * Math.pow(N, -s);

    let poch = 1, idx = 0;                       // s(s+1)...(s+2k-2)
    for (let k = 1; k <= M; k++) {
      const need = 2 * k - 1;
      while (idx < need) { poch *= (s + idx); idx++; }
      sum += (B2K[k - 1] / factorial(2 * k)) * poch * Math.pow(N, -s - 2 * k + 1);
    }
    return sum;
  }

  /* ---------- 1-2. 에러 타입 ---------- */
  class CalcError extends Error {}

  /* ---------- 1-3. 토크나이저 ---------- */
  const SYMBOL_MAP = { '×': '*', '÷': '/', '−': '-', '＋': '+', '·': '*' };

  function tokenize(src) {
    const s = src.replace(/[×÷−＋·]/g, (c) => SYMBOL_MAP[c]);
    const tokens = [];
    let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (c === ' ' || c === '\t' || c === '\n') { i++; continue; }

      if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(s[i + 1] || ''))) {
        const m = /^[0-9]*\.?[0-9]+([eE][+-]?[0-9]+)?/.exec(s.slice(i));
        tokens.push({ t: 'num', v: parseFloat(m[0]) });
        i += m[0].length;
        continue;
      }
      if (/[A-Za-z_πτ√∞]/.test(c)) {
        if (c === 'π') { tokens.push({ t: 'id', v: 'pi' }); i++; continue; }
        if (c === 'τ') { tokens.push({ t: 'id', v: 'tau' }); i++; continue; }
        if (c === '∞') { tokens.push({ t: 'id', v: 'inf' }); i++; continue; }
        if (c === '√') { tokens.push({ t: 'id', v: 'sqrt' }); i++; continue; }
        const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(s.slice(i));
        tokens.push({ t: 'id', v: m[0].toLowerCase() });
        i += m[0].length;
        continue;
      }
      if ('+-*/^%!'.includes(c)) { tokens.push({ t: 'op', v: c }); i++; continue; }
      if (c === '(' || c === '[') { tokens.push({ t: 'lp' }); i++; continue; }
      if (c === ')' || c === ']') { tokens.push({ t: 'rp' }); i++; continue; }
      if (c === ',') { tokens.push({ t: 'comma' }); i++; continue; }

      throw new CalcError('이게 뭐죠? → "' + c + '"');
    }
    return tokens;
  }

  /* ---------- 1-4. 상수 & 함수 테이블 ---------- */
  const CONSTS = {
    pi: Math.PI, tau: Math.PI * 2, e: Math.E,
    inf: Infinity, phi: (1 + Math.sqrt(5)) / 2,
    // 오일러-마스케로니 상수 (덤)
    gammaconst: 0.5772156649015329
  };

  function need(name, args, min, max) {
    if (args.length < min || args.length > max) {
      throw new CalcError(name + '() 인자 개수가 맞지 않습니다');
    }
  }

  const FUNCS = {
    // 로그 / 지수
    ln:    (a) => { need('ln', a, 1, 1);    return safeLog(a[0], Math.E); },
    log:   (a) => { need('log', a, 1, 2);   return a.length === 1 ? safeLog(a[0], 10) : safeLog(a[0], a[1]); },
    log10: (a) => { need('log10', a, 1, 1); return safeLog(a[0], 10); },
    log2:  (a) => { need('log2', a, 1, 1);  return safeLog(a[0], 2); },
    exp:   (a) => { need('exp', a, 1, 1);   return Math.exp(a[0]); },
    pow:   (a) => { need('pow', a, 2, 2);   return Math.pow(a[0], a[1]); },
    sqrt:  (a) => { need('sqrt', a, 1, 1);  if (a[0] < 0) throw new CalcError('음수의 제곱근은 허수입니다 (여긴 실수 세계)'); return Math.sqrt(a[0]); },
    cbrt:  (a) => { need('cbrt', a, 1, 1);  return Math.cbrt(a[0]); },
    abs:   (a) => { need('abs', a, 1, 1);   return Math.abs(a[0]); },

    // 삼각 / 쌍곡
    sin: (a) => Math.sin(a[0]),   cos: (a) => Math.cos(a[0]),   tan: (a) => Math.tan(a[0]),
    asin:(a) => Math.asin(a[0]),  acos:(a) => Math.acos(a[0]),  atan:(a) => Math.atan(a[0]),
    sinh:(a) => Math.sinh(a[0]),  cosh:(a) => Math.cosh(a[0]),  tanh:(a) => Math.tanh(a[0]),
    atan2:(a) => { need('atan2', a, 2, 2); return Math.atan2(a[0], a[1]); },

    // 반올림 / 잡다
    floor:(a) => Math.floor(a[0]), ceil:(a) => Math.ceil(a[0]),
    round:(a) => Math.round(a[0]), sign:(a) => Math.sign(a[0]),
    trunc:(a) => Math.trunc(a[0]),
    min:  (a) => Math.min.apply(null, a), max: (a) => Math.max.apply(null, a),
    mod:  (a) => { need('mod', a, 2, 2); return a[0] - a[1] * Math.floor(a[0] / a[1]); },
    gcd:  (a) => { need('gcd', a, 2, 2); return gcd(a[0], a[1]); },
    lcm:  (a) => { need('lcm', a, 2, 2); const g = gcd(a[0], a[1]); return g ? Math.abs(a[0] * a[1]) / g : 0; },

    // 감마 / 계승
    fact:     (a) => { need('fact', a, 1, 1); return factorial(a[0]); },
    factorial:(a) => { need('factorial', a, 1, 1); return factorial(a[0]); },
    gamma:    (a) => { need('gamma', a, 1, 1); return gamma(a[0]); },

    // 난수
    rand:   (a) => randomIn(a),
    random: (a) => randomIn(a),
    randint:(a) => { need('randint', a, 2, 2); const lo = Math.ceil(Math.min(a[0], a[1])), hi = Math.floor(Math.max(a[0], a[1])); return lo + Math.floor(Math.random() * (hi - lo + 1)); },

    // 소수
    isprime:  (a) => { need('isprime', a, 1, 1); return isPrime(a[0]) ? 1 : 0; },
    primepi:  (a) => { need('primepi', a, 1, 1); return primePi(a[0]); },
    pcount:   (a) => { need('pcount', a, 1, 1); return primePi(a[0]); },
    nextprime:(a) => { need('nextprime', a, 1, 1); return nextPrime(a[0]); },
    prime:    (a) => { need('prime', a, 1, 1); return nthPrime(a[0]); },

    // 제타
    zeta: (a) => { need('zeta', a, 1, 1); return zeta(a[0]); }
  };

  function randomIn(a) {
    if (a.length === 0) return Math.random();
    if (a.length === 1) return Math.random() * a[0];
    const lo = Math.min(a[0], a[1]), hi = Math.max(a[0], a[1]);
    return lo + Math.random() * (hi - lo);
  }

  function safeLog(x, base) {
    if (x === 0) throw new CalcError('log(0)은 -∞ 입니다. 진심인가요?');
    if (x < 0)   throw new CalcError('음수에 로그를 씌우면 실수 세계가 무너집니다');
    if (base === 10) return Math.log10(x);
    if (base === 2)  return Math.log2(x);
    if (base === Math.E) return Math.log(x);
    if (base <= 0 || base === 1) throw new CalcError('로그의 밑이 이상합니다');
    return Math.log(x) / Math.log(base);
  }

  /* ---------- 1-5. 파서 (재귀 하향) ---------- */
  function parse(src) {
    const tk = tokenize(src);
    let p = 0;

    const peek = () => tk[p];
    const eat = (t, v) => {
      const x = tk[p];
      if (!x || x.t !== t || (v !== undefined && x.v !== v)) return null;
      p++; return x;
    };

    function parseExpr() { return parseAdd(); }

    function parseAdd() {
      let left = parseMul();
      for (;;) {
        const t = peek();
        if (t && t.t === 'op' && (t.v === '+' || t.v === '-')) {
          p++;
          left = { k: 'bin', op: t.v, a: left, b: parseMul() };
        } else return left;
      }
    }

    function parseMul() {
      let left = parseUnary();
      for (;;) {
        const t = peek();
        if (t && t.t === 'op' && (t.v === '*' || t.v === '/' || t.v === '%')) {
          p++;
          left = { k: 'bin', op: t.v, a: left, b: parseUnary() };
        } else if (t && (t.t === 'num' || t.t === 'id' || t.t === 'lp')) {
          // 암묵적 곱셈: 2x, 3(4+1), 2pi
          left = { k: 'bin', op: '*', a: left, b: parseUnary() };
        } else return left;
      }
    }

    function parseUnary() {
      const t = peek();
      if (t && t.t === 'op' && (t.v === '-' || t.v === '+')) {
        p++;
        const node = parseUnary();
        return t.v === '-' ? { k: 'neg', a: node } : node;
      }
      return parsePower();
    }

    function parsePower() {
      const base = parsePostfix();
      const t = peek();
      if (t && t.t === 'op' && t.v === '^') {
        p++;
        return { k: 'bin', op: '^', a: base, b: parseUnary() };  // 우결합, 2^-3 허용
      }
      return base;
    }

    function parsePostfix() {
      let node = parsePrimary();
      for (;;) {
        const t = peek();
        if (t && t.t === 'op' && t.v === '!') { p++; node = { k: 'fact', a: node }; }
        else return node;
      }
    }

    function parsePrimary() {
      const t = peek();
      if (!t) throw new CalcError('수식이 갑자기 끝났습니다');

      if (t.t === 'num') { p++; return { k: 'num', v: t.v }; }

      if (t.t === 'lp') {
        p++;
        const e = parseExpr();
        if (!eat('rp')) throw new CalcError('괄호를 닫지 않으셨어요 )');
        return e;
      }

      if (t.t === 'id') {
        p++;
        const name = t.v;
        if (peek() && peek().t === 'lp') {
          p++;
          const args = [];
          if (!(peek() && peek().t === 'rp')) {
            args.push(parseExpr());
            while (eat('comma')) args.push(parseExpr());
          }
          if (!eat('rp')) throw new CalcError(name + '( ... 괄호를 닫아주세요');
          if (!FUNCS[name]) throw new CalcError('"' + name + '" 이라는 함수는 모릅니다');
          return { k: 'call', name, args };
        }
        if (Object.prototype.hasOwnProperty.call(CONSTS, name)) return { k: 'num', v: CONSTS[name] };
        if (name === 'x' || name === 't' || name === 'n') return { k: 'var', name: 'x' };
        if (FUNCS[name]) throw new CalcError(name + ' 뒤에는 괄호가 필요합니다: ' + name + '(...)');
        throw new CalcError('"' + name + '" 이라는 건 모르겠습니다');
      }

      if (t.t === 'op') throw new CalcError('연산자 "' + t.v + '" 위치가 이상합니다');
      throw new CalcError('해석 불가능한 수식입니다');
    }

    const ast = parseExpr();
    if (p < tk.length) throw new CalcError('수식 뒤에 남는 게 있습니다');
    return ast;
  }

  /* ---------- 1-6. 평가기 ---------- */
  function evalNode(node, env) {
    switch (node.k) {
      case 'num': return node.v;
      case 'var': return env && env.x !== undefined ? env.x : (() => { throw new CalcError('x 값이 정해지지 않았습니다 (그래프 칸에 넣어보세요)'); })();
      case 'neg': return -evalNode(node.a, env);
      case 'fact': return factorial(evalNode(node.a, env));
      case 'call': return FUNCS[node.name](node.args.map((a) => evalNode(a, env)));
      case 'bin': {
        const a = evalNode(node.a, env), b = evalNode(node.b, env);
        switch (node.op) {
          case '+': return a + b;
          case '-': return a - b;
          case '*': return a * b;
          case '/':
            if (b === 0) throw new CalcError('0으로 나누면 우주가 뒤집힙니다');
            return a / b;
          case '%':
            if (b === 0) throw new CalcError('0으로 나머지를 구할 수 없습니다');
            return a % b;
          case '^': {
            const r = Math.pow(a, b);
            if (Number.isNaN(r) && a < 0) throw new CalcError('음수의 소수 거듭제곱은 허수가 됩니다');
            return r;
          }
        }
        break;
      }
    }
    throw new CalcError('알 수 없는 노드');
  }

  function compile(src) {
    const ast = parse(src);
    return (x) => evalNode(ast, { x });
  }

  function evaluate(src) {
    if (!src || !src.trim()) throw new CalcError('빈 수식입니다');
    return evalNode(parse(src), {});
  }

  /* ---------- 1-7. 출력 포맷 ---------- */
  function format(v) {
    if (typeof v !== 'number' || Number.isNaN(v)) return 'NaN (정의되지 않음)';
    if (v === Infinity) return '∞';
    if (v === -Infinity) return '-∞';
    if (v === 0) return '0';
    const av = Math.abs(v);
    if (Number.isInteger(v) && av < 1e15) return String(v);
    if (av >= 1e15 || av < 1e-7) {
      return v.toExponential(9).replace(/(\.\d*?)0+e/, '$1e').replace(/\.e/, 'e');
    }
    const r = parseFloat(v.toPrecision(12));
    return String(r);
  }

  return {
    evaluate, compile, format, CalcError,
    zeta, isPrime, primePi, primeFactors, nextPrime, gamma, factorial,
    FUNCS, CONSTS
  };
})();


/* =========================================================================
 * [2] Grapher — Canvas 좌표평면 & 곡선
 * ========================================================================= */
const Grapher = (function () {
  const canvas = document.getElementById('canvas');
  const ctx = canvas.getContext('2d');
  const legendEl = document.getElementById('legend');

  const COLORS = ['#6cf3d6', '#ff4fa3', '#d6ff3f', '#9b6cff', '#ff9f45', '#5ab8ff'];

  const view = { cx: 0, cy: 0, scale: 40 };   // scale = 1단위당 픽셀
  let curves = [];                            // { src, fn, color, error }
  let W = 900, H = 560, dpr = 1;

  function resize() {
    dpr = Math.min(window.devicePixelRatio || 1, 2);
    const cssW = canvas.clientWidth || 900;
    const cssH = Math.round(cssW * 0.62);
    canvas.style.height = cssH + 'px';
    canvas.width = Math.round(cssW * dpr);
    canvas.height = Math.round(cssH * dpr);
    W = cssW; H = cssH;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    draw();
  }

  const toPx = (x) => W / 2 + (x - view.cx) * view.scale;
  const toPy = (y) => H / 2 - (y - view.cy) * view.scale;
  const fromPx = (px) => view.cx + (px - W / 2) / view.scale;
  const fromPy = (py) => view.cy - (py - H / 2) / view.scale;

  // 60~140px 사이가 되는 "예쁜" 눈금 간격 찾기
  function niceStep() {
    const target = 78 / view.scale;
    const mag = Math.pow(10, Math.floor(Math.log10(target)));
    const norm = target / mag;
    const mult = norm < 1.5 ? 1 : norm < 3.5 ? 2 : norm < 7.5 ? 5 : 10;
    return mult * mag;
  }

  function fmtTick(v, step) {
    if (Math.abs(v) < step * 1e-9) return '0';
    const d = Math.max(0, -Math.floor(Math.log10(step)));
    if (Math.abs(v) >= 1e5 || Math.abs(v) < 1e-4) return v.toExponential(1);
    return parseFloat(v.toFixed(Math.min(6, d + 1))).toString();
  }

  function drawGrid() {
    const step = niceStep();
    const x0 = fromPx(0), x1 = fromPx(W);
    const y0 = fromPy(H), y1 = fromPy(0);

    // 보조 격자
    ctx.lineWidth = 1;
    ctx.strokeStyle = 'rgba(120,105,190,.16)';
    ctx.beginPath();
    for (let x = Math.ceil(x0 / step) * step; x <= x1; x += step) {
      const px = Math.round(toPx(x)) + .5;
      ctx.moveTo(px, 0); ctx.lineTo(px, H);
    }
    for (let y = Math.ceil(y0 / step) * step; y <= y1; y += step) {
      const py = Math.round(toPy(y)) + .5;
      ctx.moveTo(0, py); ctx.lineTo(W, py);
    }
    ctx.stroke();

    // 축
    const ax = Math.round(toPx(0)) + .5;
    const ay = Math.round(toPy(0)) + .5;
    ctx.strokeStyle = 'rgba(210,200,255,.6)';
    ctx.lineWidth = 1.6;
    ctx.beginPath();
    if (ay > -50 && ay < H + 50) { ctx.moveTo(0, ay); ctx.lineTo(W, ay); }
    if (ax > -50 && ax < W + 50) { ctx.moveTo(ax, 0); ctx.lineTo(ax, H); }
    ctx.stroke();

    // 눈금 숫자
    ctx.fillStyle = 'rgba(190,180,230,.85)';
    ctx.font = '11px ui-monospace, Menlo, monospace';
    ctx.textAlign = 'center'; ctx.textBaseline = 'top';
    const labelY = Math.min(Math.max(ay + 4, 4), H - 16);
    for (let x = Math.ceil(x0 / step) * step; x <= x1; x += step) {
      if (Math.abs(x) < step * 1e-9) continue;
      ctx.fillText(fmtTick(x, step), toPx(x), labelY);
    }
    ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
    const labelX = Math.min(Math.max(ax - 6, 30), W - 4);
    for (let y = Math.ceil(y0 / step) * step; y <= y1; y += step) {
      if (Math.abs(y) < step * 1e-9) continue;
      ctx.fillText(fmtTick(y, step), labelX, toPy(y));
    }
    ctx.textAlign = 'left'; ctx.textBaseline = 'top';
    ctx.fillText('O', Math.min(Math.max(ax + 5, 4), W - 14), Math.min(Math.max(ay + 4, 4), H - 16));
  }

  function drawCurve(curve) {
    const { fn, color } = curve;
    ctx.strokeStyle = color;
    ctx.lineWidth = 2.2;
    ctx.lineJoin = 'round';
    ctx.beginPath();

    const stepPx = 1;
    let pen = false, prevPy = null;
    const yLimit = Math.abs(fromPy(0) - fromPy(H)) * 12 + 1000;

    for (let px = 0; px <= W; px += stepPx) {
      const x = fromPx(px);
      let y;
      try { y = fn(x); } catch (e) { y = NaN; }

      if (typeof y !== 'number' || !Number.isFinite(y) || Math.abs(y) > yLimit) {
        pen = false; prevPy = null;
        continue;
      }
      const py = toPy(y);

      // 점근선 추정: 화면 높이의 2.5배 넘게 뛰면 선을 끊는다
      if (pen && prevPy !== null && Math.abs(py - prevPy) > H * 2.5) {
        pen = false;
      }
      if (!pen) { ctx.moveTo(px, py); pen = true; }
      else ctx.lineTo(px, py);

      prevPy = py;
    }
    ctx.stroke();
  }

  function draw() {
    ctx.clearRect(0, 0, W, H);
    ctx.fillStyle = '#070612';
    ctx.fillRect(0, 0, W, H);
    drawGrid();
    for (const c of curves) if (!c.error) drawCurve(c);
  }

  function setExpressions(raw) {
    const parts = raw.split(';').map((s) => s.trim()).filter(Boolean);
    curves = parts.map((src, i) => {
      const c = { src, color: COLORS[i % COLORS.length], fn: null, error: null };
      try { c.fn = MathCore.compile(src); }
      catch (e) { c.error = e.message; }
      return c;
    });
    renderLegend();
    draw();
    return curves;
  }

  function renderLegend() {
    legendEl.innerHTML = '';
    curves.forEach((c) => {
      const span = document.createElement('span');
      span.innerHTML = '<i style="background:' + c.color + '"></i>';
      span.appendChild(document.createTextNode(
        c.error ? c.src + ' ⚠ ' + c.error : 'y = ' + c.src
      ));
      if (c.error) span.style.color = '#ff4fa3';
      legendEl.appendChild(span);
    });
  }

  function zoomAt(px, py, factor) {
    const mx = fromPx(px), my = fromPy(py);
    view.scale = Math.min(4e6, Math.max(1e-4, view.scale * factor));
    // 커서 아래 좌표가 그대로 유지되도록 중심 보정
    view.cx = mx - (px - W / 2) / view.scale;
    view.cy = my + (py - H / 2) / view.scale;
    draw();
  }

  function reset() { view.cx = 0; view.cy = 0; view.scale = 40; draw(); }

  /* --- 마우스 / 터치 인터랙션 --- */
  let dragging = false, lastX = 0, lastY = 0;

  canvas.addEventListener('pointerdown', (e) => {
    dragging = true; lastX = e.offsetX; lastY = e.offsetY;
    canvas.classList.add('dragging');
    canvas.setPointerCapture(e.pointerId);
  });
  canvas.addEventListener('pointermove', (e) => {
    if (!dragging) return;
    view.cx -= (e.offsetX - lastX) / view.scale;
    view.cy += (e.offsetY - lastY) / view.scale;
    lastX = e.offsetX; lastY = e.offsetY;
    draw();
  });
  const endDrag = () => { dragging = false; canvas.classList.remove('dragging'); };
  canvas.addEventListener('pointerup', endDrag);
  canvas.addEventListener('pointercancel', endDrag);
  canvas.addEventListener('wheel', (e) => {
    e.preventDefault();
    zoomAt(e.offsetX, e.offsetY, e.deltaY < 0 ? 1.15 : 1 / 1.15);
  }, { passive: false });

  window.addEventListener('resize', resize);

  return {
    init: resize,
    setExpressions,
    zoom: (f) => zoomAt(W / 2, H / 2, f),
    reset,
    draw
  };
})();


/* =========================================================================
 * [3] WeirdUI — 이상한 유저 인터페이스
 * ========================================================================= */
const WeirdUI = (function () {
  const root = document.documentElement;
  const toastBox = document.getElementById('toasts');

  let level = 2;                       // 0 = 멀쩡, 3 = 최대 기괴
  const WEIRD_NAMES = ['멀쩡함 😇', '살짝 이상 🙂', '보통 이상함 😵', '완전 기괴 🤪'];

  /* --- 3-1. 사운드 (사용자 조작 후 생성) --- */
  let audioCtx = null;
  function blip(kind) {
    if (level === 0) return;
    try {
      if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
      const t = audioCtx.currentTime;
      const osc = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      const waves = ['sine', 'square', 'triangle', 'sawtooth'];
      osc.type = level >= 2 ? waves[(Math.random() * waves.length) | 0] : 'sine';

      let f0 = 320 + Math.random() * (level >= 2 ? 700 : 160);
      if (kind === 'error') f0 = 150;
      if (kind === 'equal') f0 = 520;
      osc.frequency.setValueAtTime(f0, t);
      const f1 = kind === 'error' ? f0 * 0.5 : f0 * (level >= 3 ? (0.5 + Math.random() * 1.6) : 1.25);
      osc.frequency.exponentialRampToValueAtTime(Math.max(60, f1), t + 0.13);

      gain.gain.setValueAtTime(0.0001, t);
      gain.gain.exponentialRampToValueAtTime(0.09, t + 0.012);
      gain.gain.exponentialRampToValueAtTime(0.0001, t + 0.18);

      osc.connect(gain).connect(audioCtx.destination);
      osc.start(t); osc.stop(t + 0.2);
    } catch (e) { /* 소리는 없어도 계산은 됩니다 */ }
  }

  /* --- 3-2. 방해 팝업(토스트) --- */
  const NAGS = [
    '정말 그 숫자가 맞나요?', '계산 중... 인 척 하는 중',
    '제타 함수는 오늘 기분이 좋습니다', '버튼이 도망간 건 제 탓이 아닙니다',
    '소수는 외롭습니다. 1은 소수가 아니니까요.',
    '이 계산기는 정확합니다. 아마도.', '0으로 나누지 마세요. 부탁입니다.',
    'π는 무리수입니다. 저도 무리입니다.', '☕ 잠시 쉬었다 하세요',
    'ζ(2) = π²/6 입니다. 외워두면 멋있습니다.',
    '그래프 탭은 진지하게 만들었습니다. 봐주세요.',
    '기괴함 레벨 0으로 내리면 제가 조용해집니다.'
  ];
  const TONES = ['', 'hot', 'acid', 'neon'];

  function toast(msg, tone) {
    const el = document.createElement('div');
    el.className = 'toast ' + (tone !== undefined ? tone : TONES[(Math.random() * TONES.length) | 0]);
    el.textContent = msg;
    if (level >= 3) el.style.transform = 'rotate(' + (Math.random() * 10 - 5).toFixed(1) + 'deg)';
    toastBox.appendChild(el);
    setTimeout(() => {
      el.classList.add('out');
      setTimeout(() => el.remove(), 320);
    }, 2600);
  }
  function maybeNag(chance) {
    if (level === 0) return;
    if (Math.random() < chance * (level / 3)) toast(NAGS[(Math.random() * NAGS.length) | 0]);
  }

  /* --- 3-3. 키패드 (비선형 배치 + 트롤링) --- */
  const KEYS = [
    { l: '7', v: '7', c: 'num' }, { l: '8', v: '8', c: 'num' }, { l: '9', v: '9', c: 'num' },
    { l: '4', v: '4', c: 'num' }, { l: '5', v: '5', c: 'num' }, { l: '6', v: '6', c: 'num' },
    { l: '1', v: '1', c: 'num' }, { l: '2', v: '2', c: 'num' }, { l: '3', v: '3', c: 'num' },
    { l: '0', v: '0', c: 'num' }, { l: '.', v: '.', c: 'num' },
    { l: '+', v: '+', c: 'op' }, { l: '−', v: '-', c: 'op' },
    { l: '×', v: '*', c: 'op' }, { l: '÷', v: '/', c: 'op' },
    { l: 'xʸ', v: '^', c: 'op' }, { l: 'n!', v: '!', c: 'op' }, { l: 'mod', v: '%', c: 'op' },
    { l: '(', v: '(', c: 'op' }, { l: ')', v: ')', c: 'op' },
    { l: 'π', v: 'pi', c: 'fn' }, { l: 'e', v: 'e', c: 'fn' },
    { l: '√', v: 'sqrt(', c: 'fn' }, { l: 'ln', v: 'ln(', c: 'fn' },
    { l: 'log', v: 'log(', c: 'fn' }, { l: 'eˣ', v: 'exp(', c: 'fn' },
    { l: 'rand', v: 'rand(', c: 'fn' }, { l: 'ζ', v: 'zeta(', c: 'fn' },
    { l: 'p?', v: 'isprime(', c: 'fn' }, { l: 'π(x)', v: 'primepi(', c: 'fn' },
    { l: 'C', v: 'CLEAR', c: 'danger' }, { l: '⌫', v: 'BACK', c: 'danger' },
    { l: '=', v: 'EQ', c: 'equal' }
  ];

  const keypad = document.getElementById('keypad');
  let clickCount = 0, dodges = 0;
  let onInsert = () => {}, onEqual = () => {}, onClear = () => {}, onBack = () => {};

  function shuffled(arr) {
    const a = arr.slice();
    for (let i = a.length - 1; i > 0; i--) {
      const j = (Math.random() * (i + 1)) | 0;
      [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
  }

  function buildKeypad() {
    keypad.innerHTML = '';
    let list = KEYS.slice();

    if (level >= 2) {
      // 숫자/연산/함수 키를 통째로 섞어버린다 (= 와 C 는 뒤에 고정)
      const special = list.filter((k) => k.c === 'equal' || k.c === 'danger');
      const rest = shuffled(list.filter((k) => k.c !== 'equal' && k.c !== 'danger'));
      list = level >= 3 ? shuffled(rest.concat(special)) : rest.concat(special);
    }

    list.forEach((k) => {
      const b = document.createElement('button');
      b.className = 'key ' + k.c;
      b.type = 'button';
      b.textContent = k.l;
      b.dataset.val = k.v;

      if (level >= 2) {
        // 크기가 제각각인 폰트 + 미세한 회전
        const fs = 14 + Math.random() * (level >= 3 ? 14 : 7);
        b.style.fontSize = fs.toFixed(1) + 'px';
        const rot = (Math.random() * 2 - 1) * (level >= 3 ? 7 : 3);
        b.style.transform = 'rotate(' + rot.toFixed(2) + 'deg)';
      }
      keypad.appendChild(b);
    });
    hookEqual();
  }

  // "=" 버튼은 마우스를 피해 도망갑니다 (3번 피하면 포기)
  function hookEqual() {
    const eq = keypad.querySelector('.key.equal');
    if (!eq) return;
    eq.addEventListener('mouseenter', () => {
      if (level < 2 || dodges >= 3) return;
      dodges++;
      const dx = (Math.random() * 2 - 1) * 60;
      const dy = (Math.random() * 2 - 1) * 26;
      eq.style.transform = 'translate(' + dx.toFixed(0) + 'px,' + dy.toFixed(0) + 'px) rotate(' + (Math.random() * 16 - 8).toFixed(1) + 'deg)';
      eq.classList.add('fled');
      if (dodges === 3) {
        setTimeout(() => {
          eq.style.transform = '';
          eq.classList.remove('fled');
          toast('알겠어요, 항복. 누르세요.', 'acid');
        }, 380);
      }
    });
  }

  function jiggle(btn) {
    if (level === 0) return;
    const amp = level >= 3 ? 10 : level >= 2 ? 5 : 2;
    const dx = (Math.random() * 2 - 1) * amp;
    const dy = (Math.random() * 2 - 1) * amp;
    const rot = (Math.random() * 2 - 1) * amp;
    btn.style.transform = 'translate(' + dx.toFixed(1) + 'px,' + dy.toFixed(1) + 'px) rotate(' + rot.toFixed(1) + 'deg)';
  }

  keypad.addEventListener('click', (e) => {
    const btn = e.target.closest('.key');
    if (!btn) return;
    const v = btn.dataset.val;

    clickCount++;
    jiggle(btn);

    if (v === 'EQ')          { blip('equal'); onEqual(); }
    else if (v === 'CLEAR')  { blip(); onClear(); }
    else if (v === 'BACK')   { blip(); onBack(); }
    else                     { blip(); onInsert(v); }

    // 레벨 3: 몇 번 누를 때마다 배치가 통째로 바뀐다
    if (level >= 3 && clickCount % 9 === 0) {
      dodges = 0;
      buildKeypad();
      toast('버튼들이 자리를 바꿨습니다 🌀', 'hot');
    }
    maybeNag(0.08);
  });

  /* --- 3-4. 결과 표시 (제각각인 폰트) --- */
  function renderResult(el, text) {
    el.innerHTML = '';
    if (level === 0) { el.textContent = text; return; }
    [...text].forEach((ch, i) => {
      const s = document.createElement('span');
      s.className = 'ch';
      s.textContent = ch;
      // 인덱스 기반 결정적 변형 → 깜빡이지 않고 꾸준히 이상함
      const h = Math.sin(i * 12.9898) * 43758.5453;
      const r = h - Math.floor(h);
      const amp = level >= 3 ? 1 : level >= 2 ? 0.5 : 0.22;
      s.style.transform = 'rotate(' + ((r * 16 - 8) * amp).toFixed(1) + 'deg) translateY(' + ((r * 10 - 5) * amp).toFixed(1) + 'px)';
      s.style.fontSize = (1 + (r - 0.5) * 0.5 * amp).toFixed(2) + 'em';
      el.appendChild(s);
    });
  }

  function shake(el) {
    if (level === 0) return;
    el.classList.remove('shake');
    void el.offsetWidth;
    el.classList.add('shake');
    setTimeout(() => el.classList.remove('shake'), 450);
  }

  /* --- 3-5. 레벨 설정 --- */
  function setLevel(n) {
    level = n;
    root.dataset.weird = String(n);
    document.getElementById('weirdLabel').textContent = WEIRD_NAMES[n];
    dodges = 0;
    buildKeypad();
  }

  return {
    init(handlers) {
      onInsert = handlers.insert; onEqual = handlers.equal;
      onClear = handlers.clear; onBack = handlers.back;
      setLevel(level);
    },
    setLevel, toast, maybeNag, blip, renderResult, shake,
    get level() { return level; }
  };
})();


/* =========================================================================
 * [4] Wiring — 이벤트 연결
 * ========================================================================= */
(function App() {
  const exprEl   = document.getElementById('expr');
  const resultEl = document.getElementById('result');
  const errEl    = document.getElementById('errline');
  const histEl   = document.getElementById('history');

  const history = [];

  /* --- 4-1. 입력 헬퍼 --- */
  function insert(text) {
    const s = exprEl.selectionStart ?? exprEl.value.length;
    const e = exprEl.selectionEnd ?? exprEl.value.length;
    exprEl.value = exprEl.value.slice(0, s) + text + exprEl.value.slice(e);
    const pos = s + text.length;
    exprEl.focus();
    exprEl.setSelectionRange(pos, pos);
  }
  function backspace() {
    const s = exprEl.selectionStart ?? exprEl.value.length;
    const e = exprEl.selectionEnd ?? exprEl.value.length;
    if (s !== e) exprEl.value = exprEl.value.slice(0, s) + exprEl.value.slice(e);
    else if (s > 0) { exprEl.value = exprEl.value.slice(0, s - 1) + exprEl.value.slice(s); }
    const pos = Math.max(0, s === e ? s - 1 : s);
    exprEl.focus();
    exprEl.setSelectionRange(pos, pos);
  }
  function clearAll() {
    exprEl.value = '';
    errEl.textContent = '';
    WeirdUI.renderResult(resultEl, '0');
    exprEl.focus();
  }

  /* --- 4-2. 계산 --- */
  function calculate() {
    const src = exprEl.value;
    errEl.textContent = '';
    try {
      const v = MathCore.evaluate(src);
      const out = MathCore.format(v);
      WeirdUI.renderResult(resultEl, out);
      resultEl.classList.remove('pop'); void resultEl.offsetWidth; resultEl.classList.add('pop');
      pushHistory(src.trim(), out);
      WeirdUI.maybeNag(0.35);
      return v;
    } catch (err) {
      const msg = err instanceof MathCore.CalcError ? err.message : '계산할 수 없습니다: ' + err.message;
      errEl.textContent = '⚠ ' + msg;
      WeirdUI.renderResult(resultEl, '???');
      WeirdUI.shake(document.querySelector('.display'));
      WeirdUI.blip('error');
      return null;
    }
  }

  function pushHistory(src, out) {
    history.unshift({ src, out });
    if (history.length > 20) history.pop();
    renderHistory();
  }
  function renderHistory() {
    histEl.innerHTML = '';
    if (!history.length) {
      histEl.innerHTML = '<li class="empty">아직 없음</li>';
      return;
    }
    history.forEach((h) => {
      const li = document.createElement('li');
      li.textContent = h.src + ' = ';
      const b = document.createElement('b');
      b.textContent = h.out;
      li.appendChild(b);
      li.title = '클릭하면 다시 불러옵니다';
      li.addEventListener('click', () => { exprEl.value = h.src; exprEl.focus(); });
      histEl.appendChild(li);
    });
  }

  /* --- 4-3. 키패드 연결 --- */
  WeirdUI.init({
    insert, equal: calculate, clear: clearAll, back: backspace
  });

  /* --- 4-4. 키보드 (항상 멀쩡하게 동작하는 탈출구) --- */
  exprEl.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') { e.preventDefault(); WeirdUI.blip('equal'); calculate(); }
    else if (e.key === 'Escape') { e.preventDefault(); clearAll(); }
  });

  /* --- 4-5. 특수 기능 패널 --- */
  const randOut  = document.getElementById('randOut');
  const primeOut = document.getElementById('primeOut');
  const zetaOut  = document.getElementById('zetaOut');

  function setOut(el, text, bad) {
    el.textContent = text;
    el.classList.toggle('bad', !!bad);
  }

  const ACTIONS = {
    rand() {
      const lo = parseFloat(document.getElementById('randMin').value);
      const hi = parseFloat(document.getElementById('randMax').value);
      if (!Number.isFinite(lo) || !Number.isFinite(hi)) return setOut(randOut, '범위를 숫자로 넣어주세요', true);
      const isInt = document.getElementById('randInt').checked;
      const a = Math.min(lo, hi), b = Math.max(lo, hi);
      const v = isInt
        ? Math.ceil(a) + Math.floor(Math.random() * (Math.floor(b) - Math.ceil(a) + 1))
        : a + Math.random() * (b - a);
      setOut(randOut, '🎲 ' + MathCore.format(v));
      WeirdUI.blip();
    },
    isprime() {
      const n = parseFloat(document.getElementById('primeN').value);
      try {
        const yes = MathCore.isPrime(n);
        setOut(primeOut, n + ' → ' + (yes ? '소수입니다 ✅' : '소수가 아닙니다 ❌'));
      } catch (e) { setOut(primeOut, '⚠ ' + e.message, true); }
      WeirdUI.blip();
    },
    primepi() {
      const n = parseFloat(document.getElementById('primeN').value);
      try {
        const c = MathCore.primePi(n);
        const approx = n > 2 ? n / Math.log(n) : 0;
        setOut(primeOut, 'π(' + Math.floor(n) + ') = ' + c.toLocaleString()
          + '   (근사 x/ln x ≈ ' + approx.toFixed(1) + ')');
      } catch (e) { setOut(primeOut, '⚠ ' + e.message, true); }
      WeirdUI.blip();
    },
    factor() {
      const n = parseFloat(document.getElementById('primeN').value);
      try {
        const f = MathCore.primeFactors(n);
        if (!f.length) return setOut(primeOut, Math.abs(n) + ' 은(는) 인수분해할 게 없습니다');
        // 지수 형태로 묶기
        const grouped = [];
        f.forEach((p) => {
          const last = grouped[grouped.length - 1];
          if (last && last[0] === p) last[1]++;
          else grouped.push([p, 1]);
        });
        setOut(primeOut, Math.abs(Math.trunc(n)) + ' = ' +
          grouped.map(([p, k]) => k > 1 ? p + '^' + k : String(p)).join(' × '));
      } catch (e) { setOut(primeOut, '⚠ ' + e.message, true); }
      WeirdUI.blip();
    },
    zeta() {
      const s = parseFloat(document.getElementById('zetaS').value);
      if (!Number.isFinite(s)) return setOut(zetaOut, 's를 숫자로 넣어주세요', true);
      const v = MathCore.zeta(s);
      let extra = '';
      if (Math.abs(s - 2) < 1e-12) extra = '   ( = π²/6 )';
      if (Math.abs(s - 4) < 1e-12) extra = '   ( = π⁴/90 )';
      if (Math.abs(s + 1) < 1e-12) extra = '   ( = -1/12, 그 유명한 값 )';
      if (v === Infinity) return setOut(zetaOut, 'ζ(1)은 발산합니다 (조화급수)', true);
      setOut(zetaOut, 'ζ(' + s + ') = ' + MathCore.format(v) + extra);
      WeirdUI.blip();
    },
    clearHistory() {
      history.length = 0;
      renderHistory();
      WeirdUI.toast('기록을 태웠습니다 🔥', 'hot');
    },
    plot() { plot(); },
    zoomIn()  { Grapher.zoom(1.3); },
    zoomOut() { Grapher.zoom(1 / 1.3); },
    resetView() { Grapher.reset(); }
  };

  document.addEventListener('click', (e) => {
    const btn = e.target.closest('[data-act]');
    if (!btn) return;
    const fn = ACTIONS[btn.dataset.act];
    if (fn) fn();
  });

  /* --- 4-6. 그래프 --- */
  const fxEl = document.getElementById('fx');
  function plot() {
    const curves = Grapher.setExpressions(fxEl.value);
    const bad = curves.filter((c) => c.error);
    if (bad.length) WeirdUI.toast('식 ' + bad.length + '개를 못 읽었습니다', 'hot');
  }
  fxEl.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') { e.preventDefault(); plot(); }
  });

  /* --- 4-7. 기괴함 레벨 --- */
  const weirdEl = document.getElementById('weird');
  weirdEl.addEventListener('input', () => {
    WeirdUI.setLevel(parseInt(weirdEl.value, 10));
    if (weirdEl.value === '0') WeirdUI.toast('...조용히 하겠습니다.', 'neon');
    if (weirdEl.value === '3') WeirdUI.toast('후회하지 마세요 🤪', 'hot');
  });

  /* --- 4-8. 시작 --- */
  Grapher.init();
  plot();
  WeirdUI.renderResult(resultEl, '0');
  renderHistory();
  exprEl.value = 'zeta(2)';
  setTimeout(() => WeirdUI.toast('환영합니다. 버튼은 가끔 도망갑니다.', 'neon'), 700);

  // 가끔 혼자 말을 겁니다 (레벨 2 이상)
  setInterval(() => WeirdUI.maybeNag(0.22), 17000);
})();

})();
