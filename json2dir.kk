// json2dir: create the directory tree a JSON document describes, in the current directory.
// Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
//
// Koka standard library plus Koka `extern` declarations to C for the POSIX calls the
// standard library does not offer (lstat, symlink, unlink, open O_EXCL|O_NOFOLLOW, fchmod).
module json2dir

import std/num/int32
import std/os/env

extern import
  c header-include-inline "#include <sys/stat.h>\n#include <fcntl.h>\n#include <unistd.h>\nstatic kk_bytes_t j2d_read_stdin(kk_context_t* ctx) { size_t cap = 65536, len = 0; uint8_t* buf = (uint8_t*)malloc(cap); for (;;) { if (len == cap) { cap *= 2; buf = (uint8_t*)realloc(buf, cap); } ssize_t n = read(0, buf + len, cap - len); if (n < 0) { if (errno == EINTR) continue; break; } if (n == 0) break; len += (size_t)n; } kk_bytes_t b = kk_bytes_alloc_dupn((kk_ssize_t)len, buf, ctx); free(buf); return b; }\nstatic int32_t j2d_kind(const char* p) { struct stat st; if (lstat(p, &st) != 0) return errno == ENOENT ? 0 : -errno; return S_ISDIR(st.st_mode) ? 1 : 2; }\nstatic int32_t j2d_write(const char* p, kk_bytes_t content, bool exec, kk_context_t* ctx) { kk_ssize_t len = 0; const uint8_t* buf = kk_bytes_buf_borrow(content, &len, ctx); int fd = open(p, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0666); if (fd < 0) return errno; while (len > 0) { ssize_t n = write(fd, buf, (size_t)len); if (n < 0) { if (errno == EINTR) continue; int e = errno; close(fd); return e; } buf += n; len -= n; } if (exec) { struct stat st; if (fstat(fd, &st) != 0 || fchmod(fd, (st.st_mode & 07777) | 0111) != 0) { int e = errno; close(fd); return e; } } if (close(fd) != 0) return errno; return 0; }\nstatic int32_t j2d_err(int r) { return r == 0 ? 0 : errno; }"

extern read-stdin() : io bytes
  c inline "j2d_read_stdin(kk_context())"

// 0 = absent, 1 = directory, 2 = anything else (never follows a symlink), < 0 = -errno
extern lstat-kind( ^p : string ) : io int32
  c inline "j2d_kind(kk_string_cbuf_borrow(#1, NULL, kk_context()))"

extern c-unlink( ^p : string ) : io int32
  c inline "j2d_err(unlink(kk_string_cbuf_borrow(#1, NULL, kk_context())))"

extern c-mkdir( ^p : string ) : io int32
  c inline "j2d_err(mkdir(kk_string_cbuf_borrow(#1, NULL, kk_context()), 0777))"

extern c-symlink( ^target : string, ^p : string ) : io int32
  c inline "j2d_err(symlink(kk_string_cbuf_borrow(#1, NULL, kk_context()), kk_string_cbuf_borrow(#2, NULL, kk_context())))"

extern c-write( ^p : string, ^content : bytes, exec : bool ) : io int32
  c inline "j2d_write(kk_string_cbuf_borrow(#1, NULL, kk_context()), #2, #3, kk_context())"

extern c-strerror( e : int32 ) : string
  c inline "kk_string_alloc_from_qutf8(strerror(#1), kk_context())"

extern ewriteln( ^s : string ) : io ()
  c inline "(fputs(kk_string_cbuf_borrow(#1, NULL, kk_context()), stderr), fputc(10, stderr), kk_Unit)"

extern c-exit( code : int32 ) : io ()
  c inline "(exit(#1), kk_Unit)"

// ---------------------------------------------------------------------------
// Values. Strings are kept as their exact UTF-8 bytes.

type json
  JStr( b : bytes )
  JArr( items : list<json> )
  JObj( members : list<(bytes, json)> )

// Parse and validation errors are an effect; `main` installs the handler.
effect bad-input
  ctl reject( msg : string ) : a

// ---------------------------------------------------------------------------
// §3: strict UTF-8 (no overlongs, no surrogates, nothing above U+10FFFF).

fun at( b : bytes, i : int ) : int
  if i >= 0 && i < b.length then b.unsafe-index(i.ssize_t).int else -1

fun is-cont( c : int ) : bool
  c >= 0x80 && c <= 0xBF

fun check-utf8( b : bytes, i : int ) : <bad-input,div> ()
  val n = b.length
  if i >= n then return ()
  val c = b.at(i)
  if c < 0x80 then check-utf8(b, i + 1)
  elif c >= 0xC2 && c <= 0xDF && is-cont(b.at(i + 1)) then check-utf8(b, i + 2)
  elif c >= 0xE0 && c <= 0xEF then
    val c1 = b.at(i + 1)
    val ok1 = if c == 0xE0 then c1 >= 0xA0 && c1 <= 0xBF
              elif c == 0xED then c1 >= 0x80 && c1 <= 0x9F
              else is-cont(c1)
    if ok1 && is-cont(b.at(i + 2)) then check-utf8(b, i + 3) else reject("input is not valid UTF-8")
  elif c >= 0xF0 && c <= 0xF4 then
    val c1 = b.at(i + 1)
    val ok1 = if c == 0xF0 then c1 >= 0x90 && c1 <= 0xBF
              elif c == 0xF4 then c1 >= 0x80 && c1 <= 0x8F
              else is-cont(c1)
    if ok1 && is-cont(b.at(i + 2)) && is-cont(b.at(i + 3)) then check-utf8(b, i + 4)
    else reject("input is not valid UTF-8")
  else reject("input is not valid UTF-8")

// ---------------------------------------------------------------------------
// §3: a strict, hand-written JSON parser over the input bytes. Positions are threaded
// explicitly. Numbers, true, false and null are rejected right away (§4.4).

fun skip-ws( b : bytes, i : int ) : div int
  val c = b.at(i)
  if c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D then skip-ws(b, i + 1) else i

fun hex-digit( c : int ) : bad-input int
  if c >= 0x30 && c <= 0x39 then c - 0x30
  elif c >= 0x61 && c <= 0x66 then c - 0x61 + 10
  elif c >= 0x41 && c <= 0x46 then c - 0x41 + 10
  else reject("invalid \\u escape")

fun hex4( b : bytes, i : int ) : bad-input int
  hex-digit(b.at(i)) * 4096 + hex-digit(b.at(i + 1)) * 256 + hex-digit(b.at(i + 2)) * 16 + hex-digit(b.at(i + 3))

// Push the UTF-8 encoding of code point `cp` onto the reversed byte list.
fun push-utf8( acc : list<int>, cp : int ) : list<int>
  if cp < 0x80 then Cons(cp, acc)
  elif cp < 0x800 then Cons(0x80 + cp % 64, Cons(0xC0 + cp / 64, acc))
  elif cp < 0x10000 then Cons(0x80 + cp % 64, Cons(0x80 + (cp / 64) % 64, Cons(0xE0 + cp / 4096, acc)))
  else Cons(0x80 + cp % 64, Cons(0x80 + (cp / 64) % 64, Cons(0x80 + (cp / 4096) % 64, Cons(0xF0 + cp / 262144, acc))))

// `i` points just after the opening quote; returns the string bytes and the position after the closing quote.
fun parse-string( b : bytes, i : int, acc : list<int> ) : <bad-input,div> (bytes, int)
  val c = b.at(i)
  if c < 0 then reject("unterminated string")
  elif c == 0x22 then (acc.reverse.vector.bytes, i + 1)
  elif c < 0x20 then reject("control character in string")
  elif c != 0x5C then parse-string(b, i + 1, Cons(c, acc))
  else
    val e = b.at(i + 1)
    match e
      0x22 -> parse-string(b, i + 2, Cons(0x22, acc))
      0x5C -> parse-string(b, i + 2, Cons(0x5C, acc))
      0x2F -> parse-string(b, i + 2, Cons(0x2F, acc))
      0x62 -> parse-string(b, i + 2, Cons(0x08, acc))
      0x66 -> parse-string(b, i + 2, Cons(0x0C, acc))
      0x6E -> parse-string(b, i + 2, Cons(0x0A, acc))
      0x72 -> parse-string(b, i + 2, Cons(0x0D, acc))
      0x74 -> parse-string(b, i + 2, Cons(0x09, acc))
      0x75 ->
        val u = hex4(b, i + 2)
        if u >= 0xD800 && u <= 0xDBFF then
          if b.at(i + 6) != 0x5C || b.at(i + 7) != 0x75 then reject("unpaired surrogate in string")
          val lo = hex4(b, i + 8)
          if lo < 0xDC00 || lo > 0xDFFF then reject("unpaired surrogate in string")
          val cp = 0x10000 + (u - 0xD800) * 1024 + (lo - 0xDC00)
          parse-string(b, i + 12, push-utf8(acc, cp))
        elif u >= 0xDC00 && u <= 0xDFFF then reject("unpaired surrogate in string")
        else parse-string(b, i + 6, push-utf8(acc, u))
      _ -> reject("invalid escape in string")

fun parse-value( b : bytes, i0 : int ) : <bad-input,div> (json, int)
  val i = skip-ws(b, i0)
  val c = b.at(i)
  if c == 0x22 then
    val (s, j) = parse-string(b, i + 1, [])
    (JStr(s), j)
  elif c == 0x7B then parse-object(b, i + 1)
  elif c == 0x5B then parse-array(b, i + 1)
  elif c == 0x74 || c == 0x66 || c == 0x6E || c == 0x2D || (c >= 0x30 && c <= 0x39) then
    reject("numbers, true, false and null are not allowed")
  elif c < 0 then reject("unexpected end of input")
  else reject("unexpected character in JSON")

fun parse-array( b : bytes, i0 : int ) : <bad-input,div> (json, int)
  val i = skip-ws(b, i0)
  if b.at(i) == 0x5D then return (JArr([]), i + 1)
  fun items( j0 : int, acc : list<json> ) : <bad-input,div> (json, int)
    val (v, j1) = parse-value(b, j0)
    val j = skip-ws(b, j1)
    val c = b.at(j)
    if c == 0x2C then items(j + 1, Cons(v, acc))
    elif c == 0x5D then (JArr(Cons(v, acc).reverse), j + 1)
    else reject("expected , or ] in array")
  items(i, [])

fun parse-object( b : bytes, i0 : int ) : <bad-input,div> (json, int)
  val i = skip-ws(b, i0)
  if b.at(i) == 0x7D then return (JObj([]), i + 1)
  fun members( j0 : int, acc : list<(bytes, json)> ) : <bad-input,div> (json, int)
    val j = skip-ws(b, j0)
    if b.at(j) != 0x22 then reject("expected a member name")
    val (name, j1) = parse-string(b, j + 1, [])
    val j2 = skip-ws(b, j1)
    if b.at(j2) != 0x3A then reject("expected : after member name")
    val (v, j3) = parse-value(b, j2 + 1)
    val j4 = skip-ws(b, j3)
    val c = b.at(j4)
    val acc' = Cons((name, v), acc)
    if c == 0x2C then members(j4 + 1, acc')
    elif c == 0x7D then (JObj(acc'.reverse), j4 + 1)
    else reject("expected , or } in object")
  members(i, [])

fun parse( b : bytes ) : <bad-input,div> json
  check-utf8(b, 0)
  // A leading byte order mark is ignored (§3).
  val start = if b.at(0) == 0xEF && b.at(1) == 0xBB && b.at(2) == 0xBF then 3 else 0
  val (v, i) = parse-value(b, start)
  if skip-ws(b, i) != b.length then reject("trailing data after the JSON value")
  v

// ---------------------------------------------------------------------------
// §4, §6: validate the whole document before touching the file system.

fun bytes-cmp( a : list<int>, b : list<int> ) : div order
  match (a, b)
    (Nil, Nil) -> Eq
    (Nil, _) -> Lt
    (_, Nil) -> Gt
    (Cons(x, xs), Cons(y, ys)) -> if x < y then Lt elif x > y then Gt else bytes-cmp(xs, ys)

fun show-name( name : bytes ) : string
  name.string.show

fun check-name( name : bytes, where : string ) : bad-input ()
  val l = name.vector.list
  if l.is-nil || l == [0x2E] || l == [0x2E, 0x2E] || l.any(fn(c) c == 0x2F || c == 0) then
    reject(where ++ ": invalid name " ++ name.show-name)

fun validate( v : json, where : string ) : <bad-input,div> ()
  match v
    JStr(_) -> ()
    JArr([JStr(kind), JStr(arg)]) ->
      val k = kind.string
      if k == "link" then
        if arg.vector.list.any(fn(c) c == 0) then reject(where ++ ": a link target cannot contain NUL")
      elif k != "script" then reject(where ++ ": unknown array kind " ++ k.show)
    JArr(_) -> reject(where ++ ": an array must be [\"link\", target] or [\"script\", content]")
    JObj(members) ->
      // Duplicate names are rejected (§4.2 allows either rejecting or keeping the last one).
      val names = members.map(fn(m) m.fst.vector.list)
      val sorted = names.sort-bytes
      sorted.foreach-adjacent(fn(a, b) if a == b then reject(where ++ ": duplicate name " ++ a.vector.bytes.show-name))
      members.foreach fn((name, child))
        val w = if where == "." then name.string else where ++ "/" ++ name.string
        check-name(name, w)
        validate(child, w)

fun foreach-adjacent( xs : list<a>, f : (a, a) -> e () ) : e ()
  match xs
    Cons(x, rest as Cons(y, _)) -> { f(x, y); foreach-adjacent(rest, f) }
    _ -> ()

// Simple merge sort by UTF-8 bytes.
fun sort-by-bytes( xs : list<(list<int>, a)> ) : div list<(list<int>, a)>
  match xs
    Nil -> Nil
    Cons(_, Nil) -> xs
    _ ->
      val half = xs.length / 2
      merge(sort-by-bytes(xs.take(half)), sort-by-bytes(xs.drop(half)))

fun merge( xs : list<(list<int>, a)>, ys : list<(list<int>, a)> ) : div list<(list<int>, a)>
  match (xs, ys)
    (Nil, _) -> ys
    (_, Nil) -> xs
    (Cons(x, xr), Cons(y, yr)) ->
      if bytes-cmp(x.fst, y.fst) != Gt then Cons(x, merge(xr, ys)) else Cons(y, merge(xs, yr))

fun sort-bytes( xs : list<list<int>> ) : div list<list<int>>
  xs.map(fn(x) (x, ())).sort-by-bytes.map(fst)

// ---------------------------------------------------------------------------
// Writing the tree.

fun check( r : int32, what : string ) : <io,exn> ()
  if r != 0.int32 then throw(what ++ ": " ++ c-strerror(r))

fun kind-of( p : string ) : <io,exn> int
  val k = lstat-kind(p)
  if k < 0.int32 then throw(p ++ ": " ++ c-strerror(0.int32 - k))
  k.int

// §5.2, §5.3: an existing non-directory is removed (a symlink itself, never its target);
// §5.4: a directory in the way of a non-object is an error.
fun clear( p : string ) : <io,exn> ()
  match kind-of(p)
    0 -> ()
    1 -> throw(p ++ ": a directory is in the way")
    _ -> check(c-unlink(p), p)

fun apply( dir : string, members : list<(bytes, json)> ) : <io,exn> ()
  val sorted = members.map(fn(m) (m.fst.vector.list, m)).sort-by-bytes.map(snd)
  sorted.foreach fn((name, v))
    val p = dir ++ "/" ++ name.string
    match v
      JStr(content) ->
        clear(p)
        check(c-write(p, content, False), p)
      JArr([JStr(kind), JStr(arg)]) ->
        clear(p)
        if kind.string == "link" then check(c-symlink(arg.string, p), p)
        else check(c-write(p, arg, True), p)
      JObj(children) ->
        val k = kind-of(p)
        if k != 1 then
          if k == 2 then check(c-unlink(p), p)
          check(c-mkdir(p), p)
        apply(p, children)
      _ -> throw(p ++ ": invalid value")

fun fail( msg : string ) : io ()
  ewriteln("json2dir: " ++ msg)
  c-exit(1.int32)

// Parse and validate; the handler for `reject` reports the error and exits.
fun load( input : bytes ) : io json
  with ctl reject(msg)
    fail(msg)
    JObj([])
  val v = parse(input)
  match v
    JObj(_) -> { validate(v, "."); v }
    _ -> reject("the root of the document must be an object")

pub fun main() : io ()
  if !get-args().is-nil then
    ewriteln("usage: json2dir < document.json")
    c-exit(2.int32)
  match load(read-stdin())
    JObj(members) ->
      catch(fn(e) fail(e.message), { apply(".", members) })
    _ -> ()
