#!/usr/bin/env python3
"""Generate reproducible differential cases and run the C and Lean models."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import algebra_dependencies
import check_o1
import check_o2a
import check_o2b

ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 64) - 1
U32_MAX = (1 << 32) - 1
VERDICTS = ("Halted", "BadAccess", "BadValue", "BadInstance", "OutOfFuel")
ALLOWED_LEAN_AXIOMS = ["Classical.choice", "Quot.sound", "propext"]


def require(condition, message):
    # These are acceptance checks, so Python -O must not disable them.
    if not condition:
        raise RuntimeError(message)


def require_unsat(prop, result):
    require(
        result.stdout.strip() == "unsat",
        f"SMT {prop}: expected unsat, got {result.stdout!r}; {result.stderr}",
    )


def require_pass(backend, output):
    require(
        "leanISA validation: PASS" in output.splitlines(),
        f"{backend} did not report PASS: {output!r}",
    )


def validate_request(req):
    """Check the corpus domain before invoking Rust or generating Sail code."""

    def uint(value, maximum, label):
        require(
            type(value) is int and 0 <= value <= maximum,
            f"{label} must be an integer in 0..{maximum}",
        )

    def words(value, size, label):
        require(
            isinstance(value, list) and len(value) == size,
            f"{label} must contain {size} hexadecimal limbs",
        )
        require(
            all(
                isinstance(w, str) and re.fullmatch(r"[0-9a-fA-F]{1,16}", w)
                for w in value
            ),
            f"{label} limbs must be unsigned 64-bit hex strings",
        )

    require(isinstance(req, dict), "request must be an object")
    kind = req.get("kind")
    if kind == "field":
        words(req.get("a"), 3, "a")
        words(req.get("b"), 3, "b")
    elif kind == "blake":
        words(req.get("message"), 8, "message")
        words(req.get("cv"), 4, "cv")
        words(req.get("md"), 3, "md")
        require(int(req["md"][2], 16) == 0, "BLAKE metadata must fit in 128 bits")
    elif kind == "execute":
        program = req.get("program")
        require(
            isinstance(program, list)
            and 1 <= len(program) <= 1 << 32
            and len(program) & (len(program) - 1) == 0,
            "program length must be a power of two in 1..2^32",
        )
        inputs = req.get("input")
        require(
            isinstance(inputs, list) and len(inputs) == 2,
            "input must contain two 128-bit words",
        )
        for value in inputs:
            words(value, 3, "input word")
            require(int(value[2], 16) == 0, "public input words must fit in 128 bits")
        arities = {"xor": 3, "mul": 3, "set": 2, "deref": 4, "jump": 3, "blake": 7}
        for op in program:
            require(
                isinstance(op, list)
                and op
                and isinstance(op[0], str)
                and op[0] in arities,
                f"invalid instruction: {op!r}",
            )
            name = op[0]
            require(len(op) == arities[name] + 1, f"wrong operand count for {name}")
            offsets = (
                op[1:2] if name == "set" else op[1:4] if name == "deref" else op[1:]
            )
            for offset in offsets:
                uint(offset, U32_MAX, "offset")
            if name == "set":
                words(op[2], 3, "SET value")
            if name == "deref":
                require(op[4] in ("Cell", "Pc", "Fp"), "invalid DEREF mode")
        require(req.get("sail_verdict", "Halted") in VERDICTS, "invalid Sail verdict")
        if "expected_unconstrained_reads" in req:
            require(
                isinstance(req["expected_unconstrained_reads"], list),
                "expected_unconstrained_reads must be a list",
            )
            for cell in req["expected_unconstrained_reads"]:
                uint(cell, U32_MAX, "unconstrained read cell")
        require(isinstance(req.get("mutations", []), list), "mutations must be a list")
        for mutation in req.get("mutations", []):
            require(isinstance(mutation, dict), "mutation must be an object")
            uint(mutation.get("cell"), U32_MAX, "mutation cell")
            words(mutation.get("xor"), 3, "mutation xor")
            require(mutation.get("verdict") in VERDICTS, "invalid mutation verdict")
    else:
        raise RuntimeError(f"unknown request kind: {kind!r}")


def run_oracle(requests, binary, *, env, build, timeout):
    """Isolate each upstream execution; a timeout is not an ISA verdict."""
    answers = []
    journal = build / "oracle-cases.jsonl"
    journal.write_text("")
    for index, req in enumerate(requests):
        outcome = {"case": index, "request": req}
        try:
            validate_request(req)
        except RuntimeError as error:
            outcome.update(status="invalid_input", error=str(error))
        else:
            try:
                result = command(
                    [binary],
                    env=env,
                    capture=True,
                    data=json.dumps(req) + "\n",
                    timeout=timeout,
                )
                reply = json.loads(result.stdout)
                require(
                    isinstance(reply, dict)
                    and reply.get("status") in ("ok", "rejected", "panic"),
                    "invalid oracle response envelope",
                )
                if reply["status"] == "ok":
                    require("answer" in reply, "oracle response has no answer")
                outcome.update(reply)
            except subprocess.TimeoutExpired:
                outcome.update(status="timeout", timeout_seconds=timeout)
            except subprocess.CalledProcessError as error:
                outcome.update(
                    status="crash",
                    returncode=error.returncode,
                    stdout=error.stdout,
                    stderr=error.stderr,
                )
            except OSError as error:
                outcome.update(status="launch_error", error=str(error))
            except (ValueError, RuntimeError) as error:
                outcome.update(status="protocol_error", error=str(error))
        with journal.open("a") as output:
            output.write(json.dumps(outcome) + "\n")
        if outcome["status"] != "ok":
            failure = build / "oracle-failure.json"
            failure.write_text(json.dumps(outcome, indent=2) + "\n")
            raise RuntimeError(
                f"oracle case {index}: {outcome['status']}; see {failure}"
            )
        answers.append(outcome["answer"])
    return answers


def check_tool_versions(pins, support, env, *, lean):
    z3 = command(["z3", "--version"], env=env, capture=True).stdout.strip()
    match = re.fullmatch(r"Z3 version (\S+)(?: - .* bit)?", z3)
    require(
        match is not None and match[1] == pins["z3"],
        f"Z3 differs from upstreams.json: {z3!r}",
    )
    # Check the support toolchain even in a C-only campaign. Lean itself is
    # required and checked only when that backend is selected.
    toolchain = (support / "lean-toolchain").read_text().strip()
    require(
        toolchain == pins["lean_toolchain"],
        f"Lean support toolchain differs from upstreams.json: {toolchain!r}",
    )
    versions = {"z3": z3, "lean_toolchain": toolchain, "lean": None}
    if lean:
        lean_version = command(
            ["elan", "run", toolchain, "lean", "--version"], env=env, capture=True
        ).stdout.strip()
        expected = toolchain.rsplit(":v", 1)[-1]
        require(
            lean_version.startswith(f"Lean (version {expected},"),
            f"Lean executable differs from upstreams.json: {lean_version!r}",
        )
        versions["lean"] = lean_version
    return versions


def axiom_audit_source(modules):
    """Generate an audit over module ownership, independent of author namespaces."""
    require(
        modules
        and len(set(modules)) == len(modules)
        and all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", m)
                for m in modules),
        "invalid or duplicate Lean proof module names",
    )
    # Deliberately use Lean's legacy import mode (no `module` header). In the
    # pinned Lean this imports private module data as well, including declarations
    # from files that use the new `module` system. Ownership comes from the checked
    # environment's module map, never from a declaration's namespace or visibility.
    imports = "\n".join(f"import {module}" for module in modules)
    names = ", ".join(f"`{module}" for module in modules)
    return "import Lean\n" + imports + "\n\n" + r'''open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[MODULE_NAMES]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut reports : Array Json := #[]
  let mut total : Nat := 0
  let mut rejected := false
  for moduleName in modules do
    let some moduleIdx := env.getModuleIdx? moduleName
      | throwError "axiom audit: requested module {moduleName} is absent"
    let mut count := 0
    let mut used : Array String := #[]
    let mut violations : Array Json := #[]
    for (declName, _) in env.checked.get.constants.toList do
      if env.getModuleIdxFor? declName == some moduleIdx then
        count := count + 1
        let axioms ← Lean.collectAxioms declName
        for axiomName in axioms do
          unless used.contains axiomName.toString do
            used := used.push axiomName.toString
        let forbidden := axioms.filter fun axiomName => !allowed.contains axiomName
        unless forbidden.isEmpty do
          rejected := true
          violations := violations.push <| Json.mkObj [
            ("declaration", toJson declName.toString),
            ("axioms", toJson ((forbidden.map Name.toString).qsort (· < ·)))]
    total := total + count
    reports := reports.push <| Json.mkObj [
      ("module", toJson moduleName.toString),
      ("declarations", toJson count),
      ("axioms", toJson (used.qsort (· < ·))),
      ("violations", Json.arr violations)]
  let report := Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("status", toJson (if rejected then "fail" else "pass")),
    ("allowed_axioms", toJson ((allowed.map Name.toString).qsort (· < ·))),
    ("checked_declarations", toJson total),
    ("modules", Json.arr reports)]
  liftIO <| IO.FS.writeFile "axiom-audit.json" (report.pretty ++ "\n")
  if rejected then
    throwError "axiom audit: disallowed dependencies; see axiom-audit.json"
'''.replace("MODULE_NAMES", names)


def validate_axiom_audit(report, modules):
    """Fail closed if the audit is missing coverage, malformed, or rejected."""
    require(isinstance(report, dict), "axiom audit must be an object")
    require(type(report.get("schema_version")) is int
            and report["schema_version"] == 1, "invalid axiom audit schema")
    require(report.get("status") == "pass", "axiom audit did not pass")
    require(report.get("allowed_axioms") == ALLOWED_LEAN_AXIOMS,
            "axiom audit allowlist differs from policy")
    entries = report.get("modules")
    require(isinstance(entries, list) and all(isinstance(e, dict) for e in entries),
            "invalid axiom audit module entries")
    require([entry.get("module") for entry in entries] == modules,
            "axiom audit module coverage is incomplete or duplicated")
    total = 0
    for entry in entries:
        count = entry.get("declarations")
        require(type(count) is int and count >= 0, "invalid axiom audit declaration count")
        axioms = entry.get("axioms")
        require(isinstance(axioms, list)
                and all(isinstance(a, str) and a in ALLOWED_LEAN_AXIOMS for a in axioms)
                and len(set(axioms)) == len(axioms),
                f"axiom audit: disallowed or malformed dependencies in {entry['module']}")
        require(count > 0 or axioms == [],
                f"axiom audit: empty module {entry['module']} reports dependencies")
        require(entry.get("violations") == [],
                f"axiom audit: violations in {entry['module']}")
        total += count
    require(type(report.get("checked_declarations")) is int
            and report["checked_declarations"] == total,
            "axiom audit total declaration count is incomplete")


def audit_lean_proofs(destination, modules, env):
    source = destination / "LeanisaAxiomAudit.lean"
    artifact = destination / "axiom-audit.json"
    require(not source.exists(), "proof module collides with generated axiom audit")
    artifact.unlink(missing_ok=True)
    source.write_text(axiom_audit_source(modules))
    try:
        command(["lake", "env", "lean", "-DwarningAsError=true", source.name],
                cwd=destination, env=env, capture=True)
    except subprocess.CalledProcessError as error:
        raise RuntimeError(
            f"Lean axiom audit failed; see {artifact}; {error.stdout}\n{error.stderr}"
        ) from error
    require(artifact.is_file(), "Lean axiom audit did not produce a report")

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "axiom audit report has duplicate JSON keys")
            result[key] = value
        return result

    try:
        report = json.loads(artifact.read_text(), object_pairs_hook=unique_object)
    except (OSError, ValueError) as error:
        raise RuntimeError("Lean axiom audit report is unreadable or malformed") from error
    validate_axiom_audit(report, modules)
    return dict(report,
                audit_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                report_sha256=hashlib.sha256(artifact.read_bytes()).hexdigest())


def check_lean_proofs(project, build, env, toolchain, *, algebra_store=None):
    """Build every handwritten module, then enforce the transitive axiom policy."""
    build.joinpath("validation.json").unlink(missing_ok=True)
    store = algebra_store or algebra_dependencies.DEFAULT_STORE
    with algebra_dependencies.store_lease(store):
        with algebra_dependencies.offline_environment(env, build) as guarded:
            dependencies = algebra_dependencies.verify_store(store, env=guarded)
            result = build_lean_proofs(project, build, guarded, toolchain, store)
            algebra_dependencies.verify_store(store, env=guarded, replay=False)
    return dict(result, dependencies=dependencies)


def build_lean_proofs(project, build, env, toolchain, store):
    """Stage the disposable proof library against already verified dependencies."""
    proofs = sorted((ROOT / "proofs").rglob("*.lean"))
    require(proofs, "no Lean proof modules found")
    destination = build / "lean-proofs"
    if destination.exists():
        shutil.rmtree(destination)
    destination.mkdir()
    modules = []
    for proof in proofs:
        relative = proof.relative_to(ROOT / "proofs")
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(proof, target)
        modules.append(".".join(relative.with_suffix("").parts))
    destination.joinpath("lean-toolchain").write_text(toolchain + "\n")
    destination.joinpath("lakefile.toml").write_text(f"""name = "leanisa-proofs"
defaultTargets = ["LeanisaProofs"]
packagesDir = {json.dumps(str(store / 'mathlib/.lake/packages'))}
[leanOptions]
warningAsError = true
[[lean_lib]]
name = "LeanisaProofs"
roots = {json.dumps(modules)}
[[require]]
name = "leanisa"
path = {json.dumps(str(project))}
[[require]]
name = "mathlib"
path = {json.dumps(str(store / 'mathlib'))}
""")
    command(["lake", "update"], cwd=destination, env=env)
    command(["lake", "--no-cache", "build"], cwd=destination, env=env)
    audit = audit_lean_proofs(destination, modules, env)
    return {"sources": [str(proof.relative_to(ROOT)) for proof in proofs],
            "axiom_audit": audit}


def command(args, *, cwd=ROOT, env=None, capture=False, data=None, timeout=None):
    return subprocess.run(
        [str(a) for a in args],
        cwd=cwd,
        env=env,
        check=True,
        text=True,
        input=data,
        capture_output=capture,
        timeout=timeout,
    )


def revision(path):
    return command(["git", "rev-parse", "HEAD"], cwd=path, capture=True).stdout.strip()


def hx(n, width=64):
    return f"0x{n:0{width // 4}x}"


def limbs(n):
    return [f"{(n >> (64 * i)) & MASK:016x}" for i in range(3)]


def integer(words):
    return sum(int(w, 16) << (64 * i) for i, w in enumerate(words))


def polynomial_mul(a, b):
    product = 0
    for i in range(64):
        if b & (1 << i):
            product ^= a << i
    for i in range(126, 63, -1):
        if product & (1 << i):
            product ^= ((1 << 64) | 0x1B) << (i - 64)
    return product


def extension_mul(a, b):
    aa = [(a >> (64 * i)) & MASK for i in range(3)]
    bb = [(b >> (64 * i)) & MASK for i in range(3)]
    product = [0] * 5
    for i in range(3):
        for j in range(3):
            product[i + j] ^= polynomial_mul(aa[i], bb[j])
    for i in (4, 3):
        product[i - 2] ^= product[i]
        product[i - 3] ^= product[i]
    return sum(product[i] << (64 * i) for i in range(3))


def address(n):
    require(type(n) is int and 0 <= n <= U32_MAX, "offset must fit in u32")
    result, base = 1, 2
    while n:
        if n & 1:
            result = polynomial_mul(result, base)
        base = polynomial_mul(base, base)
        n >>= 1
    return hx(result)


def sail_instruction(op):
    name, *args = op
    if name == "set":
        return f"Set({address(args[0])}, {hx(integer(args[1]), 192)})"
    if name == "deref":
        return f"Deref({', '.join(address(n) for n in args[:3])}, {args[3]})"
    constructor = {"xor": "Xor", "mul": "Mul", "jump": "Jump", "blake": "Blake2s"}[name]
    return f"{constructor}({', '.join(address(n) for n in args)})"


def generate(seed, count):
    rng = random.Random(seed)
    requests = []
    boundary = [0, 1, 2, 1 << 63, MASK, 1 << 64, 1 << 128, (1 << 192) - 1]
    pairs = [(a, b) for a in boundary for b in boundary]
    pairs += [(rng.getrandbits(192), rng.getrandbits(192)) for _ in range(count)]
    requests += [{"kind": "field", "a": limbs(a), "b": limbs(b)} for a, b in pairs]
    cv_words = [
        0x6A09E667 ^ 0x01010020,
        0xBB67AE85,
        0x3C6EF372,
        0xA54FF53A,
        0x510E527F,
        0x9B05688C,
        0x1F83D9AB,
        0x5BE0CD19,
    ]
    cv = sum(n << (32 * i) for i, n in enumerate(cv_words))
    for size in (0, 1, 3, 31, 32, 63, 64):
        msg = rng.randbytes(size)
        requests.append(
            {
                "kind": "blake",
                "message": [
                    f"{n:016x}"
                    for n in [
                        int.from_bytes(msg.ljust(64, b"\0")[i : i + 8], "little")
                        for i in range(0, 64, 8)
                    ]
                ],
                "cv": [f"{(cv >> (64 * i)) & MASK:016x}" for i in range(4)],
                "md": limbs(size | (0xFFFFFFFF << 64)),
                "hashlib": hashlib.blake2s(msg).hexdigest(),
            }
        )
    for _ in range(max(8, count // 4)):
        requests.append(
            {
                "kind": "blake",
                "message": [f"{rng.getrandbits(64):016x}" for _ in range(8)],
                "cv": [f"{rng.getrandbits(64):016x}" for _ in range(4)],
                "md": limbs(rng.getrandbits(128)),
            }
        )
    for index in range(max(8, count // 8)):
        a, b = rng.getrandbits(192), rng.getrandbits(192)
        ops = [
            ["set", 2, limbs(a)],
            ["set", 3, limbs(b)],
            ["mul", 2, 3, 4],
            ["xor", 2, 3, 5],
            ["set", 6, limbs(1 << 7)],
            ["deref", 6, 0, 4, "Cell"],
            ["deref", 6, 1, 4, "Pc"],
            ["deref", 6, 2, 4, "Fp"],
        ]
        chunks = [rng.getrandbits(128) for _ in range(7)]
        for offset, value in zip((10, 12, 11, 13, 14, 15, 16), chunks):
            ops.append(["set", offset, limbs(value)])
        ops.append(["blake", 10, 12, 11, 13, 14, 17, 16])
        # A taken jump skips a deliberately contradictory SET.
        ops += [
            ["set", 19, limbs(index + 1)],
            ["set", 20, limbs(1 << 22)],
            ["set", 21, limbs(1)],
            ["jump", 19, 20, 21],
            ["set", 2, limbs(a ^ 1)],
            ["set", 2, limbs(a ^ 2)],
        ]
        ops += [["set", 22, limbs(0)], ["jump", 22, 20, 21]]
        while len(ops) < 32:
            ops.append(["xor", 0, 0, 23])
        requests.append(
            {
                "kind": "execute",
                "program": ops,
                "input": [limbs(rng.getrandbits(128)), limbs(rng.getrandbits(128))],
                # Cell 4 is the result of the executed MUL in this template.
                "mutations": [{"cell": 4, "xor": limbs(1), "verdict": "BadValue"}],
            }
        )
    return requests + json.loads((ROOT / "tests/replay.json").read_text())


def source(requests, answers):
    functions, calls = [], []
    for index, (req, ans) in enumerate(zip(requests, answers, strict=True)):
        validate_request(req)
        name = f"case_{index}"
        calls.append(f"  {name}();")
        lines = [f"function {name}() -> unit = {{"]
        if req["kind"] == "field":
            a, b = integer(req["a"]), integer(req["b"])
            base, extension = polynomial_mul(a & MASK, b & MASK), extension_mul(a, b)
            require(
                base == int(ans["base"], 16),
                f"case {index}: Rust/Python base multiplication",
            )
            require(
                extension == integer(ans["extension"]),
                f"case {index}: Rust/Python extension multiplication",
            )
            lines += [
                f'  assert(kmul({hx(a & MASK)}, {hx(b & MASK)}) == {hx(base)}, "base {index}");',
                f'  assert(emul({hx(a, 192)}, {hx(b, 192)}) == {hx(extension, 192)}, "extension {index}");',
            ]
        elif req["kind"] == "blake":
            expected = integer(ans)
            if "hashlib" in req:
                require(
                    expected.to_bytes(32, "little").hex() == req["hashlib"],
                    f"case {index}: Rust/hashlib",
                )
            lines.append(
                f"  assert(blake_compress({hx(integer(req['message']), 512)}, "
                f"{hx(integer(req['cv']), 256)}, {hx(integer(req['md']), 128)}) "
                f'== {hx(expected, 256)}, "compression {index}");'
            )
            cells = [
                integer(req["message"]) >> (128 * i) & ((1 << 128) - 1)
                for i in range(4)
            ]
            cells += [
                integer(req["cv"]) & ((1 << 128) - 1),
                integer(req["cv"]) >> 128,
                integer(req["md"]),
                expected & ((1 << 128) - 1),
                expected >> 128,
            ]
            lines.append(
                "  var mem : vector(16, eword) = vector_init(16, sail_zeros(192));"
            )
            # The message references deliberately do not form a consecutive sequence.
            offsets = (0, 2, 1, 3, 4, 5, 6, 7, 8)
            lines += [
                f"  mem[{offset}] = {hx(value, 192)};"
                for offset, value in zip(offsets, cells, strict=True)
            ]
            ins = sail_instruction(["blake", 0, 2, 1, 3, 4, 7, 6])
            lines.append(f"  expect_step({ins}, mem, Running);")
            for offset in offsets:
                lines += [
                    f"  mem[{offset}] = mem[{offset}] ^^ {hx(1 << 128, 192)};",
                    f"  expect_step({ins}, mem, BadValue);",
                    f"  mem[{offset}] = mem[{offset}] ^^ {hx(1 << 128, 192)};",
                ]
            lines += [
                f"  mem[7] = mem[7] ^^ {hx(1, 192)};",
                f"  expect_step({ins}, mem, BadValue);",
            ]
        else:
            ops = req["program"]
            if "expected_unconstrained_reads" in req:
                require(
                    ans["unconstrained_reads"] == req["expected_unconstrained_reads"],
                    f"case {index}: unexpected Rust unconstrained_reads diagnostic",
                )
            require(
                type(ans["cycles"]) is int and ans["cycles"] >= 0,
                f"case {index}: invalid oracle cycle count",
            )
            lines += [
                f"  var program : vector({len(ops)}, instruction) = vector_init({len(ops)}, Xor({address(0)}, {address(0)}, {address(0)}));",
                f"  var mem : vector({ans['memory_size']}, eword) = vector_init({ans['memory_size']}, sail_zeros(192));",
            ]
            for i, op in enumerate(ops):
                lines.append(f"  program[{i}] = {sail_instruction(op)};")
                expected = ", ".join(
                    "0x" + word for word in reversed(ans["encoding"][i])
                )
                lines.append(f"  expect_encoding(program[{i}], [{expected}]);")
            lines += [f"  mem[{i}] = {hx(integer(w), 192)};" for i, w in ans["cells"]]
            pi = integer(req["input"][0]) | integer(req["input"][1]) << 128
            verdict = req.get("sail_verdict", "Halted")
            lines.append(
                f'  assert(checked_run(program, mem, {hx(pi, 256)}, {ans["cycles"]}).verdict == {verdict}, "execution {index}");'
            )
            if verdict == "Halted" and ans["cycles"] > 0:
                lines.append(
                    f'  assert(checked_run(program, mem, {hx(pi, 256)}, {ans["cycles"] - 1}).verdict == OutOfFuel, "cycles {index}");'
                )
            for mutation in req.get("mutations", []):
                cell, mask = mutation["cell"], hx(integer(mutation["xor"]), 192)
                require(
                    cell < ans["memory_size"],
                    f"case {index}: mutation cell outside image",
                )
                lines += [
                    f"  mem[{cell}] = mem[{cell}] ^^ {mask};",
                    f'  assert(checked_run(program, mem, {hx(pi, 256)}, {ans["cycles"]}).verdict == {mutation["verdict"]}, "mutation {index} cell {cell}");',
                    f"  mem[{cell}] = mem[{cell}] ^^ {mask};",
                ]
        lines += ["  ()", "}"]
        functions.append("\n".join(lines))
    groups = []
    for offset in range(0, len(calls), 32):
        name = f"group_{offset // 32}"
        functions.append(
            f"function {name}() -> unit = {{\n"
            + "\n".join(calls[offset : offset + 32])
            + "\n  ()\n}"
        )
        groups.append(f"  {name}();")
    functions.append(
        "function main() -> unit = {\n  boundaries();\n  address_tests();\n"
        + "\n".join(groups)
        + '\n  print_endline("leanISA validation: PASS")\n}\n'
    )
    return "\n\n".join(functions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260922)
    parser.add_argument("--cases", type=int, default=64)
    parser.add_argument("--sail-root", type=Path, default=ROOT.parent / "sail")
    parser.add_argument("--leanvm", type=Path, default=ROOT.parent / "leanVM")
    parser.add_argument("--lean-support", type=Path)
    parser.add_argument("--algebra-store", type=Path, default=algebra_dependencies.DEFAULT_STORE,
                        help="prepared offline algebra dependency store")
    parser.add_argument("--backend", choices=("both", "c", "lean"), default="both")
    parser.add_argument(
        "--coverage",
        action="store_true",
        help="Collect Sail source branch coverage from the C model",
    )
    parser.add_argument(
        "--replay", type=Path, help="Replay a saved corpus instead of generating cases"
    )
    parser.add_argument(
        "--oracle-timeout",
        type=float,
        default=10.0,
        help="Wall-clock seconds allowed per Rust case (default: 10)",
    )
    args = parser.parse_args()
    if args.cases < 0:
        parser.error("--cases must be nonnegative")
    if not math.isfinite(args.oracle_timeout) or args.oracle_timeout <= 0:
        parser.error("--oracle-timeout must be positive and finite")
    sail_root, leanvm = args.sail_root.resolve(), args.leanvm.resolve()
    support = (args.lean_support or sail_root / "_deps/lean-sail").resolve()
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    build.joinpath("validation.json").unlink(missing_ok=True)
    for name in ("oracle.json", "oracle-cases.jsonl", "oracle-failure.json"):
        build.joinpath(name).unlink(missing_ok=True)
    env = dict(os.environ)
    env["PATH"] = str(sail_root / "_deps/z3/bin") + os.pathsep + env["PATH"]
    env["CARGO_TARGET_DIR"] = str(build / "cargo")
    env["LEANVM_NUM_THREADS"] = "1"
    pins = json.loads(ROOT.joinpath("upstreams.json").read_text())
    revisions = {
        "sail": revision(sail_root),
        "lean_sail": revision(support),
        "leanvm": revision(leanvm),
    }
    for name, path in (("sail", sail_root), ("lean_sail", support), ("leanvm", leanvm)):
        if revisions[name] != pins[name]["revision"]:
            raise RuntimeError(
                f"{name} revision differs from upstreams.json; review the drift and update the pin"
            )
        command(["git", "diff", "--quiet", "HEAD"], cwd=path)
    compiler_version = command(
        [sail_root / "sail", "--version"], env=env, capture=True
    ).stdout.strip()
    if revisions["sail"] not in compiler_version:
        raise RuntimeError(
            "Sail executable does not match its source revision; rebuild Sail"
        )
    versions = check_tool_versions(
        pins, support, env, lean=args.backend in ("both", "lean")
    )
    # Explicit selection prevents ELAN_TOOLCHAIN or a directory override from
    # silently changing the compiler used by Lake.
    env["ELAN_TOOLCHAIN"] = pins["lean_toolchain"]
    tracked = [
        p
        for directory in ("spec", "tests", "scripts", "proofs", "dependencies")
        for p in (ROOT / directory).rglob("*")
        if p.is_file() and "__pycache__" not in p.parts
    ]
    tracked.append(ROOT / "upstreams.json")
    snapshots = {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in tracked
    }
    oracle = build / "oracle"
    oracle.mkdir(exist_ok=True)
    oracle.joinpath("Cargo.toml").write_text(f"""[package]
name = "leanisa-oracle"
version = "0.1.0"
edition = "2024"
[workspace]
[[bin]]
name = "leanisa-oracle"
path = "../../tests/oracle.rs"
[dependencies]
lean_vm = {{ path = {json.dumps(str(leanvm / "crates/lean_vm"))} }}
primitives = {{ path = {json.dumps(str(leanvm / "crates/primitives"))} }}
serde_json = "=1.0.149"
""")
    oracle_lock = ROOT / "tests/oracle.Cargo.lock"
    shutil.copyfile(oracle_lock, oracle / "Cargo.lock")
    command(
        [
            "cargo",
            "build",
            "--offline",
            "--locked",
            "--release",
            "--manifest-path",
            oracle / "Cargo.toml",
        ],
        env=env,
    )
    requests = (
        json.loads(args.replay.read_text())
        if args.replay
        else generate(args.seed, args.cases)
    )
    build.joinpath("corpus.json").write_text(json.dumps(requests, indent=2) + "\n")
    require(isinstance(requests, list), "corpus must be a JSON array")
    answers = run_oracle(
        requests,
        build / "cargo/release/leanisa-oracle",
        env=env,
        build=build,
        timeout=args.oracle_timeout,
    )
    build.joinpath("oracle.json").write_text(json.dumps(answers, indent=2) + "\n")
    generated = build / "vectors.sail"
    generated.write_text(source(requests, answers))
    sail = [
        sail_root / "sail",
        "--no-color",
        "--memo-z3-path",
        build / "sail_smt_cache",
    ]
    files = [
        ROOT / "spec" / f
        for f in ("field.sail", "blake2s.sail", "machine.sail", "encoding.sail")
    ]
    files += [ROOT / "tests/boundaries.sail", ROOT / "tests/addressing.sail", generated]
    command(sail + ["--just-check"] + files, env=env)
    properties = (
        "advance_is_field_multiplication",
        "base_multiply_one",
        "base_multiply_zero",
        "embedding_has_zero_extension_limbs",
    )
    command(
        sail
        + ["-smt"]
        + files[:3]
        + [ROOT / "tests/properties.sail", "-o", build / "properties"],
        env=env,
    )
    smt_unsat = []
    for prop in properties:
        result = command(
            ["z3", "-T:30", build / f"properties_{prop}.smt2"],
            env=env,
            capture=True,
            timeout=35,
        )
        require_unsat(prop, result)
        smt_unsat.append(prop)
    print(f"SMT: {len(smt_unsat)} properties have no counterexample", flush=True)
    if args.backend in ("both", "c"):
        coverage_args, coverage_link = [], []
        if args.coverage:
            coverage = build / "coverage-runtime"
            shutil.copytree(
                sail_root / "lib/coverage",
                coverage,
                dirs_exist_ok=True,
                ignore=shutil.ignore_patterns("target", "Cargo.lock"),
            )
            shutil.copyfile(ROOT / "tests/coverage.Cargo.lock", coverage / "Cargo.lock")
            command(
                [
                    "cargo",
                    "build",
                    "--offline",
                    "--locked",
                    "--release",
                    "--manifest-path",
                    coverage / "Cargo.toml",
                ],
                env=env,
            )
            coverage_args = ["--c-coverage", build / "coverage.all"]
            coverage_link = [
                build / "cargo/release/libsail_coverage.a",
                "-lpthread",
                "-ldl",
                "-lm",
            ]
            build.joinpath("coverage.taken").unlink(missing_ok=True)
        command(
            sail + ["-c", "-O"] + coverage_args + files + ["-o", build / "validation"],
            env=env,
        )
        runtime = sail_root / "lib"
        command(
            ["cc", "-O2", "-I", runtime, build / "validation.c"]
            + [runtime / f for f in ("sail.c", "rts.c", "elf.c", "sail_failure.c")]
            + coverage_link
            + ["-lgmp", "-o", build / "validation"],
            env=env,
        )
        run_args = [build / "validation"] + (
            ["--coverage", build / "coverage.taken"] if args.coverage else []
        )
        output = command(run_args, env=env, capture=True).stdout
        require_pass("C", output)
        print("C:", output.strip(), flush=True)
    lean_proofs = []
    lean_axiom_audit = None
    lean_algebra = None
    if args.backend in ("both", "lean"):
        destination = build / "generated-lean"
        destination.mkdir(exist_ok=True)
        project = destination / "leanisa"
        staging = build / "lean-staging"
        if staging.exists():
            shutil.rmtree(staging)
        staging.mkdir()
        command(
            sail
            + ["--splice", ROOT / "tests/print.splice"]
            + files
            + [
                "--lean",
                "--lean-single-file",
                "--lean-executable",
                "--lean-lib-path",
                support,
                "--lean-output-dir",
                staging,
                "-o",
                "leanisa",
            ],
            env=env,
        )
        generated_toolchain = (staging / "leanisa/lean-toolchain").read_text().strip()
        require(
            generated_toolchain == pins["lean_toolchain"],
            f"Generated Lean toolchain differs from upstreams.json: {generated_toolchain!r}",
        )
        shutil.copytree(staging / "leanisa", project, dirs_exist_ok=True)
        command(["lake", "update"], cwd=project, env=env)
        command(["lake", "build", "run"], cwd=project, env=env)
        proof_result = check_lean_proofs(project, build, env, pins["lean_toolchain"],
                                         algebra_store=args.algebra_store.resolve())
        lean_proofs = proof_result["sources"]
        lean_axiom_audit = proof_result["axiom_audit"]
        lean_algebra = proof_result["dependencies"]
        output = command(
            [project / ".lake/build/bin/run"], cwd=project, env=env, capture=True
        ).stdout
        require_pass("Lean", output)
        print("Lean:", output.strip(), flush=True)
    # The full production campaign includes a separate executable O1 gate.
    # Single-backend runs remain diagnostic and cannot claim O1 acceptance.
    o1_validation = (
        check_o1.validate(sail_root=sail_root, support=support,
                          build=build / "o1", env=env)
        if args.backend == "both" else None
    )
    o2a_validation = (
        check_o2a.validate(sail_root=sail_root, support=support,
                           build=build / "o2a", env=env)
        if args.backend == "both" else None
    )
    o2b_validation = (
        check_o2b.validate(sail_root=sail_root, support=support,
                           build=build / "o2b", env=env)
        if args.backend == "both" else None
    )
    for relative, digest in snapshots.items():
        if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != digest:
            raise RuntimeError(
                f"{relative} changed during validation; rerun against stable sources"
            )
    require(
        (oracle / "Cargo.lock").read_bytes() == oracle_lock.read_bytes(),
        "oracle dependency lock changed during validation",
    )
    report = {
        "seed": None if args.replay else args.seed,
        "cases": len(requests),
        "backend": args.backend,
        "c_sail_options": ["-O"] if args.backend in ("both", "c") else [],
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        **revisions,
        "compiler": compiler_version,
        "tool_versions": versions,
        "lean_proofs": lean_proofs,
        "lean_axiom_audit": lean_axiom_audit,
        "lean_algebra": lean_algebra,
        "o1": o1_validation,
        "o2a": o2a_validation,
        "o2b": o2b_validation,
        "oracle_timeout_seconds": args.oracle_timeout,
        "corpus_sha256": hashlib.sha256(
            build.joinpath("corpus.json").read_bytes()
        ).hexdigest(),
        "generated_tests_sha256": hashlib.sha256(generated.read_bytes()).hexdigest(),
        "oracle_output_sha256": hashlib.sha256(
            build.joinpath("oracle.json").read_bytes()
        ).hexdigest(),
        "oracle_cases_sha256": hashlib.sha256(
            build.joinpath("oracle-cases.jsonl").read_bytes()
        ).hexdigest(),
        "oracle_lock_sha256": hashlib.sha256(
            oracle.joinpath("Cargo.lock").read_bytes()
        ).hexdigest(),
        "source_sha256": snapshots,
        "counts": {
            kind: sum(r["kind"] == kind for r in requests)
            for kind in ("field", "blake", "execute")
        },
        "sail_expectations": {
            verdict: sum(
                r["kind"] == "execute" and r.get("sail_verdict", "Halted") == verdict
                for r in requests
            )
            for verdict in VERDICTS
        },
        "smt_unsat": smt_unsat,
        "coverage": args.coverage,
    }
    build.joinpath("validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
