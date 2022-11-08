

from collections import Counter
import subprocess
import sys

# TODO: Move this script into tests/? Might need to adjust the CWD for cabal invocations
# TODO: Run only specific tests, when specified in argv?

proc = subprocess.run(["cabal", "build"])
if proc.returncode != 0:
    print(f"{sys.argv[0]}: Compiler failed to build: not running tests")
    sys.exit(1)
compiler_path = subprocess.run(["cabal", "exec", "which", "lambdac"], capture_output=True, encoding="utf8").stdout.strip()

proc = subprocess.run(["make", "rts/librts.a"])
if proc.returncode != 0:
    print(f"{sys.argv[0]} RTS failed to build: not running tests")
    sys.exit(1)

stats = Counter()
failed_tests = []

def standard_test(name, result):
    global stats
    stats["ran"] += 1
    path = f"./tests/{name}.lamc"
    exe_path = f"./tests/bin/{name}"
    compile_command = [compiler_path, path, "-o", exe_path]
    # compile_command = [compiler_path, path, "-o", exe_path, "--check-cps"]
    proc = subprocess.run(compile_command, capture_output=True, encoding="utf8")
    if proc.returncode != 0:
        print(f"{name} FAIL")
        stats["failed"] += 1
        failed_tests.append((name, proc.stdout, proc.stderr))
        return

    proc = subprocess.run([exe_path], capture_output=True, encoding="utf8")
    if proc.stdout != f"result = {result}\n":
        print(f"{name} FAIL")
        stats["failed"] += 1
        failed_tests.append((name, proc.stdout, proc.stderr))
        return
    print(f"{name} OK")
    stats["passed"] += 1

def compile_fail(name, err):
    stats["ran"] += 1
    print(f"{name} FAIL")
    stats["failed"] += 1
    failed_tests.append((name, "compile-fail tests not implemented"))
    return

standard_test("fibonacci", "144")
standard_test("trisum", "55")
standard_test("tailfib", "144")
standard_test("fact", "3628800")
standard_test("evenodd", "true")
standard_test("adder", "8")
standard_test("bimap", "(34, 132)")
standard_test("product_arg", "<closure>")
standard_test("state_sum", "(55, 55)")
standard_test("precedence", "-6")
standard_test("letrec", "true")
standard_test("if", "true")
standard_test("sums", "(inl 17, inr true)")
standard_test("case", "17")
standard_test("slow_divmod", "((60, 3), (60, 3))")
standard_test("listctors", "(nil, cons true nil)")
standard_test("listcase", "34")
standard_test("listsum", "15")
standard_test("listmerge", "cons 1 cons 2 cons 3 cons 4 cons 5 cons 6 cons 7 nil")
standard_test("mergesort", "cons 1 cons 2 cons 3 cons 4 cons 5 cons 6 cons 7 nil")
standard_test("polyid", "<closure>")
standard_test("polyapp", "17")
standard_test("duparg", "true")
standard_test("polystate", "(55, 55)")
standard_test("rank2poly", "true")
standard_test("foldr", "7")
standard_test("polycase", "17")
standard_test("impred_inst", "<closure>")

for (test, out, err) in failed_tests:
    print(f"--- FAILED: {test} ---")
    print(f"--- STDOUT: ---")
    print(out)
    print(f"--- STDERR: ---")
    print(err)

print(f"{stats['ran']} tests ran; {stats['passed']} tests passed; {stats['failed']} tests failed")
