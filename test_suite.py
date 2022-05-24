

import subprocess
import sys

# TODO: Move this script into tests/? Might need to adjust the CWD for cabal invocations
# TODO: Run only specific tests, when specified in argv?

proc = subprocess.run(["cabal", "build"])
if proc.returncode != 0:
    print(f"{sys.argv[0]}: Compiler failed to build: not running tests")
    sys.exit(1)
compiler_path = subprocess.run(["cabal", "exec", "which", "lambdac"], capture_output=True, encoding="utf8").stdout.strip()

failed_tests = []

def standard_test(name, result):
    path = f"./tests/{name}.lamc"
    exe_path = f"./tests/bin/{name}"
    proc = subprocess.run([compiler_path, path, "-o", exe_path], capture_output=True, encoding="utf8")
    if proc.returncode != 0:
        print(f"{name} FAIL")
        failed_tests.append((name, proc.stdout, proc.stderr))
        return

    proc = subprocess.run([exe_path], capture_output=True, encoding="utf8")
    if proc.stdout != f"result = {result}\n":
        print(f"{name} FAIL")
        failed_tests.append((name, proc.stdout, proc.stderr))
        return
    print(f"{name} OK")

def compile_fail(name, err):
    print(f"{name} FAIL")
    failed_tests.append((name, "compile-fail tests not implemented"))
    return

standard_test("fibonacci", "144")
standard_test("trisum", "55")
standard_test("tailfib", "144")
standard_test("fact", "3628800")
standard_test("evenodd", "true")
standard_test("adder", "8")
standard_test("bimap", "(34, 132)")
standard_test("state_sum", "(55, 55)")
standard_test("precedence", "-6")
standard_test("letrec", "true")
standard_test("sums", "(inl 17, inr true)")
standard_test("slow_divmod", "((60, 3), (60, 3))")
standard_test("listctors", "(nil, cons true nil)")
standard_test("listcase", "34")
standard_test("listsum", "15")


for (test, out, err) in failed_tests:
    print(f"--- FAILED: {test} ---")
    print(f"--- STDOUT: ---")
    print(out)
    print(f"--- STDERR: ---")
    print(err)
