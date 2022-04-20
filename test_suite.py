

import subprocess

# TODO: Move this to a subdirectory, and keep all executables/.out.c files there?

subprocess.run(["cabal", "build"])
exe_path = subprocess.run(["cabal", "exec", "which", "lambdac"], capture_output=True, encoding="utf8").stdout.strip()

failed_tests = []

def standard_test(name, result):
    path = f"examples/{name}.lamc"
    proc = subprocess.run([exe_path, path], capture_output=True, encoding="utf8")
    if proc.returncode != 0:
        print(f"{name} FAIL")
        failed_tests.append((name, proc.stdout))
        return

    exe = f"./{name}"
    proc = subprocess.run([exe], capture_output=True, encoding="utf8")
    if proc.stdout != f"result = {result}\n":
        print(f"{name} FAIL")
        failed_tests.append((name, proc.stdout))
        return
    print(f"{name} OK")

# TODO: compile-fail tests that assert error and possibly message
def compile_fail(name, err):
    pass

standard_test("fibonacci", "144")
standard_test("trisum", "55")
standard_test("tailfib", "144")
standard_test("fact", "3628800")
standard_test("evenodd", "1 :")
standard_test("adder", "8")
standard_test("bimap", "(34, 132)")


for (test, out) in failed_tests:
    print(f"--- FAILED: {test} ---")
    print(out)
