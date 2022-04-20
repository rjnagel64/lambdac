

import subprocess

# TODO: Move this to a subdirectory, and keep all executables/.out.c files there?

subprocess.run(["cabal", "build"])
exe_path = subprocess.run(["cabal", "exec", "which", "lambdac"], capture_output=True, encoding="utf8").stdout.strip()

# TODO: Begin building abstractions
# Collect multiple failures rather than crashing
# Report output from failed tests
# Helpers for standard test formats
def test_fibonacci():
    result = subprocess.run([exe_path, "examples/fibonacci.lamc"])
    assert result.returncode == 0

    result = subprocess.run(["./fibonacci"], capture_output=True, encoding="utf8")
    assert result.stdout == "result = 144\n"
    print("fibonacci OK")

def test_adder():
    result = subprocess.run([exe_path, "examples/adder.lamc"])
    assert result.returncode == 0

    result = subprocess.run(["./adder"], capture_output=True, encoding="utf8")
    assert result.stdout == "result = 8\n"
    print("adder OK")

def test_fact():
    result = subprocess.run([exe_path, "examples/fact.lamc"])
    assert result.returncode == 0
    result = subprocess.run(["./fact"], capture_output=True, encoding="utf8")
    assert result.stdout == "result = 3628800\n"
    print("fact OK")

def test_trisum():
    result = subprocess.run([exe_path, "examples/trisum.lamc"])
    assert result.returncode == 0
    result = subprocess.run(["./trisum"], capture_output=True, encoding="utf8")
    assert result.stdout == "result = 55\n"
    print("trisum OK")

def test_evenodd():
    result = subprocess.run([exe_path, "examples/evenodd.lamc"])
    assert result.returncode == 0
    result = subprocess.run(["./evenodd"], capture_output=True, encoding="utf8")
    assert result.stdout == "result = 1 :\n", result.stdout
    print("evenodd OK")


test_fibonacci()
test_adder()
test_fact()
test_trisum()
test_evenodd()
