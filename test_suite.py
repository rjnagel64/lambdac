

from collections import Counter
import subprocess
import sys
import time

# TODO: Move this script into tests/? Might need to adjust the CWD for cabal invocations

proc = subprocess.run(["cabal", "build"])
if proc.returncode != 0:
    print(f"{sys.argv[0]}: Compiler failed to build: not running tests")
    sys.exit(1)
compiler_path = subprocess.run(["cabal", "exec", "which", "lambdac"], capture_output=True, encoding="utf8").stdout.strip()

proc = subprocess.run(["make", "rts/librts.a"])
if proc.returncode != 0:
    print(f"{sys.argv[0]} RTS failed to build: not running tests")
    sys.exit(1)


all_tests = []
def standard_test(name, result):
    global all_tests
    all_tests.append(StandardTest(name, result))

class StandardTest:
    def __init__(self, name, result):
        self.name = name
        self.result = result

    def build(self, runner):
        runner.report_building(self.name)
        src_path = f"./tests/{self.name}.lamc"
        exe_path = f"./tests/bin/{self.name}"
        compile_command = [compiler_path, src_path, "-o", exe_path]
        compile_command.append("--check-cps")
        # compile_command.append("--check-cc")
        compile_command.append("--check-hoist")
        # compile_command.extend(["--opt-pass", "uncurry"])
        proc = subprocess.run(compile_command, capture_output=True, encoding="utf8")
        if proc.returncode != 0:
            runner.report_failure(self.name, proc.stdout, proc.stderr)
            return False
        else:
            return True

    def run(self, runner):
        exe_path = f"./tests/bin/{self.name}"

        proc = subprocess.run([exe_path], capture_output=True, encoding="utf8")
        if proc.stdout != f"result = {self.result}\n":
            runner.report_failure(self.name, proc.stdout, proc.stderr)
            return

        runner.report_success(self.name)

def io_test(name):
    global all_tests
    all_tests.append(IOTest(name))

class IOTest:
    def __init__(self, name):
        self.name = name

    def build(self, runner):
        runner.report_building(self.name)
        src_path = f"./tests/{self.name}.lamc"
        exe_path = f"./tests/bin/{self.name}"
        compile_command = [compiler_path, src_path, "-o", exe_path]
        compile_command.append("--check-cps")
        # compile_command.append("--check-cc")
        compile_command.append("--check-hoist")
        # compile_command.extend(["--opt-pass", "uncurry"])
        proc = subprocess.run(compile_command, capture_output=True, encoding="utf8")
        if proc.returncode != 0:
            runner.report_failure(self.name, proc.stdout, proc.stderr)
            return False
        else:
            return True

    def run(self, runner):
        exe_path = f"./tests/bin/{self.name}"
        stdin_path = f"./tests/{self.name}.stdin"
        stdout_path = f"./tests/{self.name}.stdout"

        def execute(stdin_obj):
            proc = subprocess.run([exe_path], stdin=stdin_obj, capture_output=True, encoding="utf8")
            with open(stdout_path, "r") as stdout_obj:
                expected_stdout = stdout_obj.read();
            if proc.stdout != expected_stdout:
                runner.report_failure(self.name, proc.stdout, proc.stderr)
                return
            runner.report_success(self.name)

        try:
            with open(stdin_path, "r") as stdin_obj:
                execute(stdin_obj)
        except FileNotFoundError:
            execute(None)

class CompileFail:
    def __init__(self, name):
        self.name = name

    def run(self, runner):
        runner.report_failure(name, "compile-fail tests not implemented", "")

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
standard_test("sums", "(inl(17), inr(true))")
standard_test("case", "17")
standard_test("slow_divmod", "((60, 3), (60, 3))")
standard_test("listctors", "(nil(), cons(true, nil()))")
standard_test("listcase", "34")
standard_test("listsum", "15")
standard_test("listmerge", "cons(1, cons(2, cons(3, cons(4, cons(5, cons(6, cons(7, nil())))))))")
standard_test("mergesort", "cons(1, cons(2, cons(3, cons(4, cons(5, cons(6, cons(7, nil())))))))")
standard_test("polyid", "<closure>")
standard_test("polyapp", "17")
standard_test("duparg", "true")
standard_test("polystate", "(55, 55)")
standard_test("rank2poly", "true")
standard_test("foldr", "7")
standard_test("polycase", "17")
standard_test("impred_inst", "<closure>")
standard_test("weird_id", "()")
standard_test("recpoly", "7")
standard_test("strings", "\"foobarfoobar\"")
standard_test("either", "true")
standard_test("rec", "17")
standard_test("datadecl", "()")
standard_test("datactor", "()")
standard_test("datacase", "true")
standard_test("monolist", "25")
standard_test("datapair", "true")
standard_test("polydata", "consF(17, true)")
io_test("hello")
io_test("echo")
io_test("bind_pure")
standard_test("hash", "(508950784, 508950784)")
standard_test("simple_proj", "true")
standard_test("record_val", "{ test = 17, it = false, works = \"yay!\" }")
standard_test("record_proj", "true")
standard_test("charliteral", "' '")
standard_test("escapechar", "(('\\n', '\\t'), ('\\\\', '\\''))")
standard_test("fieldprec", "94")
standard_test("typealias", "17")
standard_test("typealias2", "17")
standard_test("typealias3", "()")
standard_test("typealias4", "17")
standard_test("hkpoly", "single(17)")

def run_tests(test_whitelist):
    if test_whitelist is None:
        test_filter = lambda x: True
    else:
        test_filter = lambda x: x in test_whitelist
    runner = TestRunner()

    # beginning of build phase
    start = time.time()

    tests_to_run = []
    for test in all_tests:
        if not test_filter(test.name):
            runner.report_skipped(test.name)
        elif test.build(runner):
            tests_to_run.append(test)

    # end of build phase; start of execution phase
    built = time.time()

    for test in tests_to_run:
        test.run(runner)

    # end of execution phase
    ran = time.time()

    runner.print_summary()
    print(f"test build time: {built - start:.03f}s")
    print(f"test exec time: {ran - built:.03f}s")

class TestRunner:
    def __init__(self):
        self.stats = Counter()
        self.failed_tests = []

    def report_building(self, name):
        print(f"BUILD {name}")

    def report_skipped(self, name):
        self.stats["skipped"] += 1
        # print(f"{name} SKIP")

    def report_success(self, name):
        self.stats["ran"] += 1
        self.stats["passed"] += 1
        print(f"{name} OK")

    def report_failure(self, name, out, err):
        self.stats["ran"] += 1
        self.stats["failed"] += 1
        self.failed_tests.append((name, out, err))
        print(f"{name} FAIL")

    def print_summary(self):
        for (test, out, err) in self.failed_tests:
            print(f"--- FAILED: {test} ---")
            print(f"--- STDOUT: ---")
            print(out)
            print(f"--- STDERR: ---")
            print(err)

        ran = self.stats["ran"]
        skipped = self.stats["skipped"]
        passed = self.stats["passed"]
        failed = self.stats["failed"]
        print(f"{ran} tests ran; {skipped} tests skipped; {passed} tests passed; {failed} tests failed")


if len(sys.argv) > 1:
    whitelist = sys.argv[1:]
else:
    whitelist = None
run_tests(whitelist)
