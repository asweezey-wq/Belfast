import sys, os
import subprocess
from belfast_data import *
import belfast
import belfast_triples_opt
from belfast_triples_opt import OPTIMIZATION_FLAGS, OPTIMIZATION_FLAGS_DEFAULTS

def run_test(testfile):
    global COMPILER_SETTINGS, OPTIMIZATION_FLAGS
    output_filename = testfile + '.expected'
    expected_out = ''
    try:
        with open(output_filename, 'r') as f:
            expected_out = f.read()
    except FileNotFoundError:
        pass
    c = CompilerSettings(['.', 'std'])
    c.tripstr_filename = f'./tests/tripstr/{testfile.split("/")[-1][:-3]}.tripstr'
    c.output_filename = f'./tests/asm/{testfile.split("/")[-1][:-3]}.o'
    c.verbose = 0
    belfast.set_compiler_settings(c)
    belfast_triples_opt.set_opt_flags(OPTIMIZATION_FLAGS_DEFAULTS)
    print(f"[INFO] Compiling {testfile}")
    belfast.compile_bl(testfile)
    # print(f"[INFO] Building and linking asm")
    belfast.link_object(c.output_filename, 'a.out', ['std'], remove_obj=True)
    # print(f"[CMD] ./a.out")
    com = subprocess.run("./a.out", capture_output=True)
    actual_out = com.stdout.decode('utf-8')
    if actual_out != expected_out:
        print(f"[ERROR] Unexpected output")
        print(f"  Expected: \n{expected_out}")
        print(f"  Actual: \n{actual_out}")
        return False
    elif com.returncode != 0:
        print(f"[ERROR] Expected 0 return code, got {com.returncode}")
        return False
    else:
        print(f'[PASS] {testfile}')
        return True        


if __name__ == '__main__':
    failed = 0
    all_tests = []
    for entry in os.scandir('tests'):
        if entry.is_file() and entry.path.endswith('.bl'):
            all_tests.append(entry.path)
    for t in sorted(all_tests):
        if not run_test(t):
            failed += 1
    if failed > 0:
        print(f"\n[INFO] {failed} tests failed")
    else:
        print(f"\n[INFO] All tests passed")
