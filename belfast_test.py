from cgi import test
from cmath import exp
import sys, os
import subprocess

def run_test(testfile):
    cases = []
    bl_file = ''
    with open(testfile) as f:
        bl_file = f.readline().strip()
        bl_file = '/'.join(testfile.split('/')[:-1]) + '/' + bl_file
    
        rest = f.readlines()
        idx = 0
        while idx < len(rest):
            l = rest[idx].strip()
            idx += 1
            if len(l) == 0:
                continue
            if l != 'CASE':
                print(f"Invalid test file", file=sys.stderr)
                sys.exit(1)
            
            ins = []
            while idx < len(rest):
                in_l = rest[idx].strip()
                if in_l.startswith('IN '):
                    idx += 1
                    ins.append(int(in_l[3:]))
                else:
                    break
            
            outs = []
            while idx < len(rest):
                out_l = rest[idx].strip()
                if out_l.startswith('OUT '):
                    idx += 1
                    outs.append(out_l[4:])
                else:
                    break

            if len(ins) != 0 or len(outs) != 0:
                cases.append((ins, outs))
            else:
                print('Case with no ins or outs', file=sys.stderr)
                sys.exit(1)

    succeeded = True
    for i,o in cases:
        cmd = f"python3 belfast.py {bl_file} -r " + ' '.join(map(str, i))
        print(f"[CMD] {cmd}")
        com = subprocess.run(cmd.split(), capture_output=True)
        expected_out = ''
        for o_i in o:
            expected_out += str(o_i) + '\n'
        actual_out = com.stdout.decode('utf-8')
        if com.returncode != 0 or actual_out != expected_out:
            print(f"[ERROR] Unexpected output")
            print(f"  Expected: \n{expected_out}")
            print(f"  Actual: \n{actual_out}")
            succeeded = False
    
    if succeeded:
        print(f'[PASS] {testfile}')

    return succeeded
        


if __name__ == '__main__':
    for entry in os.scandir('tests'):
        if entry.is_file() and entry.path.endswith('.bltest'):
            run_test(entry.path)
