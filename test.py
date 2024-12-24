from glob import glob
import subprocess
import time

def is_colorable(filename):
    with open(filename) as file:
        content = file.read().lower()
    if "positive" in content:
        return True
    elif "negative" in content:
        return False
    else:
        return None

total = 0
successful = 0

start = time.time()

for filename in glob("graphs/*.dimacs"):
    process = subprocess.run(["gforth", "program.fs", filename, "-e", "check bye"], stdout=subprocess.PIPE, text=True)
    output = process.stdout.strip()
    match is_colorable(filename):
        case True:
            expected = "yes"
        case False:
            expected = "no"
        case None:
            print(f"{filename} : Skipping, please specify whether the graph is 3-colorable.")
            continue
    total += 1
    if output != expected:
        print(f"{filename} : Expected '{expected}' but received '{output}.'")
    else:
        successful += 1

duration = round(time.time() - start, 2)

if total == successful:
    print(f"ok ... {duration} seconds")
else:
    print(f"{duration} seconds")
